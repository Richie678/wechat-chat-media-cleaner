import hashlib
import os
import shutil
import threading
import tkinter as tk
from datetime import datetime
from queue import Empty, Queue
from tkinter import filedialog, messagebox, scrolledtext, ttk


IMAGE_EXTENSIONS = {
    ".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp", ".tif", ".tiff", ".heic", ".heif"
}

VIDEO_EXTENSIONS = {
    ".mp4", ".mov", ".avi", ".mkv", ".wmv", ".flv", ".m4v", ".3gp", ".webm", ".mpeg", ".mpg"
}

THUMBNAIL_KEYWORDS = ("thumb", "thumbnail", "thumbs", "缩略图")
LOG_EVERY = 120

FILE_TYPE_MAP = {
    "ffd8ffe000104a464946": "jpg",
    "89504e470d0a1a0a0000": "png",
    "47494638396126026f01": "gif",
    "49492a00227105008037": "tif",
    "424d228c010000000000": "bmp",
    "424d8240090000000000": "bmp",
    "424d8e1b030000000000": "bmp",
    "2e524d46000000120001": "rmvb",
    "464c5601050000000900": "flv",
    "00000020667479706973": "mp4",
    "49443303000000000f76": "mp3",
    "000001ba210001000180": "mpg",
    "3026b2758e66cf11a6d9": "wmv",
    "524946464694c9015741": "wav",
    "52494646d07d60074156": "avi",
    "494d4b48010100000200": "264",
    "6D6F6F76": "mov",
}


def is_image(file_path):
    return os.path.splitext(file_path)[1].lower() in IMAGE_EXTENSIONS


def is_video(file_path):
    return os.path.splitext(file_path)[1].lower() in VIDEO_EXTENSIONS


def is_thumbnail(file_path):
    lower_path = file_path.lower()
    return any(keyword in lower_path for keyword in THUMBNAIL_KEYWORDS)


def file_hash(file_path, chunk_size=1024 * 1024):
    digest = hashlib.sha256()
    with open(file_path, "rb") as file_obj:
        while True:
            chunk = file_obj.read(chunk_size)
            if not chunk:
                break
            digest.update(chunk)
    return digest.hexdigest()


def bytes_hash(data):
    return hashlib.sha256(data).hexdigest()


def ensure_size_bucket_hash(bucket):
    if bucket["hashes"] is not None:
        return

    if bucket["first_kind"] == "file":
        first_digest = file_hash(bucket["first_path"])
    else:
        first_digest = bytes_hash(bucket["first_bytes"])

    bucket["hashes"] = {first_digest}
    bucket["first_bytes"] = None


def build_output_name(output_dir, file_name):
    base_name, ext = os.path.splitext(file_name)
    candidate = os.path.join(output_dir, file_name)
    index = 1
    while os.path.exists(candidate):
        candidate = os.path.join(output_dir, f"{base_name}_{index}{ext}")
        index += 1
    return candidate


def get_xor_from_header(header_bytes):
    byte_values = [b & 0xFF for b in header_bytes]
    result = [None, None]

    for signature_hex, extension in FILE_TYPE_MAP.items():
        if len(signature_hex) < 6:
            continue

        signature_bytes = []
        signature_len = min(len(signature_hex), 10)
        for index in range(0, signature_len, 2):
            if index + 1 < len(signature_hex):
                signature_bytes.append(int(signature_hex[index:index + 2], 16))

        compare_len = min(len(byte_values), len(signature_bytes))
        if compare_len < 3:
            continue

        xor_values = [byte_values[i] ^ signature_bytes[i] for i in range(compare_len)]
        if len(xor_values) >= 3 and xor_values[0] == xor_values[1] == xor_values[2]:
            result[0] = extension
            result[1] = xor_values[0]
            break

    return result


def decrypt_dat_to_bytes(file_path):
    with open(file_path, "rb") as file_obj:
        encrypted = file_obj.read()

    if len(encrypted) < 3:
        return None, None

    file_ext, xor_key = get_xor_from_header(encrypted[:10])
    if xor_key is None:
        return None, None

    decrypted = bytes(value ^ xor_key for value in encrypted)
    return file_ext, decrypted


class MediaStudioApp:
    def __init__(self, root):
        self.root = root
        self.root.title("微信聊天记录图片解密清理")
        self.root.geometry("1360x860")
        self.root.minsize(1280, 820)
        self.root.configure(bg="#0c1719")

        self.queue = Queue()
        self.running = False
        self.stop_requested = False
        self.last_output_dir = ""

        self.folder1_var = tk.StringVar()
        self.folder2_var = tk.StringVar()
        self.output_var = tk.StringVar()

        self.enable_dat_decrypt_var = tk.BooleanVar(value=True)
        self.keep_images_var = tk.BooleanVar(value=True)
        self.keep_videos_var = tk.BooleanVar(value=True)
        self.remove_thumbnails_var = tk.BooleanVar(value=True)
        self.remove_duplicate_images_var = tk.BooleanVar(value=True)
        self.remove_other_files_var = tk.BooleanVar(value=True)
        self.open_when_done_var = tk.BooleanVar(value=True)

        self.hero_note_var = tk.StringVar(value="准备就绪")
        self.progress_var = tk.StringVar(value="等待开始")
        self.stats_var = tk.StringVar(value="待处理 0 | 保留 0 | 重复图片 0 | 缩略图 0 | 其他文件 0 | 失败 0")

        self._setup_styles()
        self._build_ui()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.root.after(120, self._bring_to_front)

    def _setup_styles(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Shell.TFrame", background="#0c1719")
        style.configure("Hero.TFrame", background="#10292d")
        style.configure("Card.TFrame", background="#fffaf1")
        style.configure("Side.TFrame", background="#f2eadb")
        style.configure("Title.TLabel", background="#10292d", foreground="#fff7ea", font=("Microsoft YaHei UI", 22, "bold"))
        style.configure("HeroText.TLabel", background="#10292d", foreground="#d7e4df", font=("Microsoft YaHei UI", 10))
        style.configure("CardTitle.TLabel", background="#fffaf1", foreground="#1d3a3f", font=("Microsoft YaHei UI", 12, "bold"))
        style.configure("CardText.TLabel", background="#fffaf1", foreground="#476267", font=("Microsoft YaHei UI", 10))
        style.configure("SideTitle.TLabel", background="#f2eadb", foreground="#1d3a3f", font=("Microsoft YaHei UI", 12, "bold"))
        style.configure("SideText.TLabel", background="#f2eadb", foreground="#42585d", font=("Microsoft YaHei UI", 10))
        style.configure("Accent.TButton", background="#cb7b22", foreground="#ffffff", borderwidth=0, padding=(18, 10), font=("Microsoft YaHei UI", 10, "bold"))
        style.map("Accent.TButton", background=[("active", "#af6413"), ("disabled", "#9c8c73")])
        style.configure("Soft.TButton", background="#e4d4bc", foreground="#1d3a3f", borderwidth=0, padding=(12, 8), font=("Microsoft YaHei UI", 9, "bold"))
        style.map("Soft.TButton", background=[("active", "#d7c19f")])
        style.configure("Studio.TEntry", fieldbackground="#fffdfa", foreground="#173237", bordercolor="#d8c5ab", lightcolor="#d8c5ab", darkcolor="#d8c5ab", padding=8)
        style.configure("Studio.Horizontal.TProgressbar", background="#cb7b22", troughcolor="#eadfce", bordercolor="#eadfce", lightcolor="#cb7b22", darkcolor="#cb7b22")

    def _build_ui(self):
        outer = ttk.Frame(self.root, style="Shell.TFrame")
        outer.pack(fill=tk.BOTH, expand=True, padx=12, pady=12)

        hero = ttk.Frame(outer, style="Hero.TFrame")
        hero.pack(fill=tk.X)

        hero_left = tk.Frame(hero, bg="#10292d")
        hero_left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=20, pady=16)
        ttk.Label(hero_left, text="微信聊天记录图片解密清理", style="Title.TLabel").pack(anchor="w")
        ttk.Label(hero_left, text="支持 DAT 解密、缩略图清理、重复图片过滤和媒体汇总，原目录不改动。", style="HeroText.TLabel").pack(anchor="w", pady=(4, 2))
        ttk.Label(hero_left, textvariable=self.hero_note_var, style="HeroText.TLabel").pack(anchor="w")

        badge = tk.Frame(hero, bg="#cb7b22", width=260, height=110)
        badge.pack(side=tk.RIGHT, padx=16, pady=14)
        badge.pack_propagate(False)
        tk.Label(
            badge,
            text="BY LIP Gallagher",
            bg="#cb7b22",
            fg="#fff7ea",
            font=("Microsoft YaHei UI", 18, "bold"),
            justify="center"
        ).pack(expand=True, fill=tk.BOTH, padx=12, pady=12)

        body = ttk.Frame(outer, style="Shell.TFrame")
        body.pack(fill=tk.BOTH, expand=True, pady=(10, 0))

        left = ttk.Frame(body, style="Card.TFrame")
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        right = ttk.Frame(body, style="Side.TFrame", width=340)
        right.pack(side=tk.LEFT, fill=tk.Y, padx=(14, 0))
        right.pack_propagate(False)

        self._build_left_panel(left)
        self._build_right_panel(right)

    def _build_left_panel(self, parent):
        header = ttk.Frame(parent, style="Card.TFrame")
        header.pack(fill=tk.X, padx=18, pady=(16, 8))
        ttk.Label(header, text="目录设置", style="CardTitle.TLabel").pack(anchor="w")
        ttk.Label(
            header,
            text="支持两个来源目录，第二个目录可以留空。结果会输出到你指定位置下自动新建的文件夹。",
            style="CardText.TLabel",
            wraplength=860,
            justify="left",
        ).pack(anchor="w", pady=(4, 0))

        form = ttk.Frame(parent, style="Card.TFrame")
        form.pack(fill=tk.X, padx=18)
        self._path_row(form, "来源文件夹 A", self.folder1_var)
        self._path_row(form, "来源文件夹 B", self.folder2_var)
        self._path_row(form, "输出位置", self.output_var)

        buttons = ttk.Frame(parent, style="Card.TFrame")
        buttons.pack(fill=tk.X, padx=18, pady=(10, 8))
        ttk.Button(buttons, text="开始处理", style="Accent.TButton", command=self.start_processing).pack(side=tk.LEFT)
        self.stop_button = ttk.Button(buttons, text="停止处理", style="Soft.TButton", command=self.request_stop, state=tk.DISABLED)
        self.stop_button.pack(side=tk.LEFT, padx=10)
        ttk.Button(buttons, text="打开结果", style="Soft.TButton", command=self.open_output_folder).pack(side=tk.LEFT, padx=10)
        ttk.Button(buttons, text="清空路径", style="Soft.TButton", command=self.clear_paths).pack(side=tk.LEFT)

        progress_card = ttk.Frame(parent, style="Card.TFrame")
        progress_card.pack(fill=tk.X, padx=18, pady=(0, 8))
        ttk.Label(progress_card, text="处理进度", style="CardTitle.TLabel").pack(anchor="w", padx=14, pady=(12, 6))
        self.progress = ttk.Progressbar(progress_card, style="Studio.Horizontal.TProgressbar", orient=tk.HORIZONTAL, mode="determinate")
        self.progress.pack(fill=tk.X, padx=14)
        ttk.Label(progress_card, textvariable=self.progress_var, style="CardText.TLabel").pack(anchor="w", padx=14, pady=(6, 12))

        stats_card = ttk.Frame(parent, style="Card.TFrame")
        stats_card.pack(fill=tk.X, padx=18, pady=(0, 8))
        ttk.Label(stats_card, text="实时统计", style="CardTitle.TLabel").pack(anchor="w", padx=14, pady=(12, 6))
        ttk.Label(stats_card, textvariable=self.stats_var, style="CardText.TLabel", wraplength=860, justify="left").pack(anchor="w", padx=14, pady=(0, 12))

        log_card = ttk.Frame(parent, style="Card.TFrame")
        log_card.pack(fill=tk.BOTH, expand=True, padx=18, pady=(0, 16))
        ttk.Label(log_card, text="处理日志", style="CardTitle.TLabel").pack(anchor="w", padx=14, pady=(12, 6))
        self.log_text = scrolledtext.ScrolledText(log_card, wrap=tk.WORD, height=14, bg="#fffdfa", fg="#173237", insertbackground="#173237", relief=tk.FLAT, font=("Consolas", 10))
        self.log_text.pack(fill=tk.BOTH, expand=True, padx=14, pady=(0, 12))
        self.log_text.insert(tk.END, "这里会显示扫描、解密、过滤、去重和复制进度。\n如果只处理一个目录，把来源文件夹 B 留空即可。\n")
        self.log_text.configure(state=tk.DISABLED)

    def _build_right_panel(self, parent):
        options_card = ttk.Frame(parent, style="Side.TFrame")
        options_card.pack(fill=tk.X, padx=14, pady=(14, 0))
        ttk.Label(options_card, text="处理选项", style="SideTitle.TLabel").pack(anchor="w", pady=(0, 8))
        self._option_toggle(options_card, "启用 DAT 解密", self.enable_dat_decrypt_var)
        self._option_toggle(options_card, "保留图片", self.keep_images_var)
        self._option_toggle(options_card, "保留视频", self.keep_videos_var)
        self._option_toggle(options_card, "删除缩略图", self.remove_thumbnails_var)
        self._option_toggle(options_card, "删除重复图片", self.remove_duplicate_images_var)
        self._option_toggle(options_card, "删除除图片视频外的其他文件", self.remove_other_files_var)

        finish_card = ttk.Frame(parent, style="Side.TFrame")
        finish_card.pack(fill=tk.X, padx=14, pady=(10, 0))
        ttk.Label(finish_card, text="完成行为", style="SideTitle.TLabel").pack(anchor="w", pady=(0, 8))
        self._option_toggle(finish_card, "完成后自动打开结果目录", self.open_when_done_var)

        tips_card = ttk.Frame(parent, style="Side.TFrame")
        tips_card.pack(fill=tk.BOTH, expand=True, padx=14, pady=(10, 14))
        ttk.Label(tips_card, text="规则说明", style="SideTitle.TLabel").pack(anchor="w", pady=(0, 8))
        tips = [
            "启用 DAT 解密：识别微信缓存 DAT 文件头，并恢复原始图片或视频格式。",
            "删除缩略图：按路径或文件名中的 thumb、thumbnail、缩略图 等关键词判断。",
            "删除重复图片：只对图片按内容去重，完全相同才会视为重复。",
            "删除其他文件：勾选后，文档、压缩包、数据库等不会复制到结果目录。",
            "现在是边处理边写出，所以中途停止也会保留已经完成的文件。",
        ]
        for tip in tips:
            ttk.Label(tips_card, text=tip, style="SideText.TLabel", wraplength=290, justify="left").pack(anchor="w", pady=3)

    def _option_toggle(self, parent, text, variable):
        frame = tk.Frame(parent, bg="#f2eadb")
        frame.pack(fill=tk.X, pady=3)
        checkbox = tk.Checkbutton(
            frame,
            text=text,
            variable=variable,
            onvalue=True,
            offvalue=False,
            bg="#f2eadb",
            fg="#1d3a3f",
            activebackground="#f2eadb",
            activeforeground="#1d3a3f",
            selectcolor="#fff7ea",
            font=("Microsoft YaHei UI", 10),
            anchor="w",
            padx=2,
        )
        checkbox.pack(fill=tk.X, anchor="w")

    def _path_row(self, parent, label, variable):
        row_frame = ttk.Frame(parent, style="Card.TFrame")
        row_frame.pack(fill=tk.X, pady=6)
        ttk.Label(row_frame, text=label, style="CardText.TLabel").pack(anchor="w")
        entry_row = ttk.Frame(row_frame, style="Card.TFrame")
        entry_row.pack(fill=tk.X, pady=(4, 0))
        ttk.Entry(entry_row, textvariable=variable, style="Studio.TEntry").pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(entry_row, text="浏览", style="Soft.TButton", command=lambda current_var=variable: self.choose_directory(current_var)).pack(side=tk.LEFT, padx=(10, 0))

    def choose_directory(self, variable):
        directory = filedialog.askdirectory()
        if directory:
            variable.set(directory)

    def clear_paths(self):
        if self.running:
            return
        self.folder1_var.set("")
        self.folder2_var.set("")
        self.output_var.set("")
        self.hero_note_var.set("路径已清空")

    def start_processing(self):
        if self.running:
            return

        source_dirs = [self.folder1_var.get().strip()]
        second_dir = self.folder2_var.get().strip()
        if second_dir:
            source_dirs.append(second_dir)
        output_parent = self.output_var.get().strip()

        if not source_dirs[0] or not os.path.isdir(source_dirs[0]):
            messagebox.showerror("路径错误", "请先选择有效的来源文件夹 A。")
            return
        for directory in source_dirs[1:]:
            if not os.path.isdir(directory):
                messagebox.showerror("路径错误", f"来源文件夹不存在：{directory}")
                return
        if not output_parent or not os.path.isdir(output_parent):
            messagebox.showerror("路径错误", "请先选择有效的输出位置。")
            return
        if not self.keep_images_var.get() and not self.keep_videos_var.get() and self.remove_other_files_var.get():
            messagebox.showerror("选项冲突", "当前设置下不会保留任何文件，请至少保留图片或视频。")
            return

        output_dir = os.path.join(output_parent, f"微信聊天记录图片解密清理_{datetime.now().strftime('%Y%m%d_%H%M%S')}")
        os.makedirs(output_dir, exist_ok=True)

        self.running = True
        self.stop_requested = False
        self.last_output_dir = output_dir
        self.stop_button.config(state=tk.NORMAL)
        self.progress.configure(value=0, maximum=1)
        self.progress_var.set("开始准备")
        self.stats_var.set("待处理 0 | 保留 0 | 重复图片 0 | 缩略图 0 | 其他文件 0 | 失败 0")
        self.hero_note_var.set("正在扫描目录并应用筛选规则")
        self._append_log(f"输出目录：{output_dir}\n")

        worker = threading.Thread(target=self._process_files, args=(source_dirs, output_dir), daemon=True)
        worker.start()
        self.root.after(100, self._drain_queue)

    def _process_files(self, source_dirs, output_dir):
        try:
            options = {
                "enable_dat_decrypt": self.enable_dat_decrypt_var.get(),
                "keep_images": self.keep_images_var.get(),
                "keep_videos": self.keep_videos_var.get(),
                "remove_thumbnails": self.remove_thumbnails_var.get(),
                "remove_duplicate_images": self.remove_duplicate_images_var.get(),
                "remove_other_files": self.remove_other_files_var.get(),
            }

            all_files = []
            for directory in source_dirs:
                for current_root, _, files in os.walk(directory):
                    for file_name in files:
                        all_files.append(os.path.join(current_root, file_name))

            total_files = len(all_files)
            kept_count = 0
            duplicate_images = 0
            thumbnail_skipped = 0
            other_skipped = 0
            failed_count = 0
            image_buckets = {}

            self.queue.put(("progress_max", max(total_files, 1)))
            self.queue.put(("log", f"共发现 {total_files} 个文件，开始处理。\n"))

            for index, file_path in enumerate(all_files, start=1):
                if self.stop_requested:
                    self.queue.put(("stopped", kept_count, duplicate_images, thumbnail_skipped, other_skipped, failed_count, output_dir))
                    return

                self.queue.put(("progress_value", index, total_files, "处理中"))

                try:
                    lower_name = file_path.lower()

                    if options["enable_dat_decrypt"] and lower_name.endswith(".dat"):
                        file_ext, decrypted_bytes = decrypt_dat_to_bytes(file_path)
                        if not file_ext or decrypted_bytes is None:
                            if options["remove_other_files"]:
                                other_skipped += 1
                            else:
                                target_path = build_output_name(output_dir, os.path.basename(file_path))
                                shutil.copy2(file_path, target_path)
                                kept_count += 1
                        elif f".{file_ext.lower()}" in IMAGE_EXTENSIONS:
                            if not options["keep_images"]:
                                other_skipped += 1
                            elif options["remove_thumbnails"] and is_thumbnail(file_path):
                                thumbnail_skipped += 1
                            else:
                                if options["remove_duplicate_images"]:
                                    data_size = len(decrypted_bytes)
                                    digest = bytes_hash(decrypted_bytes)
                                    bucket = image_buckets.get(data_size)
                                    if bucket is None:
                                        image_buckets[data_size] = {
                                            "first_kind": "bytes",
                                            "first_path": None,
                                            "first_bytes": None,
                                            "hashes": {digest},
                                        }
                                    else:
                                        ensure_size_bucket_hash(bucket)
                                        if digest in bucket["hashes"]:
                                            duplicate_images += 1
                                            self.queue.put(("stats", total_files, kept_count, duplicate_images, thumbnail_skipped, other_skipped, failed_count))
                                            continue
                                        bucket["hashes"].add(digest)
                                output_name = f"{os.path.splitext(os.path.basename(file_path))[0]}.{file_ext}"
                                target_path = build_output_name(output_dir, output_name)
                                with open(target_path, "wb") as output_file:
                                    output_file.write(decrypted_bytes)
                                kept_count += 1
                        elif f".{file_ext.lower()}" in VIDEO_EXTENSIONS:
                            if options["keep_videos"]:
                                output_name = f"{os.path.splitext(os.path.basename(file_path))[0]}.{file_ext}"
                                target_path = build_output_name(output_dir, output_name)
                                with open(target_path, "wb") as output_file:
                                    output_file.write(decrypted_bytes)
                                kept_count += 1
                            else:
                                other_skipped += 1
                        else:
                            if options["remove_other_files"]:
                                other_skipped += 1
                            else:
                                output_name = f"{os.path.splitext(os.path.basename(file_path))[0]}.{file_ext}"
                                target_path = build_output_name(output_dir, output_name)
                                with open(target_path, "wb") as output_file:
                                    output_file.write(decrypted_bytes)
                                kept_count += 1
                    elif is_image(file_path):
                        if not options["keep_images"]:
                            other_skipped += 1
                        elif options["remove_thumbnails"] and is_thumbnail(file_path):
                            thumbnail_skipped += 1
                        else:
                            if options["remove_duplicate_images"]:
                                file_size = os.path.getsize(file_path)
                                bucket = image_buckets.get(file_size)
                                if bucket is None:
                                    image_buckets[file_size] = {
                                        "first_kind": "file",
                                        "first_path": file_path,
                                        "first_bytes": None,
                                        "hashes": None,
                                    }
                                else:
                                    ensure_size_bucket_hash(bucket)
                                    digest = file_hash(file_path)
                                    if digest in bucket["hashes"]:
                                        duplicate_images += 1
                                        self.queue.put(("stats", total_files, kept_count, duplicate_images, thumbnail_skipped, other_skipped, failed_count))
                                        continue
                                    bucket["hashes"].add(digest)
                            target_path = build_output_name(output_dir, os.path.basename(file_path))
                            shutil.copy2(file_path, target_path)
                            kept_count += 1
                    elif is_video(file_path):
                        if options["keep_videos"]:
                            target_path = build_output_name(output_dir, os.path.basename(file_path))
                            shutil.copy2(file_path, target_path)
                            kept_count += 1
                        else:
                            other_skipped += 1
                    else:
                        if options["remove_other_files"]:
                            other_skipped += 1
                        else:
                            target_path = build_output_name(output_dir, os.path.basename(file_path))
                            shutil.copy2(file_path, target_path)
                            kept_count += 1
                except Exception as exc:
                    failed_count += 1
                    self.queue.put(("log", f"处理失败: {os.path.basename(file_path)} | {exc}\n"))

                if index % LOG_EVERY == 0 or index == total_files:
                    self.queue.put(("log", f"处理进度: {index}/{total_files} | 已保留 {kept_count}\n"))
                self.queue.put(("stats", total_files, kept_count, duplicate_images, thumbnail_skipped, other_skipped, failed_count))

            summary = (
                f"\n处理完成。\n"
                f"保留文件: {kept_count}\n"
                f"删除重复图片: {duplicate_images}\n"
                f"删除缩略图: {thumbnail_skipped}\n"
                f"删除其他文件: {other_skipped}\n"
                f"失败: {failed_count}\n"
                f"输出目录: {output_dir}\n"
            )
            self.queue.put(("done", summary))
        except Exception as exc:
            self.queue.put(("error", str(exc)))

    def _drain_queue(self):
        try:
            while True:
                item = self.queue.get_nowait()
                event = item[0]

                if event == "log":
                    self._append_log(item[1])
                elif event == "progress_max":
                    self.progress.configure(maximum=max(item[1], 1))
                elif event == "progress_value":
                    current, total, stage = item[1], item[2], item[3]
                    self.progress.configure(value=current)
                    self.progress_var.set(f"{stage}: {current}/{total}")
                elif event == "stats":
                    _, total, kept, duplicate, thumbnail, other, failed = item
                    self.stats_var.set(f"待处理 {total} | 保留 {kept} | 重复图片 {duplicate} | 缩略图 {thumbnail} | 其他文件 {other} | 失败 {failed}")
                elif event == "done":
                    self._append_log(item[1])
                    self.progress_var.set("已完成")
                    self.hero_note_var.set("处理完成，结果目录已经生成")
                    self._finish(True)
                elif event == "stopped":
                    _, kept, duplicate, thumbnail, other, failed, output_dir = item
                    self._append_log(
                        f"\n已停止处理。\n保留文件: {kept}\n删除重复图片: {duplicate}\n删除缩略图: {thumbnail}\n删除其他文件: {other}\n失败: {failed}\n输出目录: {output_dir}\n"
                    )
                    self.progress_var.set("已停止")
                    self.hero_note_var.set("处理已停止，已保留完成部分")
                    self._finish(False)
                elif event == "error":
                    self._append_log(f"\n发生错误: {item[1]}\n")
                    self.progress_var.set("处理失败")
                    self.hero_note_var.set("处理中断，请查看日志")
                    self._finish(False)
        except Empty:
            pass

        if self.running:
            self.root.after(100, self._drain_queue)

    def _finish(self, success):
        self.running = False
        self.stop_requested = False
        self.stop_button.config(state=tk.DISABLED)
        if success and self.open_when_done_var.get():
            self.open_output_folder()

    def request_stop(self):
        if not self.running:
            return
        self.stop_requested = True
        self.stop_button.config(state=tk.DISABLED)
        self.hero_note_var.set("正在停止，请等待当前文件处理完成")
        self._append_log("\n收到停止请求，正在安全结束当前任务...\n")

    def _on_close(self):
        if self.running and not self.stop_requested:
            should_stop = messagebox.askyesno("确认退出", "当前正在处理。是否先停止任务？")
            if not should_stop:
                return
            self.request_stop()
            return
        self.root.destroy()

    def _bring_to_front(self):
        try:
            self.root.lift()
            self.root.attributes("-topmost", True)
            self.root.after(250, lambda: self.root.attributes("-topmost", False))
            self.root.focus_force()
        except Exception:
            pass

    def _append_log(self, message):
        self.log_text.configure(state=tk.NORMAL)
        self.log_text.insert(tk.END, message)
        self.log_text.see(tk.END)
        self.log_text.configure(state=tk.DISABLED)

    def open_output_folder(self):
        if not self.last_output_dir or not os.path.isdir(self.last_output_dir):
            messagebox.showinfo("提示", "结果文件夹还不存在，请先执行一次处理。")
            return
        try:
            os.startfile(self.last_output_dir)
        except Exception as exc:
            messagebox.showerror("打开失败", f"无法打开结果文件夹：{exc}")


def main():
    root = tk.Tk()
    app = MediaStudioApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
