#!/usr/bin/env python3
# -*- coding: utf-8 -*-
###################################################################
#
#         ____.       __    __           ________  .____________
#        |    |____  |  | _|  | _______  \_____  \ |   ____/_   |
#        |    \__  \ |  |/ /  |/ /\__  \   _(__  < |____  \ |   |
#    /\__|    |/ __ \|    <|    <  / __ \_/       \/       \|   |
#    \________(____  /__|_ \__|_ \(____  /______  /______  /|___|
#                  \/     \/    \/     \/       \/       \/
#
###################################################################
"""
VBF Unpacker + Packer GUI by Jakka351

Unpack:
  - Finds ASCII header via quote-aware brace matching.
  - Parses big-endian blocks: [u32 addr][u32 len][data...][u16 CRC16-CCITT].
  - Verifies per-block CRC16 (init=0xFFFF, poly=0x1021).
  - Optional header file_checksum (CRC32) verify.

Pack:
  - "Pack VBF" tab: load/edit header text, add MULTIPLE BINs with start addresses.
  - Emits valid VBF: header + blocks + CRC16 per block.
  - Optional file_checksum stamping with selectable scope:
      * whole_file_zeroed_field (default)
      * payload_only
      * header_only
    If the header lacks a `file_checksum = 0x????????;` line, nothing is stamped.

Notes:
  - CRC16 per block is computed over DATA BYTES ONLY, appended as u16 BE.
  - file_checksum uses zlib CRC32.
"""

from __future__ import annotations
import re
import zlib
import mmap
import json
import struct
from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple, Optional

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog

# ---------- CRCs ----------

CRC16_POLY = 0x1021
CRC16_INIT = 0xFFFF

def crc16_ccitt_ffff(data: memoryview | bytes) -> int:
    """CRC-16/CCITT-FALSE (poly 0x1021, init 0xFFFF) over data bytes."""
    crc = CRC16_INIT
    mv = memoryview(data) if not isinstance(data, memoryview) else data
    for b in mv:
        crc ^= (b << 8) & 0xFFFF
        for _ in range(8):
            if crc & 0x8000:
                crc = ((crc << 1) ^ CRC16_POLY) & 0xFFFF
            else:
                crc = (crc << 1) & 0xFFFF
    return crc & 0xFFFF

def crc32_bytes(buf: bytes) -> int:
    return zlib.crc32(buf) & 0xFFFFFFFF

def crc32_file(mm: mmap.mmap) -> int:
    """CRC32 over a memory-mapped file."""
    pos = 0
    crc = 0
    blksz = 1 << 20
    size = len(mm)
    while pos < size:
        end = min(size, pos + blksz)
        crc = zlib.crc32(mm[pos:end], crc)
        pos = end
    return crc & 0xFFFFFFFF

# ---------- Parsing (unpack) ----------

@dataclass
class VBFSection:
    index: int
    start_addr: int
    length: int
    data_off: int
    crc_stored: int
    crc_calc: int

@dataclass
class VBFFile:
    path: Path
    header_text: str
    header_end_off: int
    header_fields: dict
    file_crc_from_header: Optional[int]
    sections: List[VBFSection]

HEADER_PREFIX_RE = re.compile(r"\bvbf_version\s*=\s*([0-9.]+)\s*;", re.IGNORECASE)

def _find_header_bounds(mm: mmap.mmap) -> Tuple[int, int]:
    lower = mm.read().lower(); mm.seek(0)
    hidx = lower.find(b'header')
    if hidx < 0:
        head = lower[:min(2_000_000, len(mm))]
        if b'vbf_version' in head:
            vpos = head.find(b'vbf_version')
            obr = head.find(b'{', vpos)
            cpos = _match_brace(mm, obr)
            if obr < 0 or cpos < 0:
                raise ValueError("Could not locate 'header { ... }' block.")
            return (vpos, cpos + 1)
        raise ValueError("No 'header' keyword found; not a VBF or header corrupted.")
    obr = lower.find(b'{', hidx)
    if obr < 0:
        raise ValueError("Found 'header' but no opening '{'.")
    cpos = _match_brace(mm, obr)
    if cpos < 0:
        raise ValueError("Header brace matching failed (unbalanced braces or unterminated quotes).")
    return (hidx, cpos + 1)

def _match_brace(mm: mmap.mmap, obr: int) -> int:
    """Given offset of '{', find matching '}' respecting quotes. Return index of '}' or -1."""
    i = obr
    depth = 0
    size = len(mm)
    in_str = False
    esc = False
    while i < size:
        c = mm[i]; i += 1
        if in_str:
            if esc:
                esc = False; continue
            if c == 0x5C:  # '\'
                esc = True; continue
            if c == 0x22:  # '"'
                in_str = False
            continue
        if c == 0x22:
            in_str = True; continue
        if c == 0x7B:  # '{'
            depth += 1; continue
        if c == 0x7D:  # '}'
            depth -= 1
            if depth == 0:
                return i - 1
    return -1

def parse_header_fields(header_text: str) -> Tuple[dict, Optional[int]]:
    """Light parser to pull key fields; return (fields_dict, file_checksum if present)."""
    lines = []
    for line in header_text.splitlines():
        if '//' in line:
            line = line.split('//', 1)[0]
        lines.append(line)
    txt = '\n'.join(lines)

    kv_re = re.compile(r'([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*?);', re.DOTALL)
    fields = {}
    file_crc = None
    for m in kv_re.finditer(txt):
        k = m.group(1); v = m.group(2).strip()
        if v.startswith('{') and v.endswith('}'):
            fields[k] = v[1:-1].strip(); continue
        if v.startswith('"') and v.endswith('"'):
            fields[k] = v[1:-1]; continue
        vlow = v.lower()
        if vlow.startswith('0x'):
            try:
                num = int(vlow, 16)
                fields[k] = num
                if k.lower() == 'file_checksum':
                    file_crc = num & 0xFFFFFFFF
                continue
            except Exception:
                pass
        try:
            if '.' in v: fields[k] = float(v)
            else: fields[k] = int(v)
        except Exception:
            fields[k] = v
    return fields, file_crc

def parse_blocks(mm: mmap.mmap, start_off: int, on_progress=None) -> List[VBFSection]:
    total = len(mm); p = start_off; idx = 1
    sections: List[VBFSection] = []
    min_hdr = 4 + 4 + 2
    while p + min_hdr <= total:
        addr = struct.unpack_from('>I', mm, p)[0]; p += 4
        length = struct.unpack_from('>I', mm, p)[0]; p += 4
        if length < 0 or p + length + 2 > total:
            break
        data_off = p
        data_mv = memoryview(mm)[data_off:data_off+length]
        p += length
        crc_stored = struct.unpack_from('>H', mm, p)[0]; p += 2
        crc_calc = crc16_ccitt_ffff(data_mv)
        sections.append(VBFSection(idx, addr, length, data_off, crc_stored, crc_calc))
        idx += 1
        if on_progress and (idx % 64 == 0):
            on_progress(p / total)
    return sections

# ---------- GUI ----------

class VBFGui(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("VBF Unpacker/Pack­er — github.com/Jakka351")
        self.geometry("1280x800"); self.minsize(1100, 700)

        # Unpack state
        self.mm: Optional[mmap.mmap] = None
        self.path: Optional[Path] = None
        self.header_text: str = ""
        self.header_end: int = 0
        self.header_fields: dict = {}
        self.header_crc32: Optional[int] = None
        self.sections: List[VBFSection] = []
        self.outdir: Optional[Path] = None

        # Pack state
        self.pack_header_text = tk.StringVar(value="")
        self.pack_header_loaded_from: Optional[Path] = None
        self.pack_items: List[Tuple[Path,int,int]] = []  # (path, addr, length)

        # Checksum options
        self.pk_do_file_crc = tk.BooleanVar(value=True)
        self.pk_crc_scope = tk.StringVar(value="whole_file_zeroed_field")  # payload_only, header_only also

        self._build_menu()
        self._build_ui()

    # ----- Menus -----
    def _build_menu(self):
        m = tk.Menu(self)

        fm = tk.Menu(m, tearoff=0)
        fm.add_command(label="Open VBF…", command=self.cmd_open)
        fm.add_separator()
        fm.add_command(label="Exit", command=self.destroy)
        m.add_cascade(label="File", menu=fm)

        am = tk.Menu(m, tearoff=0)
        am.add_command(label="Choose Output Folder…", command=self.cmd_choose_out)
        am.add_command(label="Extract Selected Block", command=self.cmd_extract_selected)
        am.add_command(label="Extract All Blocks", command=self.cmd_extract_all)
        m.add_cascade(label="Actions", menu=am)

        hm = tk.Menu(m, tearoff=0)
        hm.add_command(label="About", command=self.cmd_about)
        m.add_cascade(label="Help", menu=hm)

        self.config(menu=m)

    # ----- Layout -----
    def _build_ui(self):
        # Top status row
        top = ttk.Frame(self, padding=8); top.pack(fill='x')
        self.lbl_file = ttk.Label(top, text="No file loaded"); self.lbl_file.pack(side='left')
        self.lbl_out = ttk.Label(top, text="Output: (not set)"); self.lbl_out.pack(side='right')

        paned = ttk.Panedwindow(self, orient='horizontal'); paned.pack(fill='both', expand=True, padx=8, pady=8)

        # Left: unpack sections list
        left = ttk.Frame(paned); paned.add(left, weight=1)
        cols = ("#", "start", "len", "crc", "ok")
        self.tree = ttk.Treeview(left, columns=cols, show='headings', selectmode='browse')
        self.tree.heading("#", text="#"); self.tree.column("#", width=60, anchor='e')
        self.tree.heading("start", text="Start Addr (hex)"); self.tree.column("start", width=160, anchor='w')
        self.tree.heading("len", text="Length"); self.tree.column("len", width=120, anchor='e')
        self.tree.heading("crc", text="CRC16 stored/calc"); self.tree.column("crc", width=220, anchor='w')
        self.tree.heading("ok", text="OK"); self.tree.column("ok", width=60, anchor='center')
        self.tree.pack(fill='both', expand=True)

        btns = ttk.Frame(left); btns.pack(fill='x', pady=(6,0))
        ttk.Button(btns, text="Extract Selected", command=self.cmd_extract_selected).pack(side='left', padx=4)
        ttk.Button(btns, text="Extract All", command=self.cmd_extract_all).pack(side='left', padx=4)

        # Right: tabs
        right = ttk.Notebook(paned); paned.add(right, weight=2)

        # --- Unpack: Header (raw) ---
        tab_hdr = ttk.Frame(right); right.add(tab_hdr, text="Header")
        self.txt_hdr = tk.Text(tab_hdr, wrap='none')
        y1 = ttk.Scrollbar(tab_hdr, orient='vertical', command=self.txt_hdr.yview)
        x1 = ttk.Scrollbar(tab_hdr, orient='horizontal', command=self.txt_hdr.xview)
        self.txt_hdr.configure(yscrollcommand=y1.set, xscrollcommand=x1.set)
        self.txt_hdr.pack(side='top', fill='both', expand=True); y1.pack(side='right', fill='y'); x1.pack(side='bottom', fill='x')

        # --- Unpack: Header (JSON) ---
        tab_json = ttk.Frame(right); right.add(tab_json, text="Header (JSON)")
        self.txt_json = tk.Text(tab_json, wrap='none')
        y2 = ttk.Scrollbar(tab_json, orient='vertical', command=self.txt_json.yview)
        x2 = ttk.Scrollbar(tab_json, orient='horizontal', command=self.txt_json.xview)
        self.txt_json.configure(yscrollcommand=y2.set, xscrollcommand=x2.set)
        self.txt_json.pack(side='top', fill='both', expand=True); y2.pack(side='right', fill='y'); x2.pack(side='bottom', fill='x')

        # --- Pack VBF tab ---
        tab_pack = ttk.Frame(right); right.add(tab_pack, text="Pack VBF")

        # Header load/edit controls
        header_frame = ttk.LabelFrame(tab_pack, text="Header")
        header_frame.pack(fill='both', expand=False, padx=6, pady=6)
        header_btns = ttk.Frame(header_frame); header_btns.pack(fill='x', padx=6, pady=4)
        ttk.Button(header_btns, text="Load Header…", command=self.pk_load_header).pack(side='left', padx=4)
        ttk.Button(header_btns, text="Save Header As…", command=self.pk_save_header_as).pack(side='left', padx=4)
        self.lbl_header_src = ttk.Label(header_btns, text="(no header loaded)")
        self.lbl_header_src.pack(side='left', padx=10)

        self.txt_pk_hdr = tk.Text(header_frame, height=12, wrap='none')
        yph = ttk.Scrollbar(header_frame, orient='vertical', command=self.txt_pk_hdr.yview)
        xph = ttk.Scrollbar(header_frame, orient='horizontal', command=self.txt_pk_hdr.xview)
        self.txt_pk_hdr.configure(yscrollcommand=yph.set, xscrollcommand=xph.set)
        self.txt_pk_hdr.pack(side='top', fill='both', expand=True, padx=6)
        yph.pack(side='right', fill='y'); xph.pack(side='bottom', fill='x')

        # BIN list + controls
        bins_frame = ttk.LabelFrame(tab_pack, text="Blocks (addr + file)")
        bins_frame.pack(fill='both', expand=True, padx=6, pady=6)

        cols_pk = ("#", "addr", "len", "path")
        self.tree_pk = ttk.Treeview(bins_frame, columns=cols_pk, show='headings', selectmode='browse')
        self.tree_pk.heading("#", text="#"); self.tree_pk.column("#", width=40, anchor='e')
        self.tree_pk.heading("addr", text="Start Addr (hex)"); self.tree_pk.column("addr", width=160, anchor='w')
        self.tree_pk.heading("len", text="Length"); self.tree_pk.column("len", width=120, anchor='e')
        self.tree_pk.heading("path", text="File"); self.tree_pk.column("path", width=500, anchor='w')
        self.tree_pk.pack(fill='both', expand=True, padx=6, pady=4)

        pk_btns = ttk.Frame(bins_frame); pk_btns.pack(fill='x', padx=6, pady=(0,6))
        ttk.Button(pk_btns, text="Add BIN(s)…", command=self.pk_add_bin).pack(side='left', padx=4)
        ttk.Button(pk_btns, text="Remove", command=self.pk_remove_selected).pack(side='left', padx=4)
        ttk.Button(pk_btns, text="Move Up", command=lambda: self.pk_move_sel(-1)).pack(side='left', padx=4)
        ttk.Button(pk_btns, text="Move Down", command=lambda: self.pk_move_sel(+1)).pack(side='left', padx=4)
        ttk.Button(pk_btns, text="Build VBF…", command=self.pk_build).pack(side='right', padx=4)

        # Checksum options
        opts = ttk.LabelFrame(tab_pack, text="Checksum options")
        opts.pack(fill='x', padx=6, pady=(0,6))
        ttk.Checkbutton(opts, text="Compute and stamp file_checksum", variable=self.pk_do_file_crc).pack(side='left', padx=6)
        ttk.Label(opts, text="Scope:").pack(side='left', padx=(12,4))
        scope = ttk.Combobox(opts, textvariable=self.pk_crc_scope, state="readonly",
                             values=("whole_file_zeroed_field", "payload_only", "header_only"))
        scope.pack(side='left')

        # Bottom status
        bottom = ttk.Frame(self, padding=(8,0,8,8)); bottom.pack(fill='x')
        self.status = tk.StringVar(value="Ready")
        ttk.Label(bottom, textvariable=self.status, anchor='w').pack(side='left')
        self.pb = ttk.Progressbar(bottom, mode='determinate', length=200)
        self.pb.pack(side='right')

    # -------- Unpack Commands --------
    def cmd_open(self):
        path = filedialog.askopenfilename(title="Open VBF", filetypes=[("VBF files", "*.vbf"), ("All files", "*.*")])
        if not path: return
        self._load_vbf(Path(path))

    def _load_vbf(self, path: Path):
        try:
            if self.mm is not None: self.mm.close()
        except Exception:
            pass

        fh = path.open('rb')
        mm = mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ)
        self.mm = mm; self.path = path
        self.lbl_file.config(text=f"File: {path.name}")

        start, end = _find_header_bounds(mm)
        header_bytes = mm[:end]
        self.header_text = header_bytes.decode('latin-1', errors='ignore')
        self.header_end = end

        self.header_fields, self.header_crc32 = parse_header_fields(self.header_text)

        self.pb['value'] = 0
        self.status.set("Parsing blocks…"); self.update_idletasks()
        sections = parse_blocks(mm, self.header_end, on_progress=lambda f: self._set_progress(int(f*100)))
        self.sections = sections; self._set_progress(100)

        self.txt_hdr.delete("1.0", "end"); self.txt_hdr.insert("1.0", self.header_text)
        self.txt_json.delete("1.0", "end"); self.txt_json.insert("1.0", json.dumps(self.header_fields, indent=2, ensure_ascii=False))

        for iid in self.tree.get_children(): self.tree.delete(iid)
        for s in sections:
            ok = "✔" if s.crc_calc == s.crc_stored else "✖"
            self.tree.insert("", "end", iid=str(s.index), values=(
                s.index, f"0x{s.start_addr:08X}", f"{s.length:,}",
                f"0x{s.crc_stored:04X} / 0x{s.crc_calc:04X}", ok
            ))

        checksum_note = ""
        if self.header_crc32 is not None:
            calc = crc32_file(mm)
            checksum_note = f" | file_checksum header=0x{self.header_crc32:08X} calc=0x{calc:08X} ({'OK' if calc==self.header_crc32 else 'MISMATCH'})"
        self.status.set(f"Loaded {path.name}: {len(sections)} block(s){checksum_note}")

    def _set_progress(self, v: int):
        self.pb['value'] = v; self.update_idletasks()

    def cmd_choose_out(self):
        d = filedialog.askdirectory(title="Choose Output Folder")
        if not d: return
        self.outdir = Path(d)
        self.lbl_out.config(text=f"Output: {self.outdir}")

    def _ensure_outdir(self) -> Path:
        if self.outdir is None:
            self.outdir = self.path.with_suffix("")
            self.outdir = Path(str(self.outdir) + "_unpacked")
            self.lbl_out.config(text=f"Output: {self.outdir}")
        self.outdir.mkdir(parents=True, exist_ok=True)
        return self.outdir

    def _write_header_sidecars(self, outdir: Path):
        (outdir / f"{self.path.name}_ascii_head.txt").write_text(self.header_text, encoding="utf-8", errors="ignore")
        (outdir / f"{self.path.name}_config.json").write_text(json.dumps(self.header_fields, indent=2, ensure_ascii=False), encoding="utf-8")

    def cmd_extract_selected(self):
        if not self.sections: return
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("Nothing selected", "Pick a block in the list."); return
        idx = int(sel[0])
        sec = next((s for s in self.sections if s.index == idx), None)
        if not sec: return
        outdir = self._ensure_outdir()
        self._write_header_sidecars(outdir)
        out_name = f"{self.path.name}_section_{sec.index:03d}_{sec.start_addr:08X}_len_{sec.length:06X}.bin"
        out_path = outdir / out_name
        with out_path.open('wb') as fh:
            fh.write(self.mm[sec.data_off:sec.data_off+sec.length])
        self.status.set(f"Extracted block #{sec.index} → {out_path}")
        messagebox.showinfo("Extracted", str(out_path))

    def cmd_extract_all(self):
        if not self.sections: return
        outdir = self._ensure_outdir()
        self._write_header_sidecars(outdir)
        count = 0
        for sec in self.sections:
            out_name = f"{self.path.name}_section_{sec.index:03d}_{sec.start_addr:08X}_len_{sec.length:06X}.bin"
            out_path = outdir / out_name
            with out_path.open('wb') as fh:
                fh.write(self.mm[sec.data_off:sec.data_off+sec.length])
            count += 1
        self.status.set(f"Extracted {count} block(s) → {outdir}")
        messagebox.showinfo("Done", f"Extracted {count} block(s) to:\n{outdir}")

    def cmd_about(self):
        messagebox.showinfo(
            "About",
            "VBF Unpacker/Pack­er by Jakka351\n"
            "Block CRC16 verify, optional file CRC32, and a full Pack tab.\n"
            "github.com/jakka351"
        )

    # -------- Pack Tab Commands --------
    def pk_load_header(self):
        p = filedialog.askopenfilename(title="Load Header Text",
                                       filetypes=[("Text/Headers", "*.txt *.h *.hdr *.vbf"), ("All files","*.*")])
        if not p: return
        pth = Path(p)
        data = pth.read_bytes()
        # If it's a .vbf, try to slice header only
        text: str
        if pth.suffix.lower() == ".vbf":
            try:
                with pth.open("rb") as fh:
                    mm = mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ)
                    _, end = _find_header_bounds(mm)
                    text = mm[:end].decode("latin-1", errors="ignore")
                    mm.close()
            except Exception:
                text = data.decode("latin-1", errors="ignore")
        else:
            text = data.decode("latin-1", errors="ignore")
        self.txt_pk_hdr.delete("1.0", "end"); self.txt_pk_hdr.insert("1.0", text)
        self.pack_header_loaded_from = pth
        self.lbl_header_src.config(text=f"Header source: {pth.name}")
        self.status.set("Header loaded into editor")

    def pk_save_header_as(self):
        text = self.txt_pk_hdr.get("1.0","end").encode("latin-1", errors="ignore")
        p = filedialog.asksaveasfilename(defaultextension=".txt", title="Save Header As")
        if not p: return
        Path(p).write_bytes(text)
        self.status.set(f"Header saved → {p}")

    def pk_add_bin(self):
        """Add multiple binaries; ask once for base start address and lay them back-to-back."""
        fps = filedialog.askopenfilenames(
            title="Select Binary Files",
            filetypes=[("Binary files","*.bin *.img *.bin2 *.dat *.hex"), ("All files","*.*")]
        )
        if not fps: return
        s = simpledialog.askstring("Start Address",
                                   "Enter start address for the first file (hex like 0x7E000 or decimal):")
        if s is None: return
        s = s.strip()
        try:
            base_addr = int(s, 16) if s.lower().startswith("0x") else int(s)
        except Exception:
            messagebox.showerror("Bad address", f"Could not parse address: {s}")
            return

        addr = base_addr
        for fp in fps:
            pth = Path(fp)
            length = pth.stat().st_size
            self.pack_items.append((pth, addr, length))
            # default: contiguous placement; edit later if you need gaps/align
            addr += length
        self._pk_refresh_tree()

    def pk_remove_selected(self):
        sel = self.tree_pk.selection()
        if not sel: return
        idx = int(sel[0]) - 1
        if 0 <= idx < len(self.pack_items):
            del self.pack_items[idx]
            self._pk_refresh_tree()

    def pk_move_sel(self, delta: int):
        sel = self.tree_pk.selection()
        if not sel: return
        idx = int(sel[0]) - 1
        j = idx + delta
        if 0 <= idx < len(self.pack_items) and 0 <= j < len(self.pack_items):
            self.pack_items[idx], self.pack_items[j] = self.pack_items[j], self.pack_items[idx]
            self._pk_refresh_tree()
            self.tree_pk.selection_set(str(j+1))

    def _pk_refresh_tree(self):
        for iid in self.tree_pk.get_children(): self.tree_pk.delete(iid)
        for i, (pth, addr, length) in enumerate(self.pack_items, start=1):
            self.tree_pk.insert("", "end", iid=str(i), values=(i, f"0x{addr:08X}", f"{length:,}", str(pth)))

    def pk_build(self):
        # Get/validate header text
        raw_header = self.txt_pk_hdr.get("1.0","end").rstrip("\n")
        if not raw_header.strip():
            messagebox.showerror("No header", "Load or paste a header first."); return

        hb = raw_header.encode("latin-1", errors="ignore")
        o = hb.find(b'{'); c = hb.rfind(b'}')
        if o < 0 or c < 0 or c < o:
            messagebox.showerror("Header error", "Header lacks a proper { ... } block."); return

        if not self.pack_items:
            messagebox.showerror("No blocks", "Add at least one BIN + address."); return

        # Choose output path
        outp = filedialog.asksaveasfilename(title="Save VBF As", defaultextension=".vbf",
                                            filetypes=[("VBF files","*.vbf"), ("All files","*.*")])
        if not outp: return
        out_path = Path(outp)

        try:
            self.status.set("Building VBF…"); self._set_progress(0); self.update_idletasks()

            # 1) Build payload: [addr][len][data][crc16] per block
            payload_parts: List[bytes] = []
            total_bins = len(self.pack_items)
            for i, (pth, addr, length) in enumerate(self.pack_items, start=1):
                data = pth.read_bytes()
                if len(data) != length:
                    length = len(data)  # in case file changed
                crc16 = crc16_ccitt_ffff(data)  # CCITT-FALSE over data only
                part = struct.pack(">II", addr, length) + data + struct.pack(">H", crc16)
                payload_parts.append(part)
                self._set_progress(int(10 + (i * 60) / max(1,total_bins)))  # progress 10-70%

            payload = b"".join(payload_parts)

            # 2) file_checksum stamping (if header has it AND user enabled)
            checksum_re = re.compile(r"(file_checksum\s*=\s*)0x[0-9A-Fa-f]{8}(\s*;)")
            header_has_field = checksum_re.search(raw_header) is not None
            header_bytes = raw_header.encode("latin-1", errors="ignore")

            if self.pk_do_file_crc.get() and header_has_field:
                scope = self.pk_crc_scope.get()
                if scope == "whole_file_zeroed_field":
                    header_zero = checksum_re.sub(r"\g<1>0x00000000\2", raw_header)
                    h_zero_bytes = header_zero.encode("latin-1", errors="ignore")
                    crc32_val = crc32_bytes(h_zero_bytes + payload)
                    header_final = checksum_re.sub(lambda m: f"{m.group(1)}0x{crc32_val:08X}{m.group(2)}", raw_header)
                    header_bytes = header_final.encode("latin-1", errors="ignore")

                elif scope == "payload_only":
                    crc32_val = crc32_bytes(payload)
                    header_final = checksum_re.sub(lambda m: f"{m.group(1)}0x{crc32_val:08X}{m.group(2)}", raw_header)
                    header_bytes = header_final.encode("latin-1", errors="ignore")

                elif scope == "header_only":
                    header_zero = checksum_re.sub(r"\g<1>0x00000000\2", raw_header)
                    crc32_val = crc32_bytes(header_zero.encode("latin-1", errors="ignore"))
                    header_final = checksum_re.sub(lambda m: f"{m.group(1)}0x{crc32_val:08X}{m.group(2)}", raw_header)
                    header_bytes = header_final.encode("latin-1", errors="ignore")
                else:
                    pass  # unknown -> do nothing

            # 3) Write final file
            out_path.write_bytes(header_bytes + payload)
            self._set_progress(100)
            self.status.set(f"Built VBF → {out_path.name} ({out_path.stat().st_size:,} bytes)")
            messagebox.showinfo("Done", f"VBF written:\n{out_path}")

        except Exception as e:
            messagebox.showerror("Pack error", f"{type(e).__name__}: {e}")

# ---- main ----
if __name__ == "__main__":
    app = VBFGui()
    app.mainloop()
