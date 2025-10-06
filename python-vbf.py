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
VBF Unpacker GUI by Jakka351
- Finds ASCII header using quote-aware brace matching.
- Parses big-endian blocks: [u32 addr][u32 len][data...][u16 CRC16-CCITT].
- Verifies per-block CRC16 (init=0xFFFF, poly=0x1021) and optional header file_checksum (CRC32).
- Uses mmap for speed and low RAM, handles huge VBFs.
- Extracts selected/all blocks to disk with informative names.

References for format & layout:
- MK4 Wiki (header + block structure; CRC16-CCITT) — Volvo/Ford VBF. 
- esaulenka/vbf_parser readme (same block layout summary).

"""

from __future__ import annotations
import io
import os
import re
import sys
import zlib
import mmap
import json
import struct
from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple, Optional

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

# ---------- CRCs ----------

CRC16_POLY = 0x1021
CRC16_INIT = 0xFFFF

def crc16_ccitt_ffff(data: memoryview | bytes) -> int:
    """CRC-16/CCITT-FALSE (poly 0x1021, init 0xFFFF)."""
    crc = CRC16_INIT
    # use memoryview for speed where possible
    mv = memoryview(data) if not isinstance(data, memoryview) else data
    for b in mv:
        crc ^= (b << 8) & 0xFFFF
        for _ in range(8):
            if crc & 0x8000:
                crc = ((crc << 1) ^ CRC16_POLY) & 0xFFFF
            else:
                crc = (crc << 1) & 0xFFFF
    return crc & 0xFFFF

def crc32_file(mm: mmap.mmap) -> int:
    """CRC32 (same as zlib.crc32 over bytes)."""
    # Iterate in chunks to avoid making big copies
    pos = 0
    crc = 0
    blksz = 1 << 20
    size = len(mm)
    while pos < size:
        end = min(size, pos + blksz)
        crc = zlib.crc32(mm[pos:end], crc)
        pos = end
    return crc & 0xFFFFFFFF

# ---------- Parsing ----------

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
    text_view = mm  # treat as bytes
    lower = mm.read().lower()
    mm.seek(0)
    hidx = lower.find(b'header')
    if hidx < 0:
        # Some files may have BOM/odd spacing. As a fallback, scan the first meg for '{' after a vbf_version line.
        head = lower[:min(2_000_000, len(mm))]
        if b'vbf_version' in head:
            # assume header starts at first '{' after vbf_version
            vpos = head.find(b'vbf_version')
            obr = head.find(b'{', vpos)
            cpos = _match_brace(mm, obr)
            if obr < 0 or cpos < 0:
                raise ValueError("Could not locate 'header { ... }' block.")
            return (vpos, cpos + 1)
        raise ValueError("No 'header' keyword found; not a VBF or header corrupted.")
    # find first '{' after 'header'
    obr = lower.find(b'{', hidx)
    if obr < 0:
        raise ValueError("Found 'header' but no opening '{'.")
    cpos = _match_brace(mm, obr)
    if cpos < 0:
        raise ValueError("Header brace matching failed (unbalanced braces or unterminated quotes).")
    return (hidx, cpos + 1)

def _match_brace(mm: mmap.mmap, obr: int) -> int:
    """
    Given the offset of an opening '{', find the matching '}' respecting quoted strings.
    Returns the index of the matching '}', or -1.
    """
    i = obr
    depth = 0
    size = len(mm)
    in_str = False
    esc = False
    while i < size:
        c = mm[i]
        i += 1
        if in_str:
            if esc:
                esc = False
                continue
            if c == 0x5C:       # backslash '\'
                esc = True
                continue
            if c == 0x22:       # '"'
                in_str = False
            continue
        # not inside string
        if c == 0x22:           # '"'
            in_str = True
            continue
        if c == 0x7B:           # '{'
            depth += 1
            continue
        if c == 0x7D:           # '}'
            depth -= 1
            if depth == 0:
                return i - 1
            continue
    return -1

def parse_header_fields(header_text: str) -> Tuple[dict, Optional[int]]:
    """
    Very light parser to pull key fields and numeric constants.
    Returns (fields_dict, file_checksum_value_if_present).
    """
    # strip // comments
    lines = []
    for line in header_text.splitlines():
        if '//' in line:
            line = line.split('//', 1)[0]
        lines.append(line)
    txt = '\n'.join(lines)

    # capture key=value; pairs (top-level)
    kv_re = re.compile(r'([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*?);', re.DOTALL)
    fields = {}
    file_crc = None
    for m in kv_re.finditer(txt):
        k = m.group(1)
        v = m.group(2).strip()
        # blocklike value { ... } keep raw
        if v.startswith('{') and v.endswith('}'):
            fields[k] = v[1:-1].strip()
            continue
        # quoted string
        if v.startswith('"') and v.endswith('"'):
            fields[k] = v[1:-1]
            continue
        # numerics/idents
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
        # plain number?
        try:
            if '.' in v:
                fields[k] = float(v)
            else:
                fields[k] = int(v)
        except Exception:
            fields[k] = v
    return fields, file_crc

def parse_blocks(mm: mmap.mmap, start_off: int, on_progress=None) -> List[VBFSection]:
    """
    Walk payload blocks starting from start_off:
      [addr: u32 BE][len: u32 BE][data: len bytes][crc: u16 BE]
    Stop when remaining bytes < minimal block header (or a sanity check fails).
    """
    total = len(mm)
    p = start_off
    idx = 1
    sections: List[VBFSection] = []
    min_hdr = 4 + 4 + 2  # minimal addr+len+crc with 0 data (rare)
    while p + min_hdr <= total:
        # Read address and length
        addr = struct.unpack_from('>I', mm, p)[0]; p += 4
        length = struct.unpack_from('>I', mm, p)[0]; p += 4
        if length < 0 or p + length + 2 > total:
            # No more sane blocks; bail
            break
        data_off = p
        data_mv = memoryview(mm)[data_off:data_off+length]
        p += length
        crc_stored = struct.unpack_from('>H', mm, p)[0]; p += 2
        crc_calc = crc16_ccitt_ffff(data_mv)

        sections.append(VBFSection(
            index=idx,
            start_addr=addr,
            length=length,
            data_off=data_off,
            crc_stored=crc_stored,
            crc_calc=crc_calc
        ))
        idx += 1
        if on_progress and (idx % 64 == 0):
            on_progress(p / total)
    return sections

# ---------- GUI ----------

class VBFGui(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("VBF Unpacker — github.com/Jakka351")
        self.geometry("1200x760")
        self.minsize(1000, 640)

        self.mm: Optional[mmap.mmap] = None
        self.path: Optional[Path] = None
        self.header_text: str = ""
        self.header_end: int = 0
        self.header_fields: dict = {}
        self.header_crc32: Optional[int] = None
        self.sections: List[VBFSection] = []

        self.outdir: Optional[Path] = None

        self._build_menu()
        self._build_ui()

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

    def _build_ui(self):
        top = ttk.Frame(self, padding=8); top.pack(fill='x')
        self.lbl_file = ttk.Label(top, text="No file loaded"); self.lbl_file.pack(side='left')
        self.lbl_out = ttk.Label(top, text="Output: (not set)"); self.lbl_out.pack(side='right')

        paned = ttk.Panedwindow(self, orient='horizontal'); paned.pack(fill='both', expand=True, padx=8, pady=8)

        # Left: tree of sections
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

        # Header (raw)
        tab_hdr = ttk.Frame(right); right.add(tab_hdr, text="Header")
        self.txt_hdr = tk.Text(tab_hdr, wrap='none')
        y1 = ttk.Scrollbar(tab_hdr, orient='vertical', command=self.txt_hdr.yview)
        x1 = ttk.Scrollbar(tab_hdr, orient='horizontal', command=self.txt_hdr.xview)
        self.txt_hdr.configure(yscrollcommand=y1.set, xscrollcommand=x1.set)
        self.txt_hdr.pack(side='top', fill='both', expand=True); y1.pack(side='right', fill='y'); x1.pack(side='bottom', fill='x')

        # Header (JSON-ish)
        tab_json = ttk.Frame(right); right.add(tab_json, text="Header (JSON)")
        self.txt_json = tk.Text(tab_json, wrap='none')
        y2 = ttk.Scrollbar(tab_json, orient='vertical', command=self.txt_json.yview)
        x2 = ttk.Scrollbar(tab_json, orient='horizontal', command=self.txt_json.xview)
        self.txt_json.configure(yscrollcommand=y2.set, xscrollcommand=x2.set)
        self.txt_json.pack(side='top', fill='both', expand=True); y2.pack(side='right', fill='y'); x2.pack(side='bottom', fill='x')

        # Status + progress
        bottom = ttk.Frame(self, padding=(8,0,8,8)); bottom.pack(fill='x')
        self.status = tk.StringVar(value="Ready")
        ttk.Label(bottom, textvariable=self.status, anchor='w').pack(side='left')
        self.pb = ttk.Progressbar(bottom, mode='determinate', length=200)
        self.pb.pack(side='right')

    # -------- Commands --------

    def cmd_open(self):
        path = filedialog.askopenfilename(title="Open VBF", filetypes=[("VBF files", "*.vbf"), ("All files", "*.*")])
        if not path:
            return
        self._load_vbf(Path(path))

    def _load_vbf(self, path: Path):
        # close previous
        try:
            if self.mm is not None:
                self.mm.close()
        except Exception:
            pass

        fh = path.open('rb')
        mm = mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ)
        self.mm = mm
        self.path = path
        self.lbl_file.config(text=f"File: {path.name}")

        # header bounds
        start, end = _find_header_bounds(mm)
        header_bytes = mm[:end]
        self.header_text = header_bytes.decode('latin-1', errors='ignore')
        self.header_end = end

        self.header_fields, self.header_crc32 = parse_header_fields(self.header_text)

        # blocks
        self.pb['value'] = 0
        self.status.set("Parsing blocks…")
        self.update_idletasks()
        sections = parse_blocks(mm, self.header_end, on_progress=lambda f: self._set_progress(int(f*100)))
        self.sections = sections
        self._set_progress(100)

        # UI populate
        self.txt_hdr.delete("1.0", "end"); self.txt_hdr.insert("1.0", self.header_text)
        self.txt_json.delete("1.0", "end"); self.txt_json.insert("1.0", json.dumps(self.header_fields, indent=2, ensure_ascii=False))

        for iid in self.tree.get_children():
            self.tree.delete(iid)
        for s in sections:
            ok = "✔" if s.crc_calc == s.crc_stored else "✖"
            self.tree.insert("", "end", iid=str(s.index), values=(
                s.index,
                f"0x{s.start_addr:08X}",
                f"{s.length:,}",
                f"0x{s.crc_stored:04X} / 0x{s.crc_calc:04X}",
                ok
            ))

        # optional file checksum verify (header value vs computed)
        checksum_note = ""
        if self.header_crc32 is not None:
            calc = crc32_file(mm)
            checksum_note = f" | file_checksum header=0x{self.header_crc32:08X} calc=0x{calc:08X} ({'OK' if calc==self.header_crc32 else 'MISMATCH'})"
        self.status.set(f"Loaded {path.name}: {len(sections)} block(s){checksum_note}")

    def _set_progress(self, v: int):
        self.pb['value'] = v
        self.update_idletasks()

    def cmd_choose_out(self):
        d = filedialog.askdirectory(title="Choose Output Folder")
        if not d:
            return
        self.outdir = Path(d)
        self.lbl_out.config(text=f"Output: {self.outdir}")

    def _ensure_outdir(self) -> Path:
        if self.outdir is None:
            self.outdir = self.path.with_suffix("")  # strip .vbf
            self.outdir = Path(str(self.outdir) + "_unpacked")
            self.lbl_out.config(text=f"Output: {self.outdir}")
        self.outdir.mkdir(parents=True, exist_ok=True)
        return self.outdir

    def _write_header_sidecars(self, outdir: Path):
        (outdir / f"{self.path.name}_ascii_head.txt").write_text(self.header_text, encoding="utf-8", errors="ignore")
        (outdir / f"{self.path.name}_config.json").write_text(json.dumps(self.header_fields, indent=2, ensure_ascii=False), encoding="utf-8")

    def cmd_extract_selected(self):
        if not self.sections:
            return
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("Nothing selected", "Pick a block in the list.")
            return
        idx = int(sel[0])
        sec = next((s for s in self.sections if s.index == idx), None)
        if not sec:
            return
        outdir = self._ensure_outdir()
        self._write_header_sidecars(outdir)
        out_name = f"{self.path.name}_section_{sec.index:03d}_{sec.start_addr:08X}_len_{sec.length:06X}.bin"
        out_path = outdir / out_name
        with out_path.open('wb') as fh:
            fh.write(self.mm[sec.data_off:sec.data_off+sec.length])
        self.status.set(f"Extracted block #{sec.index} → {out_path}")
        messagebox.showinfo("Extracted", str(out_path))

    def cmd_extract_all(self):
        if not self.sections:
            return
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
            "VBF Unpacker by Jakka351\n"
            "Header brace-matching, CRC16 block verify, optional file CRC32 check.\n"
            "github.com/jakka351"
        )

if __name__ == "__main__":
    app = VBFGui()
    # keep styling simple and native
    app.mainloop()
