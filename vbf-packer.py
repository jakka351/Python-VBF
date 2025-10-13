#packer doesnt work correctly 
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
VBF Unpacker + Packer GUI with PROPER Python LZSS Implementation
Based on the C++ algorithm, fully rewritten in Python
By Jakka351
"""

from __future__ import annotations
import re
import zlib
import mmap
import json
import struct
import threading
import queue
from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple, Optional, Callable

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog

# ---------- PROPER Python LZSS Implementation ----------

class TreeNode:
    """Binary tree node for LZSS"""
    def __init__(self):
        self.parent: int = 0
        self.small_child: int = 0
        self.large_child: int = 0

class LZSSContext:
    """LZSS compression context matching C++ implementation"""
    def __init__(self):
        self.compressed_data = bytearray()
        self.out_bit: int = 128
        self.out_len: int = 0
        self.in_bit: int = 128
        self.lzss_window = bytearray(1024)
        self.match_len: int = 0
        self.tree: List[TreeNode] = [TreeNode() for _ in range(1025)]
        self.current_byte: int = 0

def lzss_init_tree(root_child: int, ctx: LZSSContext) -> LZSSContext:
    """Initialize the binary search tree"""
    ctx.tree[1024].parent = 0
    ctx.tree[1024].small_child = 0
    ctx.tree[1024].large_child = root_child
    ctx.tree[root_child].parent = 1024
    ctx.tree[root_child].large_child = 0
    ctx.tree[root_child].small_child = 0
    return ctx

def lzss_contract_node(old_node: int, new_node: int, ctx: LZSSContext) -> LZSSContext:
    """Contract a node in the tree"""
    ctx.tree[new_node].parent = ctx.tree[old_node].parent
    if ctx.tree[ctx.tree[old_node].parent].large_child == old_node:
        ctx.tree[ctx.tree[old_node].parent].large_child = new_node
    else:
        ctx.tree[ctx.tree[old_node].parent].small_child = new_node
    ctx.tree[old_node].parent = 0
    ctx.tree[old_node].small_child = 0
    ctx.tree[old_node].large_child = 0
    return ctx

def lzss_replace_node(old_node: int, new_node: int, ctx: LZSSContext) -> LZSSContext:
    """Replace a node in the tree"""
    if ctx.tree[ctx.tree[old_node].parent].small_child == old_node:
        ctx.tree[ctx.tree[old_node].parent].small_child = new_node
    else:
        ctx.tree[ctx.tree[old_node].parent].large_child = new_node
    
    ctx.tree[new_node].parent = ctx.tree[old_node].parent
    ctx.tree[new_node].small_child = ctx.tree[old_node].small_child
    ctx.tree[new_node].large_child = ctx.tree[old_node].large_child
    
    ctx.tree[ctx.tree[new_node].small_child].parent = new_node
    ctx.tree[ctx.tree[new_node].large_child].parent = new_node
    
    ctx.tree[old_node].parent = 0
    ctx.tree[old_node].small_child = 0
    ctx.tree[old_node].large_child = 0
    return ctx

def lzss_find_next_node(node: int, ctx: LZSSContext) -> int:
    """Find the next node in the tree"""
    next_node = ctx.tree[node].small_child
    while ctx.tree[next_node].large_child:
        next_node = ctx.tree[next_node].large_child
    return next_node

def lzss_delete_node(node: int, ctx: LZSSContext) -> LZSSContext:
    """Delete a node from the tree"""
    if ctx.tree[node].large_child:
        if ctx.tree[node].small_child:
            repl_node = lzss_find_next_node(node, ctx)
            ctx = lzss_contract_node(repl_node, ctx.tree[repl_node].small_child, ctx)
            ctx = lzss_replace_node(node, repl_node, ctx)
        else:
            ctx = lzss_contract_node(node, ctx.tree[node].large_child, ctx)
    else:
        ctx = lzss_contract_node(node, ctx.tree[node].small_child, ctx)
    return ctx

def lzss_add_node(new_node: int, lzss_window: bytearray, ctx: LZSSContext) -> Tuple[LZSSContext, int]:
    """Add a node to the tree and return match position"""
    match_pos = 0
    match_done = False
    
    if new_node == 0:
        ctx.match_len = 0
        return ctx, match_pos
    
    test_node = ctx.tree[1024].large_child
    match_len = 0
    
    while not match_done:
        test_node_3 = 0
        delta = 0
        
        # Compare bytes
        while test_node_3 <= 0x10 and delta == 0:
            idx1 = (new_node + test_node_3) & 0x3FF
            idx2 = (test_node + test_node_3) & 0x3FF
            delta = lzss_window[idx1] - lzss_window[idx2]
            test_node_3 += 1
        
        if delta:
            test_node_3 -= 1
        
        if test_node_3 >= match_len:
            match_len = test_node_3
            match_pos = test_node
            if test_node_3 > 0x10:
                ctx = lzss_replace_node(test_node, new_node, ctx)
                ctx.match_len = test_node_3
                match_done = True
        
        if not match_done:
            if delta < 0:
                child_ptr = ctx.tree[test_node].small_child
                if child_ptr == 0:
                    ctx.tree[test_node].small_child = new_node
                    ctx.tree[new_node].parent = test_node
                    ctx.tree[new_node].large_child = 0
                    ctx.tree[new_node].small_child = 0
                    ctx.match_len = match_len
                    match_done = True
                else:
                    test_node = child_ptr
            else:
                child_ptr = ctx.tree[test_node].large_child
                if child_ptr == 0:
                    ctx.tree[test_node].large_child = new_node
                    ctx.tree[new_node].parent = test_node
                    ctx.tree[new_node].large_child = 0
                    ctx.tree[new_node].small_child = 0
                    ctx.match_len = match_len
                    match_done = True
                else:
                    test_node = child_ptr
    
    return ctx, match_pos

def output_bits(bits: int, num_bits: int, ctx: LZSSContext) -> LZSSContext:
    """Output bits to the compressed stream"""
    bit_value = 1 << (num_bits - 1)
    
    for _ in range(num_bits):
        if ctx.out_bit == 128:
            ctx.compressed_data.append(0)
            ctx.current_byte = len(ctx.compressed_data) - 1
            ctx.out_len += 1
        
        if bits & bit_value:
            ctx.compressed_data[ctx.current_byte] |= ctx.out_bit
        
        if ctx.out_bit == 1:
            ctx.out_bit = 128
        else:
            ctx.out_bit >>= 1
        
        bit_value >>= 1
    
    return ctx

def lzss_compress_data(input_buffer: bytes, on_progress: Optional[Callable[[float], None]] = None) -> bytes:
    """
    Compress data using LZSS algorithm - Python implementation of C++ version
    This matches the exact C++ algorithm behavior
    """
    ctx = LZSSContext()
    input_length = len(input_buffer)
    
    if input_length == 0:
        return bytes()
    
    # Initialize
    win_pos = 1
    repl_cnt = 0
    match_pos = 0
    eos_reached = False
    in_ptr = 0
    
    ctx.out_bit = 128
    ctx.out_len = 0
    
    # Clear window and tree
    for i in range(1024):
        ctx.lzss_window[i] = 0
    for i in range(1025):
        ctx.tree[i] = TreeNode()
    
    # Fill initial window
    byte2_win = (win_pos >> 16) & 0xFF
    while byte2_win <= 0x10 and not eos_reached:
        if in_ptr < input_length:
            match_pos_hi = input_buffer[in_ptr]
            in_ptr += 1
            
            idx = byte2_win + (win_pos & 0xFFFF)
            if idx < 1024:
                ctx.lzss_window[idx] = match_pos_hi
            byte2_win += 1
        else:
            eos_reached = True
        
        # Update win_pos
        win_pos = (win_pos & 0xFFFF) | (byte2_win << 16)
    
    # Initialize tree
    ctx = lzss_init_tree(win_pos & 0xFFFF, ctx)
    
    # Main compression loop
    byte2_win = (win_pos >> 16) & 0xFF
    total_iterations = 0
    max_iterations = input_length * 2
    
    while byte2_win > 0 and total_iterations < max_iterations:
        total_iterations += 1
        
        # Progress reporting
        if on_progress and total_iterations % 1000 == 0:
            progress = min(0.95, in_ptr / max(1, input_length))
            on_progress(progress)
        
        if ctx.match_len > byte2_win:
            ctx.match_len = byte2_win
        
        if ctx.match_len > 1:
            # Output match
            ctx = output_bits(0, 1, ctx)
            ctx = output_bits(match_pos & 0xFFFF, 0x0A, ctx)
            ctx = output_bits(ctx.match_len - 2, 4, ctx)
            repl_cnt = ctx.match_len
        else:
            # Output literal
            repl_cnt = 1
            ctx = output_bits(1, 1, ctx)
            literal_val = ctx.lzss_window[(win_pos & 0xFFFF) & 0x3FF]
            ctx = output_bits(literal_val, 8, ctx)
        
        # Replace bytes
        byte3_win = 0
        while byte3_win < repl_cnt:
            delete_pos = ((win_pos & 0xFFFF) + 17) & 0x3FF
            ctx = lzss_delete_node(delete_pos, ctx)
            
            if in_ptr < input_length:
                match_pos_hi = input_buffer[in_ptr]
                in_ptr += 1
                store_pos = ((win_pos & 0xFFFF) + 17) & 0x3FF
                ctx.lzss_window[store_pos] = match_pos_hi
            else:
                byte2_win -= 1
                win_pos = (win_pos & 0xFFFF) | (byte2_win << 16)
            
            # Increment window position
            win_pos_lo = ((win_pos & 0xFFFF) + 1) & 0x3FF
            win_pos = win_pos_lo | (win_pos & 0xFFFF0000)
            
            # Add node if we still have data
            byte2_check = (win_pos >> 16) & 0xFF
            if byte2_check > 0:
                ctx, match_pos = lzss_add_node(win_pos & 0xFFFF, ctx.lzss_window, ctx)
            
            byte3_win += 1
        
        byte2_win = (win_pos >> 16) & 0xFF
    
    # Write EOF marker
    ctx = output_bits(0, 1, ctx)
    ctx = output_bits(0, 0x0A, ctx)
    ctx.compressed_data.append(0)
    ctx.out_len += 1
    
    if on_progress:
        on_progress(1.0)
    
    return bytes(ctx.compressed_data[:ctx.out_len])

# ---------- CRCs ----------

def crc16_ccitt_ffff(data: memoryview | bytes) -> int:
    CRC16_POLY = 0x1021
    CRC16_INIT = 0xFFFF
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

def crc32_bytes(buf: bytes, init: int = 0) -> int:
    return zlib.crc32(buf, init) & 0xFFFFFFFF

def crc32_file(mm: mmap.mmap) -> int:
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

def _find_header_bounds(mm: mmap.mmap) -> Tuple[int, int]:
    lower = mm.read().lower()
    mm.seek(0)
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
        raise ValueError("Header brace matching failed.")
    return (hidx, cpos + 1)

def _match_brace(mm: mmap.mmap, obr: int) -> int:
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
            if c == 0x5C:
                esc = True
                continue
            if c == 0x22:
                in_str = False
            continue
        if c == 0x22:
            in_str = True
            continue
        if c == 0x7B:
            depth += 1
            continue
        if c == 0x7D:
            depth -= 1
            if depth == 0:
                return i - 1
    return -1

def parse_header_fields(header_text: str) -> Tuple[dict, Optional[int]]:
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
        k = m.group(1)
        v = m.group(2).strip()
        if v.startswith('{') and v.endswith('}'):
            fields[k] = v[1:-1].strip()
            continue
        if v.startswith('"') and v.endswith('"'):
            fields[k] = v[1:-1]
            continue
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
            if '.' in v:
                fields[k] = float(v)
            else:
                fields[k] = int(v)
        except Exception:
            fields[k] = v
    return fields, file_crc

def parse_blocks(mm: mmap.mmap, start_off: int, on_progress=None) -> List[VBFSection]:
    total = len(mm)
    p = start_off
    idx = 1
    sections: List[VBFSection] = []
    min_hdr = 4 + 4 + 2
    while p + min_hdr <= total:
        addr = struct.unpack_from('>I', mm, p)[0]
        p += 4
        length = struct.unpack_from('>I', mm, p)[0]
        p += 4
        if length < 0 or p + length + 2 > total:
            break
        data_off = p
        data_mv = memoryview(mm)[data_off:data_off+length]
        p += length
        crc_stored = struct.unpack_from('>H', mm, p)[0]
        p += 2
        crc_calc = crc16_ccitt_ffff(data_mv)
        sections.append(VBFSection(idx, addr, length, data_off, crc_stored, crc_calc))
        idx += 1
        if on_progress and (idx % 64 == 0):
            on_progress(p / total)
    return sections

# ---------- GUI ----------

PROG_SET = "PROG_SET"
STATUS_SET = "STATUS_SET"
DONE_OK = "DONE_OK"
DONE_ERR = "DONE_ERR"
ENABLE_UI = "ENABLE_UI"
DISABLE_UI = "DISABLE_UI"

class VBFGui(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("VBF Unpacker/Packer with Python LZSS — github.com/Jakka351")
        self.geometry("1280x800")
        self.minsize(1100, 700)

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
        self.pack_items: List[Tuple[Path,int,int]] = []
        self.pk_use_lzss = tk.BooleanVar(value=True)
        self.pk_do_file_crc = tk.BooleanVar(value=True)
        self.pk_crc_scope = tk.StringVar(value="whole_file_zeroed_field")

        # Worker machinery
        self._worker_thread: Optional[threading.Thread] = None
        self._worker_q: "queue.Queue[tuple]" = queue.Queue()
        self._cancel_evt: threading.Event = threading.Event()

        self._build_menu()
        self._build_ui()
        self._tick_ui()

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
        # Top status row
        top = ttk.Frame(self, padding=8)
        top.pack(fill='x')
        self.lbl_file = ttk.Label(top, text="No file loaded")
        self.lbl_file.pack(side='left')
        self.lbl_out = ttk.Label(top, text="Output: (not set)")
        self.lbl_out.pack(side='right')

        paned = ttk.Panedwindow(self, orient='horizontal')
        paned.pack(fill='both', expand=True, padx=8, pady=8)

        # Left: sections list
        left = ttk.Frame(paned)
        paned.add(left, weight=1)
        cols = ("#", "start", "len", "crc", "ok")
        self.tree = ttk.Treeview(left, columns=cols, show='headings', selectmode='browse')
        self.tree.heading("#", text="#")
        self.tree.column("#", width=60, anchor='e')
        self.tree.heading("start", text="Start Addr")
        self.tree.column("start", width=160)
        self.tree.heading("len", text="Length")
        self.tree.column("len", width=120, anchor='e')
        self.tree.heading("crc", text="CRC16")
        self.tree.column("crc", width=220)
        self.tree.heading("ok", text="OK")
        self.tree.column("ok", width=60, anchor='center')
        self.tree.pack(fill='both', expand=True)

        btns = ttk.Frame(left)
        btns.pack(fill='x', pady=(6,0))
        ttk.Button(btns, text="Extract Selected", command=self.cmd_extract_selected).pack(side='left', padx=4)
        ttk.Button(btns, text="Extract All", command=self.cmd_extract_all).pack(side='left', padx=4)

        # Right: tabs
        right = ttk.Notebook(paned)
        paned.add(right, weight=2)

        # Header tab
        tab_hdr = ttk.Frame(right)
        right.add(tab_hdr, text="Header")
        self.txt_hdr = tk.Text(tab_hdr, wrap='none')
        y1 = ttk.Scrollbar(tab_hdr, orient='vertical', command=self.txt_hdr.yview)
        x1 = ttk.Scrollbar(tab_hdr, orient='horizontal', command=self.txt_hdr.xview)
        self.txt_hdr.configure(yscrollcommand=y1.set, xscrollcommand=x1.set)
        self.txt_hdr.pack(side='top', fill='both', expand=True)
        y1.pack(side='right', fill='y')
        x1.pack(side='bottom', fill='x')

        # JSON tab
        tab_json = ttk.Frame(right)
        right.add(tab_json, text="Header (JSON)")
        self.txt_json = tk.Text(tab_json, wrap='none')
        y2 = ttk.Scrollbar(tab_json, orient='vertical', command=self.txt_json.yview)
        x2 = ttk.Scrollbar(tab_json, orient='horizontal', command=self.txt_json.xview)
        self.txt_json.configure(yscrollcommand=y2.set, xscrollcommand=x2.set)
        self.txt_json.pack(side='top', fill='both', expand=True)
        y2.pack(side='right', fill='y')
        x2.pack(side='bottom', fill='x')

        # Pack tab
        tab_pack = ttk.Frame(right)
        right.add(tab_pack, text="Pack VBF")

        # Header controls
        header_frame = ttk.LabelFrame(tab_pack, text="Header")
        header_frame.pack(fill='both', expand=False, padx=6, pady=6)
        header_btns = ttk.Frame(header_frame)
        header_btns.pack(fill='x', padx=6, pady=4)
        ttk.Button(header_btns, text="Load Header…", command=self.pk_load_header).pack(side='left', padx=4)
        ttk.Button(header_btns, text="Save Header As…", command=self.pk_save_header_as).pack(side='left', padx=4)
        self.lbl_header_src = ttk.Label(header_btns, text="(no header loaded)")
        self.lbl_header_src.pack(side='left', padx=10)

        self.txt_pk_hdr = tk.Text(header_frame, height=12, wrap='none')
        yph = ttk.Scrollbar(header_frame, orient='vertical', command=self.txt_pk_hdr.yview)
        xph = ttk.Scrollbar(header_frame, orient='horizontal', command=self.txt_pk_hdr.xview)
        self.txt_pk_hdr.configure(yscrollcommand=yph.set, xscrollcommand=xph.set)
        self.txt_pk_hdr.pack(side='top', fill='both', expand=True, padx=6)
        yph.pack(side='right', fill='y')
        xph.pack(side='bottom', fill='x')

        # BIN list
        bins_frame = ttk.LabelFrame(tab_pack, text="Blocks (addr + file)")
        bins_frame.pack(fill='both', expand=True, padx=6, pady=6)

        cols_pk = ("#", "addr", "len", "path")
        self.tree_pk = ttk.Treeview(bins_frame, columns=cols_pk, show='headings', selectmode='browse')
        self.tree_pk.heading("#", text="#")
        self.tree_pk.column("#", width=40, anchor='e')
        self.tree_pk.heading("addr", text="Start Addr")
        self.tree_pk.column("addr", width=160)
        self.tree_pk.heading("len", text="Length")
        self.tree_pk.column("len", width=120, anchor='e')
        self.tree_pk.heading("path", text="File")
        self.tree_pk.column("path", width=500)
        self.tree_pk.pack(fill='both', expand=True, padx=6, pady=4)

        pk_btns = ttk.Frame(bins_frame)
        pk_btns.pack(fill='x', padx=6, pady=(0,6))
        ttk.Button(pk_btns, text="Add BIN(s)…", command=self.pk_add_bin).pack(side='left', padx=4)
        ttk.Button(pk_btns, text="Remove", command=self.pk_remove_selected).pack(side='left', padx=4)
        ttk.Button(pk_btns, text="Move Up", command=lambda: self.pk_move_sel(-1)).pack(side='left', padx=4)
        ttk.Button(pk_btns, text="Move Down", command=lambda: self.pk_move_sel(+1)).pack(side='left', padx=4)
        self.btn_build = ttk.Button(pk_btns, text="Build VBF…", command=self.pk_build)
        self.btn_build.pack(side='right', padx=4)
        self.btn_cancel = ttk.Button(pk_btns, text="Cancel", command=self.pk_cancel, state="disabled")
        self.btn_cancel.pack(side='right', padx=4)

        # Options
        opts = ttk.LabelFrame(tab_pack, text="Compression & Checksum Options")
        opts.pack(fill='x', padx=6, pady=(0,6))
        ttk.Checkbutton(opts, text="Use LZSS Compression", variable=self.pk_use_lzss).pack(side='left', padx=6)
        ttk.Separator(opts, orient='vertical').pack(side='left', fill='y', padx=6)
        ttk.Checkbutton(opts, text="Compute file_checksum", variable=self.pk_do_file_crc).pack(side='left', padx=6)
        ttk.Label(opts, text="Scope:").pack(side='left', padx=(12,4))
        scope = ttk.Combobox(opts, textvariable=self.pk_crc_scope, state="readonly",
                             values=("whole_file_zeroed_field", "payload_only", "header_only"))
        scope.pack(side='left')

        # Bottom status
        bottom = ttk.Frame(self, padding=(8,0,8,8))
        bottom.pack(fill='x')
        self.status = tk.StringVar(value="Ready")
        ttk.Label(bottom, textvariable=self.status, anchor='w').pack(side='left')
        self.pb = ttk.Progressbar(bottom, mode='determinate', length=260, maximum=100)
        self.pb.pack(side='right')

    # -------- Unpack Commands --------
    def cmd_open(self):
        path = filedialog.askopenfilename(title="Open VBF", filetypes=[("VBF files", "*.vbf"), ("All files", "*.*")])
        if not path:
            return
        self._load_vbf(Path(path))

    def _load_vbf(self, path: Path):
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

        start, end = _find_header_bounds(mm)
        header_bytes = mm[:end]
        self.header_text = header_bytes.decode('latin-1', errors='ignore')
        self.header_end = end

        self.header_fields, self.header_crc32 = parse_header_fields(self.header_text)

        self.pb['value'] = 0
        self.status.set("Parsing blocks…")
        self.update_idletasks()
        sections = parse_blocks(mm, self.header_end, on_progress=lambda f: self._set_progress(int(f*100)))
        self.sections = sections
        self._set_progress(100)

        self.txt_hdr.delete("1.0", "end")
        self.txt_hdr.insert("1.0", self.header_text)
        self.txt_json.delete("1.0", "end")
        self.txt_json.insert("1.0", json.dumps(self.header_fields, indent=2, ensure_ascii=False))

        for iid in self.tree.get_children():
            self.tree.delete(iid)
        for s in sections:
            ok = "✔" if s.crc_calc == s.crc_stored else "✖"
            self.tree.insert("", "end", iid=str(s.index), values=(
                s.index, f"0x{s.start_addr:08X}", f"{s.length:,}",
                f"0x{s.crc_stored:04X} / 0x{s.crc_calc:04X}", ok
            ))

        checksum_note = ""
        if self.header_crc32 is not None:
            calc = crc32_file(mm)
            match = "OK" if calc == self.header_crc32 else "MISMATCH"
            checksum_note = f" | file_checksum header=0x{self.header_crc32:08X} calc=0x{calc:08X} ({match})"
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
        if self.outdir is None and self.path:
            self.outdir = self.path.with_suffix("")
            self.outdir = Path(str(self.outdir) + "_unpacked")
            self.lbl_out.config(text=f"Output: {self.outdir}")
        if self.outdir:
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
        if not outdir:
            return
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
        if not outdir:
            return
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
            "VBF Unpacker/Packer with Python LZSS by Jakka351\n"
            "Pure Python implementation of LZSS compression\n"
            "github.com/jakka351"
        )

    # -------- Pack Tab Commands --------
    def pk_load_header(self):
        p = filedialog.askopenfilename(title="Load Header Text",
                                       filetypes=[("Text/Headers", "*.txt *.h *.hdr *.vbf"), ("All files","*.*")])
        if not p:
            return
        pth = Path(p)
        data = pth.read_bytes()
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
        self.txt_pk_hdr.delete("1.0", "end")
        self.txt_pk_hdr.insert("1.0", text)
        self.lbl_header_src.config(text=f"Header source: {pth.name}")
        self.status.set("Header loaded into editor")

    def pk_save_header_as(self):
        text = self.txt_pk_hdr.get("1.0","end").encode("latin-1", errors="ignore")
        p = filedialog.asksaveasfilename(defaultextension=".txt", title="Save Header As")
        if not p:
            return
        Path(p).write_bytes(text)
        self.status.set(f"Header saved → {p}")

    def pk_add_bin(self):
        fps = filedialog.askopenfilenames(
            title="Select Binary Files",
            filetypes=[("Binary files","*.bin *.img *.bin2 *.dat *.hex"), ("All files","*.*")]
        )
        if not fps:
            return
        s = simpledialog.askstring("Start Address",
                                   "Enter start address for the first file (hex like 0x7E000 or decimal):")
        if s is None:
            return
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
            addr += length
        self._pk_refresh_tree()

    def pk_remove_selected(self):
        sel = self.tree_pk.selection()
        if not sel:
            return
        idx = int(sel[0]) - 1
        if 0 <= idx < len(self.pack_items):
            del self.pack_items[idx]
            self._pk_refresh_tree()

    def pk_move_sel(self, delta: int):
        sel = self.tree_pk.selection()
        if not sel:
            return
        idx = int(sel[0]) - 1
        j = idx + delta
        if 0 <= idx < len(self.pack_items) and 0 <= j < len(self.pack_items):
            self.pack_items[idx], self.pack_items[j] = self.pack_items[j], self.pack_items[idx]
            self._pk_refresh_tree()
            self.tree_pk.selection_set(str(j+1))

    def _pk_refresh_tree(self):
        for iid in self.tree_pk.get_children():
            self.tree_pk.delete(iid)
        for i, (pth, addr, length) in enumerate(self.pack_items, start=1):
            self.tree_pk.insert("", "end", iid=str(i), values=(i, f"0x{addr:08X}", f"{length:,}", str(pth)))

    # ---- Worker plumbing ----
    def pk_build(self):
        raw_header = self.txt_pk_hdr.get("1.0","end").rstrip("\n")
        if not raw_header.strip():
            messagebox.showerror("No header", "Load or paste a header first.")
            return
        if not self.pack_items:
            messagebox.showerror("No blocks", "Add at least one BIN + address.")
            return

        hb = raw_header.encode("latin-1", errors="ignore")
        o = hb.find(b'{')
        c = hb.rfind(b'}')
        if o < 0 or c < 0 or c < o:
            messagebox.showerror("Header error", "Header lacks a proper { ... } block.")
            return

        outp = filedialog.asksaveasfilename(title="Save VBF As", defaultextension=".vbf",
                                            filetypes=[("VBF files","*.vbf"), ("All files","*.*")])
        if not outp:
            return
        out_path = Path(outp)

        if self._worker_thread and self._worker_thread.is_alive():
            messagebox.showwarning("Busy", "A build is already running.")
            return

        self._cancel_evt.clear()
        self._worker_q.put((DISABLE_UI, None))
        args = dict(
            raw_header=raw_header,
            out_path=out_path,
            pack_items=self.pack_items.copy(),
            use_lzss=self.pk_use_lzss.get(),
            do_crc=self.pk_do_file_crc.get(),
            crc_scope=self.pk_crc_scope.get(),
        )
        self._worker_thread = threading.Thread(target=self._worker_build, kwargs=args, daemon=True)
        self._worker_thread.start()

    def pk_cancel(self):
        if self._worker_thread and self._worker_thread.is_alive():
            self._cancel_evt.set()
            self._worker_q.put((STATUS_SET, "Cancelling…"))

    def _tick_ui(self):
        try:
            while True:
                kind, payload = self._worker_q.get_nowait()
                if kind == PROG_SET:
                    self.pb['value'] = int(payload)
                elif kind == STATUS_SET:
                    self.status.set(str(payload))
                elif kind == DISABLE_UI:
                    self.btn_build.config(state="disabled")
                    self.btn_cancel.config(state="normal")
                    self.pb['value'] = 0
                    self.status.set("Starting build…")
                elif kind == ENABLE_UI:
                    self.btn_build.config(state="normal")
                    self.btn_cancel.config(state="disabled")
                elif kind == DONE_OK:
                    self.pb['value'] = 100
                    self.status.set(payload)
                    messagebox.showinfo("Done", payload)
                elif kind == DONE_ERR:
                    self.status.set("Build failed")
                    messagebox.showerror("Pack error", payload)
        except queue.Empty:
            pass
        self.after(100, self._tick_ui)

    # ---- Background worker ----
    def _worker_build(self, *, raw_header: str, out_path: Path, pack_items: List[Tuple[Path,int,int]],
                      use_lzss: bool, do_crc: bool, crc_scope: str):
        try:
            self._worker_q.put((STATUS_SET, "Building VBF…"))
            self._worker_q.put((PROG_SET, 5))

            checksum_re = re.compile(r"(file_checksum\s*=\s*)0x[0-9A-Fa-f]{8}(\s*;)")
            header_has_field = checksum_re.search(raw_header) is not None

            header_bytes = raw_header.encode("latin-1", errors="ignore")
            patch_offset = None

            def locate_patch_offset(text_for_search: str) -> Optional[int]:
                m = checksum_re.search(text_for_search)
                if not m:
                    return None
                prefix = m.group(1)
                before = text_for_search[:m.start()] + prefix
                return len(before)

            if not do_crc or not header_has_field:
                header_to_write = header_bytes
                patch_after = False
                crc32_acc = None
            elif crc_scope == "header_only":
                header_zero = checksum_re.sub(r"\g<1>0x00000000\2", raw_header)
                crc = crc32_bytes(header_zero.encode("latin-1", errors="ignore"))
                header_final = checksum_re.sub(lambda m: f"{m.group(1)}0x{crc:08X}{m.group(2)}", raw_header)
                header_to_write = header_final.encode("latin-1", errors="ignore")
                patch_after = False
                crc32_acc = None
            elif crc_scope == "payload_only":
                header_zero = checksum_re.sub(r"\g<1>0x00000000\2", raw_header)
                header_to_write = header_zero.encode("latin-1", errors="ignore")
                patch_after = True
                patch_offset = locate_patch_offset(header_zero)
                crc32_acc = 0
            elif crc_scope == "whole_file_zeroed_field":
                header_zero = checksum_re.sub(r"\g<1>0x00000000\2", raw_header)
                header_to_write = header_zero.encode("latin-1", errors="ignore")
                patch_after = True
                patch_offset = locate_patch_offset(header_zero)
                crc32_acc = crc32_bytes(header_to_write)
            else:
                header_zero = checksum_re.sub(r"\g<1>0x00000000\2", raw_header)
                header_to_write = header_zero.encode("latin-1", errors="ignore")
                patch_after = True
                patch_offset = locate_patch_offset(header_zero)
                crc32_acc = 0

            with out_path.open("wb+") as fh:
                fh.write(header_to_write)

                if use_lzss:
                    # Use Python LZSS compression
                    self._worker_q.put((STATUS_SET, "Compressing with LZSS…"))
                    self._worker_q.put((PROG_SET, 10))
                    
                    # Read all binary data
                    all_data = bytearray()
                    for (pth, _addr, _len) in pack_items:
                        if self._cancel_evt.is_set():
                            raise KeyboardInterrupt("Cancelled")
                        all_data.extend(pth.read_bytes())
                    
                    self._worker_q.put((PROG_SET, 20))
                    
                    # Compress using Python LZSS
                    def progress_callback(frac: float):
                        if self._cancel_evt.is_set():
                            raise KeyboardInterrupt("Cancelled")
                        self._worker_q.put((PROG_SET, int(20 + frac * 70)))
                    
                    compressed = lzss_compress_data(bytes(all_data), on_progress=progress_callback)
                    
                    self._worker_q.put((PROG_SET, 90))
                    
                    # Write compressed data
                    if crc32_acc is not None:
                        crc32_acc = crc32_bytes(compressed, crc32_acc)
                    fh.write(compressed)
                    
                    self._worker_q.put((PROG_SET, 95))
                    
                else:
                    # No compression - write raw
                    self._worker_q.put((STATUS_SET, "Writing payload (no compression)…"))
                    written = 0
                    total_len = sum(pth.stat().st_size for (pth, _a, _l) in pack_items)
                    
                    for (pth, _addr, _len) in pack_items:
                        if self._cancel_evt.is_set():
                            raise KeyboardInterrupt("Cancelled")
                        chunk = pth.read_bytes()
                        if crc32_acc is not None:
                            crc32_acc = crc32_bytes(chunk, crc32_acc)
                        fh.write(chunk)
                        written += len(chunk)
                        if total_len:
                            frac = min(1.0, written / max(1, total_len))
                            self._worker_q.put((PROG_SET, int(10 + frac * 85)))

                if patch_after and patch_offset is not None:
                    final_crc = crc32_acc & 0xFFFFFFFF if crc32_acc is not None else 0
                    hex8 = f"{final_crc:08X}".encode("ascii")
                    fh.seek(patch_offset, 0)
                    fh.write(hex8)

            if self._cancel_evt.is_set():
                try:
                    out_path.unlink(missing_ok=True)
                except Exception:
                    pass
                self._worker_q.put((ENABLE_UI, None))
                self._worker_q.put((STATUS_SET, "Cancelled"))
                return

            msg = f"VBF written:\n{out_path}\nSize: {out_path.stat().st_size:,} bytes"
            if use_lzss:
                msg += f"\n\nCompressed using Python LZSS"
            self._worker_q.put((DONE_OK, msg))
            self._worker_q.put((ENABLE_UI, None))

        except KeyboardInterrupt:
            try:
                out_path.unlink(missing_ok=True)
            except Exception:
                pass
            self._worker_q.put((ENABLE_UI, None))
            self._worker_q.put((STATUS_SET, "Cancelled"))
        except Exception as e:
            import traceback
            tb = traceback.format_exc()
            self._worker_q.put((ENABLE_UI, None))
            self._worker_q.put((DONE_ERR, f"{type(e).__name__}: {e}\n\n{tb}"))

# ---- main ----
if __name__ == "__main__":
    app = VBFGui()
    app.mainloop()
