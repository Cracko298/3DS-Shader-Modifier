from __future__ import annotations

import csv
import json
import math
import os
import re
import shutil
import struct
import tkinter as tk
from dataclasses import dataclass, field
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk
from typing import Any, Dict, Iterable, List, Optional, Tuple

from .constants import *
from .utils import *
from .pica import *
from .assembler import *
from .parser import *
from .renderer import *

class App(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title(APP_TITLE)
        self._configure_initial_window()
        self.parser = SHBINParser()
        self.selected_constant: Optional[Tuple[int, int]] = None
        self.selected_instruction: Optional[int] = None
        self.selected_opdesc: Optional[int] = None
        self.item_ranges: Dict[str, Tuple[int, int]] = {}
        self.filter_var = tk.StringVar()
        self.edit_vars = [tk.StringVar() for _ in range(4)]
        self.raw_vars = [tk.StringVar() for _ in range(4)]
        self.instr_mnemonic_var = tk.StringVar()
        self.instr_raw_var = tk.StringVar()
        self.instr_asm_var = tk.StringVar()
        self.instr_desc_var = tk.StringVar()
        self.instr_dst_var = tk.StringVar()
        self.instr_src1_var = tk.StringVar()
        self.instr_src2_var = tk.StringVar()
        self.instr_src3_var = tk.StringVar()
        self.instr_idx_var = tk.StringVar()
        self.instr_num_var = tk.StringVar()
        self.instr_target_var = tk.StringVar()
        self.instr_condop_var = tk.StringVar()
        self.instr_boolint_var = tk.StringVar()
        self.instr_refx_var = tk.StringVar()
        self.instr_refy_var = tk.StringVar()
        self.instr_cmpx_var = tk.StringVar()
        self.instr_cmpy_var = tk.StringVar()
        self.opdesc_raw_var = tk.StringVar()
        self.opdesc_flags_var = tk.StringVar()
        self.opdesc_mask_var = tk.StringVar()
        self.opdesc_src1_swizzle_var = tk.StringVar()
        self.opdesc_src2_swizzle_var = tk.StringVar()
        self.opdesc_src3_swizzle_var = tk.StringVar()
        self.opdesc_src1_neg_var = tk.BooleanVar(value=False)
        self.opdesc_src2_neg_var = tk.BooleanVar(value=False)
        self.opdesc_src3_neg_var = tk.BooleanVar(value=False)
        self.cfg_dvle_var = tk.StringVar(value="0")
        self.analysis_dvle_var = tk.StringVar(value="0")
        self.symbol_dvle_var = tk.StringVar(value="global")
        self.symbol_register_var = tk.StringVar(value="c17")
        self.symbol_name_var = tk.StringVar(value="CHUNK_ORIGIN_AND_SCALE")
        self.instr_register_widgets: Dict[str, ttk.Combobox] = {}
        self.symbol_tree: Optional[ttk.Treeview] = None
        self.symbol_register_combo: Optional[ttk.Combobox] = None
        self.symbol_scope_combo: Optional[ttk.Combobox] = None
        self._build_ui()

    def _configure_initial_window(self) -> None:
        try:
            sw, sh = int(self.winfo_screenwidth()), int(self.winfo_screenheight())
        except Exception:
            sw, sh = 1540, 820
        width = min(1800, max(1920, int(sw * 0.92)))
        height = min(900, max(1280, int(sh * 0.86)))
        x = max(0, (sw - width) // 2)
        y = max(0, (sh - height) // 2)
        self.geometry(f"{width}x{height}+{x}+{y}")
        self.minsize(min(980, max(760, sw - 120)), min(600, max(520, sh - 140)))

    def _build_ui(self) -> None:
        self._build_toolbar()
        self._build_body()
        self._build_statusbar()
        self._set_status("Open a .shbin / DVLB file to begin.")

    def _build_toolbar(self) -> None:
        toolbar_outer = ttk.Frame(self, padding=(4, 4))
        toolbar_outer.pack(side=tk.TOP, fill=tk.X)
        toolbar_outer.columnconfigure(0, weight=1)

        self.toolbar_canvas = tk.Canvas(toolbar_outer, highlightthickness=0, height=34)
        self.toolbar_canvas.grid(row=0, column=0, sticky="ew")
        self.toolbar_scroll = ttk.Scrollbar(toolbar_outer, orient=tk.HORIZONTAL, command=self.toolbar_canvas.xview)
        self.toolbar_scroll.grid(row=1, column=0, sticky="ew")
        self.toolbar_canvas.configure(xscrollcommand=self.toolbar_scroll.set)
        toolbar = ttk.Frame(self.toolbar_canvas)
        self.toolbar_window = self.toolbar_canvas.create_window((0, 0), window=toolbar, anchor="nw")

        def _sync_toolbar(_event: Optional[tk.Event] = None) -> None:
            try:
                self.toolbar_canvas.configure(scrollregion=self.toolbar_canvas.bbox("all"))
                self.toolbar_canvas.configure(height=max(30, toolbar.winfo_reqheight()))
            except Exception:
                pass

        toolbar.bind("<Configure>", _sync_toolbar)
        self.toolbar_canvas.bind("<Configure>", _sync_toolbar)

        ttk.Button(toolbar, text="Open .shbin", command=self.open_file).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Assembly -> Shader", command=self.compile_vsh_to_shbin).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Save", command=self.save_file).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Save As", command=self.save_file_as).pack(side=tk.LEFT, padx=2)
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=8)
        ttk.Button(toolbar, text="Export JSON", command=self.export_json).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Import JSON Values", command=self.import_json_values).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Export Constants CSV", command=self.export_csv).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Export Commented Disasm", command=self.export_disassembly).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Export ASM/VSH", command=self.export_clean_source).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Export Commented ASM", command=self.export_full_asm).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Import Commented ASM", command=self.import_full_asm).pack(side=tk.LEFT, padx=2)
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=8)

        analysis_tools = ttk.Frame(toolbar)
        analysis_tools.pack(side=tk.LEFT, padx=2)

                                   
        ttk.Button(analysis_tools, text="Symbols", command=self.show_symbol_tools).grid(row=0, column=0, padx=2, pady=(0, 2), sticky="ew")
        ttk.Button(analysis_tools, text="Export Symbol Map", command=self.export_symbol_map).grid(row=0, column=1, padx=2, pady=(0, 2), sticky="ew")
        ttk.Button(analysis_tools, text="Import Symbol Map", command=self.import_symbol_map).grid(row=0, column=2, padx=2, pady=(0, 2), sticky="ew")

                                                                                        
        ttk.Button(analysis_tools, text="Validate", command=self.show_validation).grid(row=1, column=0, padx=2, pady=(2, 0), sticky="ew")
        ttk.Button(analysis_tools, text="CFG", command=self.refresh_cfg).grid(row=1, column=1, padx=2, pady=(2, 0), sticky="ew")
        ttk.Button(analysis_tools, text="Analyze Regs", command=self.show_register_lifetimes).grid(row=1, column=2, padx=2, pady=(2, 0), sticky="ew")

        for col in range(3):
            analysis_tools.columnconfigure(col, weight=1, uniform="analysis_tools")

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=8)

    def _build_body(self) -> None:
        paned = ttk.Panedwindow(self, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True)
        self.main_paned = paned
        self._pane_resize_job: Optional[str] = None
        self._pane_first_fit = True

        left = ttk.Frame(paned, padding=4)
        self.left_pane = left
        paned.add(left, weight=1)
        filter_bar = ttk.Frame(left)
        filter_bar.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 4))
        filter_bar.columnconfigure(1, weight=1)
        ttk.Label(filter_bar, text="Filter:").grid(row=0, column=0, sticky="w", padx=(0, 4))
        filter_entry = ttk.Entry(filter_bar, textvariable=self.filter_var)
        filter_entry.grid(row=0, column=1, sticky="ew", padx=(0, 4))
        filter_entry.bind("<KeyRelease>", lambda _e: self.refresh_tree())
        ttk.Button(filter_bar, text="Clear", command=lambda: (self.filter_var.set(""), self.refresh_tree())).grid(row=0, column=2, sticky="e")

        self.tree = ttk.Treeview(left, columns=("Kind", "Info"), show="tree headings")
        self.tree.heading("#0", text="Section / Entry")
        self.tree.heading("Kind", text="Kind")
        self.tree.heading("Info", text="Info")
        self.tree.column("#0", width=420, minwidth=80, stretch=True)
        self.tree.column("Kind", width=70, minwidth=40, anchor=tk.W, stretch=False)
        self.tree.column("Info", width=90, minwidth=40, anchor=tk.W, stretch=False)
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        self.tree.bind("<Configure>", self._fit_tree_columns)

        yscroll = ttk.Scrollbar(left, orient=tk.VERTICAL, command=self.tree.yview)
        xscroll = ttk.Scrollbar(left, orient=tk.HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        self.tree.grid(row=1, column=0, sticky="nsew")
        yscroll.grid(row=1, column=1, sticky="ns")
        xscroll.grid(row=2, column=0, sticky="ew")
        left.rowconfigure(1, weight=1)
        left.columnconfigure(0, weight=1)

        right = ttk.Frame(paned, padding=4)
        self.center_pane = right
        paned.add(right, weight=3)

        self.notebook = ttk.Notebook(right)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        self.details_text = self._make_text_tab("Details")
        self.edit_frame = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(self.edit_frame, text="Edit Constant")
        self.instruction_frame = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(self.instruction_frame, text="Edit Instruction")
        self.opdesc_frame = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(self.opdesc_frame, text="Edit Opdesc")
        self.hex_text = self._make_text_tab("Hex View")
        self.raw_text = self._make_text_tab("Raw Tables")
        self.analysis_text = self._make_text_tab("Register Analysis")
        self.symbol_frame = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(self.symbol_frame, text="Symbol Map")
        self.cfg_frame = ttk.Frame(self.notebook, padding=4)
        self.notebook.add(self.cfg_frame, text="Control Flow")
        self._build_edit_tab()
        self._build_instruction_tab()
        self._build_opdesc_tab()
        self._build_symbol_tab()
        self._build_cfg_tab()

        self.preview = ShaderPreview3D(paned)
        paned.add(self.preview, weight=2)
        for child, minsize in ((left, 260), (right, 420), (self.preview, 220)):
            try:
                paned.paneconfigure(child, minsize=minsize)
            except Exception:
                pass
        paned.bind("<Configure>", self._queue_fit_main_panes)
        self.after_idle(lambda: self._fit_main_panes(force=True))

    def _queue_fit_main_panes(self, _event: Optional[tk.Event] = None) -> None:
        try:
            if self._pane_resize_job:
                self.after_cancel(self._pane_resize_job)
        except Exception:
            pass
        self._pane_resize_job = self.after(80, self._fit_main_panes)

    def _fit_main_panes(self, force: bool = False) -> None:
        paned = getattr(self, "main_paned", None)
        if paned is None:
            return
        try:
            total = int(paned.winfo_width())
        except Exception:
            return
        if total < 700:
            return

        target_left = max(340, min(520, int(total * 0.30)))
        target_preview = max(280, min(460, int(total * 0.24)))
        min_center = 500
        if target_left + target_preview + min_center > total:
            target_left = max(300, min(target_left, int(total * 0.28)))
            target_preview = max(240, min(target_preview, total - target_left - min_center))
        target_preview = max(230, target_preview)
        second_sash = max(target_left + min_center, total - target_preview)

        try:
            cur_left = int(paned.sashpos(0))
            cur_second = int(paned.sashpos(1))
            cur_preview = total - cur_second
            cur_center = cur_second - cur_left
        except Exception:
            cur_preview = cur_center = 0

        needs_fit = bool(force or getattr(self, "_pane_first_fit", False) or cur_preview < 230 or cur_center < 460)
        if not needs_fit:
            return
        try:
            paned.sashpos(0, target_left)
            paned.sashpos(1, second_sash)
            self._pane_first_fit = False
        except Exception:
            pass

    def _fit_tree_columns(self, _event: Optional[tk.Event] = None) -> None:
        tree = getattr(self, "tree", None)
        if tree is None:
            return
        try:
            width = int(tree.winfo_width())
        except Exception:
            return
        if width <= 80:
            return

        usable = max(80, width - 26)
        kind_w = max(48, min(78, int(usable * 0.14)))
        info_w = max(52, min(112, int(usable * 0.18)))
        section_w = max(120, usable - kind_w - info_w)
        try:
            tree.column("#0", width=section_w, minwidth=60, stretch=True)
            tree.column("Kind", width=kind_w, minwidth=40, stretch=False)
            tree.column("Info", width=info_w, minwidth=40, stretch=False)
        except Exception:
            pass

    def _make_text_tab(self, title: str) -> tk.Text:
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text=title)
        text = tk.Text(frame, wrap=tk.NONE, undo=False, font=("Consolas", 10))
        text.configure(state=tk.DISABLED)
        yscroll = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=text.yview)
        xscroll = ttk.Scrollbar(frame, orient=tk.HORIZONTAL, command=text.xview)
        text.configure(yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        text.grid(row=0, column=0, sticky="nsew")
        yscroll.grid(row=0, column=1, sticky="ns")
        xscroll.grid(row=1, column=0, sticky="ew")
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)
        return text

    def _build_edit_tab(self) -> None:
        self.edit_name_label = ttk.Label(self.edit_frame, text="Select a constant to edit.", font=("Segoe UI", 10, "bold"))
        self.edit_name_label.grid(row=0, column=0, columnspan=4, sticky="w", pady=(0, 10))

        labels = ["X / R", "Y / G", "Z / B", "W / A"]
        for i, label in enumerate(labels):
            ttk.Label(self.edit_frame, text=label, width=8).grid(row=i + 1, column=0, sticky="w", pady=3)
            ttk.Entry(self.edit_frame, textvariable=self.edit_vars[i], width=22).grid(row=i + 1, column=1, sticky="ew", padx=(4, 12), pady=3)
            ttk.Label(self.edit_frame, text="raw").grid(row=i + 1, column=2, sticky="e", pady=3)
            ttk.Entry(self.edit_frame, textvariable=self.raw_vars[i], width=16).grid(row=i + 1, column=3, sticky="ew", padx=(4, 0), pady=3)

        btns = ttk.Frame(self.edit_frame)
        btns.grid(row=6, column=0, columnspan=4, sticky="ew", pady=(14, 0))
        ttk.Button(btns, text="Apply Display Values", command=self.apply_display_values).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Apply Raw Values", command=self.apply_raw_values).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Copy Constant JSON", command=self.copy_constant_json).pack(side=tk.LEFT)

        help_text = (
            "Float uniforms are stored as PICA 24-bit floats inside 32-bit fields.\n"
            "For Float24 constants, edit display values as normal floats or raw as 0x00RRGGBB-style 24-bit values.\n"
            "For Bool constants, only X / raw0 is used. Int constants use byte values 0..255."
        )
        ttk.Label(self.edit_frame, text=help_text, foreground="#555", wraplength=520, justify=tk.LEFT).grid(
            row=7, column=0, columnspan=4, sticky="w", pady=(16, 0)
        )
        self.edit_frame.columnconfigure(1, weight=1)
        self.edit_frame.columnconfigure(3, weight=1)

    def _build_instruction_tab(self) -> None:
        header = ttk.Label(self.instruction_frame, text="Select a decoded instruction to edit.", font=("Segoe UI", 10, "bold"))
        header.grid(row=0, column=0, columnspan=6, sticky="w", pady=(0, 8))
        self.instr_header_label = header

        ttk.Label(self.instruction_frame, text="ASM line").grid(row=1, column=0, sticky="w", pady=3)
        asm_entry = ttk.Entry(self.instruction_frame, textvariable=self.instr_asm_var)
        asm_entry.grid(row=1, column=1, columnspan=4, sticky="ew", padx=(4, 8), pady=3)
        ttk.Button(self.instruction_frame, text="Apply ASM", command=self.apply_instruction_asm).grid(row=1, column=5, sticky="ew", pady=3)

        ttk.Label(self.instruction_frame, text="Raw word").grid(row=2, column=0, sticky="w", pady=3)
        ttk.Entry(self.instruction_frame, textvariable=self.instr_raw_var, width=18).grid(row=2, column=1, sticky="ew", padx=(4, 8), pady=3)
        ttk.Button(self.instruction_frame, text="Apply Raw", command=self.apply_instruction_raw).grid(row=2, column=2, sticky="ew", pady=3)
        ttk.Label(self.instruction_frame, text="Mnemonic").grid(row=2, column=3, sticky="e", padx=(16, 4), pady=3)
        values = sorted(set(MNEMONIC_TO_OPCODE.keys()) - {"EXP", "LOG", "LIT"})
        self.instr_mnemonic_combo = ttk.Combobox(self.instruction_frame, textvariable=self.instr_mnemonic_var, values=values, width=12)
        self.instr_mnemonic_combo.grid(row=2, column=4, sticky="ew", padx=(4, 8), pady=3)
        self.instr_mnemonic_combo.bind("<<ComboboxSelected>>", lambda _e: self._refresh_instruction_register_choices(None))
        self.instr_mnemonic_combo.bind("<KeyRelease>", lambda _e: self.after_idle(lambda: self._refresh_instruction_register_choices(None)))
        ttk.Button(self.instruction_frame, text="Apply Fields", command=self.apply_instruction_fields).grid(row=2, column=5, sticky="ew", pady=3)

        fields = [
            ("Desc ID", self.instr_desc_var), ("DST", self.instr_dst_var), ("SRC1", self.instr_src1_var),
            ("SRC2", self.instr_src2_var), ("SRC3", self.instr_src3_var), ("IDX", self.instr_idx_var),
            ("NUM", self.instr_num_var), ("Target", self.instr_target_var), ("CondOp", self.instr_condop_var),
            ("Bool/Int ID", self.instr_boolint_var), ("RefX", self.instr_refx_var), ("RefY", self.instr_refy_var),
            ("CmpX", self.instr_cmpx_var), ("CmpY", self.instr_cmpy_var),
        ]
        row = 3
        self.instr_register_widgets = {}
        for i, (label, var) in enumerate(fields):
            r = row + i // 2
            c = 0 if i % 2 == 0 else 3
            ttk.Label(self.instruction_frame, text=label).grid(row=r, column=c, sticky="w", pady=3)
            if label in {"DST", "SRC1", "SRC2", "SRC3", "Bool/Int ID", "CondOp", "CmpX", "CmpY"}:
                combo = ttk.Combobox(self.instruction_frame, textvariable=var, width=24)
                if label == "CondOp":
                    combo.configure(values=[CONDOP_NAMES[i] for i in sorted(CONDOP_NAMES)])
                elif label in {"CmpX", "CmpY"}:
                    combo.configure(values=[CMP_OP_NAMES[i] for i in sorted(CMP_OP_NAMES)])
                combo.grid(row=r, column=c + 1, columnspan=2, sticky="ew", padx=(4, 10), pady=3)
                self.instr_register_widgets[label] = combo
            else:
                ttk.Entry(self.instruction_frame, textvariable=var, width=18).grid(row=r, column=c + 1, columnspan=2, sticky="ew", padx=(4, 10), pady=3)

        bottom_row = row + (len(fields) + 1) // 2
        instr_btns = ttk.Frame(self.instruction_frame)
        instr_btns.grid(row=bottom_row, column=0, columnspan=6, sticky="ew", pady=(10, 0))
        for i, (text, command) in enumerate([
            ("Insert NOP Before", self.insert_nop_before_selected),
            ("Delete / Shift Up", self.delete_selected_instruction),
            ("Add ASM Near DVLE End", self.add_asm_instruction_to_active_dvle),
        ]):
            ttk.Button(instr_btns, text=text, command=command).grid(row=0, column=i, sticky="ew", padx=(0 if i == 0 else 4, 0))
            instr_btns.columnconfigure(i, weight=1)

        help_text = (
            "ASM patching supports arithmetic forms like: add r0.xy, v0.xyzw, c0.xyzw  |  "
            "mul r1, r0, c5  |  dp3 o0.xyz, r0, c2  |  mad r2, r0, c1, r1.\n"
            "Flow-control can be edited directly in the ASM line now. Unused dropdowns are disabled per mnemonic. "
            "Register fields accept native names, plain symbols, or dropdown values like CHUNK_ORIGIN_AND_SCALE (c17)."
        )
        self.instr_help_label = ttk.Label(self.instruction_frame, text=help_text, foreground="#555", wraplength=760, justify=tk.LEFT)
        self.instr_help_label.grid(row=bottom_row + 1, column=0, columnspan=6, sticky="w", pady=(16, 0))
        self.instruction_frame.bind("<Configure>", self._fit_instruction_help_text)

        for col, weight in enumerate((0, 1, 1, 0, 1, 1)):
            self.instruction_frame.columnconfigure(col, weight=weight)

    def _fit_instruction_help_text(self, event: Optional[tk.Event] = None) -> None:
        try:
            width = int(event.width if event is not None else self.instruction_frame.winfo_width())
            self.instr_help_label.configure(wraplength=max(360, width - 32))
        except Exception:
            pass

    def _build_opdesc_tab(self) -> None:
        self.opdesc_header_label = ttk.Label(self.opdesc_frame, text="Select an operand descriptor to edit.", font=("Segoe UI", 10, "bold"))
        self.opdesc_header_label.grid(row=0, column=0, columnspan=5, sticky="w", pady=(0, 8))

        ttk.Label(self.opdesc_frame, text="Raw desc").grid(row=1, column=0, sticky="w", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_raw_var, width=18).grid(row=1, column=1, sticky="ew", padx=(4, 8), pady=3)
        ttk.Label(self.opdesc_frame, text="Flags").grid(row=1, column=2, sticky="e", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_flags_var, width=18).grid(row=1, column=3, sticky="ew", padx=(4, 8), pady=3)
        ttk.Button(self.opdesc_frame, text="Apply Raw", command=self.apply_opdesc_raw).grid(row=1, column=4, sticky="ew", pady=3)

        ttk.Label(self.opdesc_frame, text="Dest mask").grid(row=2, column=0, sticky="w", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_mask_var, width=12).grid(row=2, column=1, sticky="ew", padx=(4, 8), pady=3)
        ttk.Button(self.opdesc_frame, text="Apply Decoded", command=self.apply_opdesc_decoded).grid(row=2, column=4, sticky="ew", pady=3)

        ttk.Checkbutton(self.opdesc_frame, text="Neg SRC1", variable=self.opdesc_src1_neg_var).grid(row=3, column=0, sticky="w", pady=3)
        ttk.Label(self.opdesc_frame, text="SRC1 swizzle").grid(row=3, column=1, sticky="e", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_src1_swizzle_var, width=12).grid(row=3, column=2, sticky="ew", padx=(4, 8), pady=3)

        ttk.Checkbutton(self.opdesc_frame, text="Neg SRC2", variable=self.opdesc_src2_neg_var).grid(row=4, column=0, sticky="w", pady=3)
        ttk.Label(self.opdesc_frame, text="SRC2 swizzle").grid(row=4, column=1, sticky="e", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_src2_swizzle_var, width=12).grid(row=4, column=2, sticky="ew", padx=(4, 8), pady=3)

        ttk.Checkbutton(self.opdesc_frame, text="Neg SRC3", variable=self.opdesc_src3_neg_var).grid(row=5, column=0, sticky="w", pady=3)
        ttk.Label(self.opdesc_frame, text="SRC3 swizzle").grid(row=5, column=1, sticky="e", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_src3_swizzle_var, width=12).grid(row=5, column=2, sticky="ew", padx=(4, 8), pady=3)

        help_text = (
            "Opdescs control write masks, source swizzles, and source negation. A lot of ADD/DP3/MUL-style edits need both the opcode word and the referenced opdesc changed.\n"
            "Mask uses xyzw. Swizzles use xyzw/xxxx/yxzw/etc. The flags word is preserved unless you change it manually."
        )
        ttk.Label(self.opdesc_frame, text=help_text, foreground="#555", wraplength=720, justify=tk.LEFT).grid(
            row=7, column=0, columnspan=5, sticky="w", pady=(16, 0)
        )
        for col in range(5):
            self.opdesc_frame.columnconfigure(col, weight=1)


    def _build_symbol_tab(self) -> None:
        ttk.Label(self.symbol_frame, text="Register Symbol Table Editor", font=("Segoe UI", 10, "bold")).grid(row=0, column=0, columnspan=5, sticky="w", pady=(0, 8))

        ttk.Label(self.symbol_frame, text="Scope/DVLE").grid(row=1, column=0, sticky="w", pady=3)
        self.symbol_scope_combo = ttk.Combobox(self.symbol_frame, textvariable=self.symbol_dvle_var, width=12, values=["global"])
        self.symbol_scope_combo.grid(row=1, column=1, sticky="ew", padx=(4, 8), pady=3)
        ttk.Label(self.symbol_frame, text="Register").grid(row=1, column=2, sticky="w", pady=3)
        self.symbol_register_combo = ttk.Combobox(self.symbol_frame, textvariable=self.symbol_register_var, width=24)
        self.symbol_register_combo.grid(row=1, column=3, sticky="ew", padx=(4, 0), pady=3)

        ttk.Label(self.symbol_frame, text="Symbol name").grid(row=2, column=0, sticky="w", pady=3)
        ttk.Entry(self.symbol_frame, textvariable=self.symbol_name_var).grid(row=2, column=1, columnspan=3, sticky="ew", padx=(4, 0), pady=3)
        ttk.Button(self.symbol_frame, text="Load Selected", command=self.load_selected_symbol_row).grid(row=2, column=4, sticky="ew", padx=(8, 0), pady=3)

        btns = ttk.Frame(self.symbol_frame)
        btns.grid(row=3, column=0, columnspan=5, sticky="ew", pady=(8, 8))
        ttk.Button(btns, text="Apply / Update Alias", command=self.apply_register_alias).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Delete Alias", command=self.delete_register_alias).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Export Symbol Map", command=self.export_symbol_map).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Import Symbol Map", command=self.import_symbol_map).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Refresh", command=self.show_symbol_tools).pack(side=tk.LEFT)

        self.symbol_tree = ttk.Treeview(self.symbol_frame, columns=("Scope", "Register", "Symbol", "Source"), show="headings", height=10)
        for col, width in [("Scope", 105), ("Register", 90), ("Symbol", 300), ("Source", 185)]:
            self.symbol_tree.heading(col, text=col)
            self.symbol_tree.column(col, width=width, anchor=tk.W)
        self.symbol_tree.grid(row=4, column=0, columnspan=4, sticky="nsew")
        self.symbol_tree.bind("<<TreeviewSelect>>", self.on_symbol_table_select)
        sy = ttk.Scrollbar(self.symbol_frame, orient=tk.VERTICAL, command=self.symbol_tree.yview)
        sy.grid(row=4, column=4, sticky="ns")
        self.symbol_tree.configure(yscrollcommand=sy.set)

        self.symbol_text = tk.Text(self.symbol_frame, wrap=tk.NONE, font=("Consolas", 9), height=7)
        self.symbol_text.grid(row=5, column=0, columnspan=4, sticky="nsew", pady=(8, 0))
        yscroll = ttk.Scrollbar(self.symbol_frame, orient=tk.VERTICAL, command=self.symbol_text.yview)
        yscroll.grid(row=5, column=4, sticky="ns", pady=(8, 0))
        self.symbol_text.configure(yscrollcommand=yscroll.set)

        help_text = (
            "This editor creates register aliases used by disassembly, direct ASM editing, field dropdowns, full ASM import/export, and reports. "
            "It does not create new hardware registers; it maps names onto existing PICA registers like c17, v0, o2, r3, b0, or i0."
        )
        ttk.Label(self.symbol_frame, text=help_text, foreground="#555", wraplength=860, justify=tk.LEFT).grid(row=6, column=0, columnspan=5, sticky="w", pady=(10, 0))
        self.symbol_frame.columnconfigure(1, weight=1)
        self.symbol_frame.columnconfigure(3, weight=2)
        self.symbol_frame.rowconfigure(4, weight=2)
        self.symbol_frame.rowconfigure(5, weight=1)

    def _build_cfg_tab(self) -> None:
        top = ttk.Frame(self.cfg_frame)
        top.grid(row=0, column=0, sticky="ew", pady=(0, 4))
        ttk.Label(top, text="DVLE:").pack(side=tk.LEFT)
        ttk.Entry(top, textvariable=self.cfg_dvle_var, width=6).pack(side=tk.LEFT, padx=(4, 8))
        ttk.Button(top, text="Refresh graph", command=self.refresh_cfg).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(top, text="Show register lifetimes", command=self.show_register_lifetimes).pack(side=tk.LEFT)
        self.cfg_canvas = tk.Canvas(self.cfg_frame, bg="#10141b", highlightthickness=1, highlightbackground="#2b3240")
        self.cfg_canvas.grid(row=1, column=0, sticky="nsew")
        self.cfg_frame.rowconfigure(1, weight=1)
        self.cfg_frame.columnconfigure(0, weight=1)
        self.cfg_canvas.bind("<Configure>", lambda _e: self.refresh_cfg(redraw_only=True))

    def _build_statusbar(self) -> None:
        self.status_var = tk.StringVar()
        status = ttk.Label(self, textvariable=self.status_var, anchor=tk.W, padding=(4, 2), relief=tk.SUNKEN)
        status.pack(side=tk.BOTTOM, fill=tk.X)

    def _set_status(self, text: str) -> None:
        self.status_var.set(text)

    def _set_text(self, widget: tk.Text, text: str) -> None:
        widget.configure(state=tk.NORMAL)
        widget.delete("1.0", tk.END)
        widget.insert(tk.END, text)
        widget.configure(state=tk.DISABLED)

    def open_file(self) -> None:
        path = filedialog.askopenfilename(filetypes=[("3DS Shader Binary", "*.shbin *.bcsdr *.bin"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.load(path)
        except Exception as exc:
            messagebox.showerror("Open failed", str(exc))
            return
        self.refresh_tree()
        self.refresh_symbol_table()
        self.show_overview()
        self.preview.set_shader(self.parser)
        self._set_status(f"Loaded {os.path.basename(path)} | {len(self.parser.data):,} bytes | {len(self.parser.dvles)} DVLE(s)")

    def compile_vsh_to_shbin(self) -> None:
        in_path = filedialog.askopenfilename(filetypes=[("Picasso Vertex Shader", "*.vsh *.pica *.asm *.txt"), ("All files", "*.*")])
        if not in_path:
            return
        default = Path(in_path).with_suffix(".shbin").name
        out_path = filedialog.asksaveasfilename(initialfile=default, defaultextension=".shbin", filetypes=[("3DS Shader Binary", "*.shbin"), ("All files", "*.*")])
        if not out_path:
            return
        try:
            compile_vsh_file_to_shbin(in_path, out_path, auto_nop=True)
            self.parser.load(out_path)
            self.refresh_tree()
            self.refresh_symbol_table()
            self.show_overview()
            self.preview.set_shader(self.parser)
            self._set_status(f"Compiled {os.path.basename(in_path)} -> {os.path.basename(out_path)} and loaded the SHBIN.")
        except Exception as exc:
            messagebox.showerror("VSH compile failed", str(exc))

    def save_file(self) -> None:
        if not self._require_loaded():
            return
        if not self.parser.filename:
            self.save_file_as()
            return
        try:
            self.parser.save(self.parser.filename, make_backup=True)
            self._set_status(f"Saved {os.path.basename(self.parser.filename)} and created/updated .bak backup.")
        except Exception as exc:
            messagebox.showerror("Save failed", str(exc))

    def save_file_as(self) -> None:
        if not self._require_loaded():
            return
        path = filedialog.asksaveasfilename(defaultextension=".shbin", filetypes=[("Shader Binary", "*.shbin"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.save(path, make_backup=True)
            self._set_status(f"Saved {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("Save As failed", str(exc))

    def export_json(self) -> None:
        if not self._require_loaded():
            return
        default = Path(self.parser.filename).with_suffix(".shader.json").name if self.parser.filename else "shader.json"
        path = filedialog.asksaveasfilename(initialfile=default, defaultextension=".json", filetypes=[("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.export_json(path)
            self._set_status(f"Exported JSON to {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("Export failed", str(exc))

    def import_json_values(self) -> None:
        if not self._require_loaded():
            return
        path = filedialog.askopenfilename(filetypes=[("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            updated = self.parser.import_constant_values_json(path)
            self.refresh_tree()
            self.show_overview()
            self._set_status(f"Imported JSON values: updated {updated} constant(s). Save to write them to disk.")
        except Exception as exc:
            messagebox.showerror("Import failed", str(exc))

    def export_csv(self) -> None:
        if not self._require_loaded():
            return
        default = Path(self.parser.filename).with_suffix(".constants.csv").name if self.parser.filename else "constants.csv"
        path = filedialog.asksaveasfilename(initialfile=default, defaultextension=".csv", filetypes=[("CSV", "*.csv"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.export_constants_csv(path)
            self._set_status(f"Exported constants CSV to {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("CSV export failed", str(exc))

    def export_disassembly(self) -> None:
        if not self._require_loaded():
            return
        default = Path(self.parser.filename).with_suffix(".pica.asm").name if self.parser.filename else "shader.pica.asm"
        path = filedialog.asksaveasfilename(initialfile=default, defaultextension=".asm", filetypes=[("Assembly text", "*.asm *.txt"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.export_disassembly(path)
            self._set_status(f"Exported decoded instruction listing to {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("Disassembly export failed", str(exc))


    def export_clean_source(self) -> None:
        if not self._require_loaded():
            return
        default = Path(self.parser.filename).with_suffix(".vsh").name if self.parser.filename else "shader.vsh"
        path = filedialog.asksaveasfilename(
            initialfile=default,
            defaultextension=".vsh",
            filetypes=[("Picasso source", "*.vsh"), ("Clean ASM source", "*.asm *.txt"), ("All files", "*.*")],
        )
        if not path:
            return
        try:
            self.parser.export_source_by_extension(path)
            mode = "VSH" if Path(path).suffix.lower() == ".vsh" else "ASM"
            self._set_status(f"Exported clean {mode} source to {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("Clean source export failed", str(exc))

    def export_full_asm(self) -> None:
        if not self._require_loaded():
            return
        default = Path(self.parser.filename).with_suffix(".full.pica.asm").name if self.parser.filename else "shader.full.pica.asm"
        path = filedialog.asksaveasfilename(initialfile=default, defaultextension=".asm", filetypes=[("Assembly text", "*.asm *.txt"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.export_full_asm(path)
            self._set_status(f"Exported reassemblable full ASM to {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("Full ASM export failed", str(exc))

    def import_full_asm(self) -> None:
        if not self._require_loaded():
            return
        path = filedialog.askopenfilename(filetypes=[("Assembly text", "*.asm *.txt"), ("All files", "*.*")])
        if not path:
            return
        try:
            updated = self.parser.import_full_asm(path)
            self.refresh_tree()
            self.show_overview()
            self.preview.set_shader(self.parser)
            self.refresh_cfg(redraw_only=True)
            self._set_status(f"Imported full ASM: updated {updated} instruction(s). Save to write them to disk.")
        except Exception as exc:
            messagebox.showerror("Full ASM import failed", str(exc))

    def _parse_symbol_scope(self, text: Optional[str] = None) -> Optional[int]:
        scope = (self.symbol_dvle_var.get() if text is None else str(text)).strip().lower()
        if scope in {"", "global", "all", "none"}:
            return None
        if scope.startswith("dvle:"):
            scope = scope.split(":", 1)[1]
        return int(scope, 0)

    def _active_dvle_for_instruction(self, inst_idx: Optional[int] = None) -> Optional[int]:
        if inst_idx is None:
            inst_idx = self.selected_instruction
        if inst_idx is None:
            return None
        for dvle in self.parser.dvles:
            if self.parser._instruction_in_dvle_range(int(inst_idx), dvle):
                return dvle.index
        try:
            dvle_idx = int(self.cfg_dvle_var.get().strip() or "0", 0)
            if 0 <= dvle_idx < len(self.parser.dvles):
                return dvle_idx
        except Exception:
            pass
        return 0 if self.parser.dvles else None

    def _labels_for_dvle(self, dvle_idx: Optional[int]) -> Dict[str, int]:
        if dvle_idx is None or not (0 <= int(dvle_idx) < len(self.parser.dvles)):
            return {}
        dvle = self.parser.dvles[int(dvle_idx)]
        labels: Dict[str, int] = {}
        for lab in dvle.labels:
            name = self.parser._label_display_name(lab)
            if name:
                labels[name] = lab.opcode_address
                labels[name.replace(" ", "_")] = lab.opcode_address
        return labels

    def _symbol_map_for_instruction(self, inst_idx: Optional[int] = None) -> Dict[str, str]:
        return self.parser.symbol_to_register_map(self._active_dvle_for_instruction(inst_idx))

    @staticmethod
    def _add_symbol_binding(symbol_map: Dict[str, str], symbol: str, register: str, *, prefer: bool = False) -> None:
        sym = str(symbol or "").strip()
        reg = native_register_from_display(register)
        if not sym or not reg:
            return

        def add_one(name: str) -> None:
            if not name:
                return
            if prefer:
                symbol_map[name] = reg
                symbol_map[name.replace(" ", "_")] = reg
            else:
                symbol_map.setdefault(name, reg)
                symbol_map.setdefault(name.replace(" ", "_"), reg)

        add_one(sym)
        stem, component_suffix = split_vector_component_suffix(sym)
        if component_suffix and stem and stem != sym:
            add_one(stem)

    def _symbol_map_for_asm_roundtrip(self, inst_idx: int, dvle_idx: Optional[int]) -> Dict[str, str]:
        merged: Dict[str, str] = {}
        if self.parser.dvlp and 0 <= int(inst_idx) < len(self.parser.dvlp.instructions):
            inst = self.parser.dvlp.instructions[int(inst_idx)]
            for ann in inst.fields.get("register_annotations", []) or []:
                self._add_symbol_binding(merged, ann.get("symbol", ""), ann.get("register", ""), prefer=True)
        for sym, reg in self.parser.symbol_to_register_map(dvle_idx).items():
            self._add_symbol_binding(merged, sym, reg, prefer=False)
        return merged

    def _resolve_register_field(self, text: str, kind: str = "src", inst_idx: Optional[int] = None) -> str:
        raw = str(text or "").strip()
        if not raw:
            return raw
        display = native_register_from_display(raw)
        if display != raw.lower():
            return display
        dvle_idx = self._active_dvle_for_instruction(inst_idx) if inst_idx is not None else None
        symbols = self._symbol_map_for_asm_roundtrip(inst_idx, dvle_idx) if inst_idx is not None else self._symbol_map_for_instruction()
        low_map = {str(k).lower(): v for k, v in symbols.items()}
        if raw in symbols:
            return symbols[raw]
        if raw.lower() in low_map:
            return low_map[raw.lower()]
        return raw

    def _display_register_field(self, register: str, dvle_idx: Optional[int]) -> str:
        return self.parser.register_display_name(register, dvle_idx)

    def _instruction_format_from_editor(self, inst_idx: Optional[int] = None) -> Tuple[Optional[int], str]:
        mnemonic = self.instr_mnemonic_var.get().strip().upper() if hasattr(self, "instr_mnemonic_var") else ""
        if mnemonic in MNEMONIC_TO_OPCODE:
            op = MNEMONIC_TO_OPCODE[mnemonic]
            return op, pica_instruction_format(op, is_word=False)
        if inst_idx is not None and self.parser.dvlp and 0 <= int(inst_idx) < len(self.parser.dvlp.instructions):
            inst = self.parser.dvlp.instructions[int(inst_idx)]
            return inst.opcode, inst.fmt
        return None, "unknown"

    def _used_instruction_dropdowns(self, opcode: Optional[int], fmt: str) -> set[str]:
        used: set[str] = set()
        if fmt in {"1", "1i"}:
            used.update({"DST", "SRC1", "SRC2"})
        elif fmt == "1u":
            used.update({"DST", "SRC1"})
        elif fmt == "1c":
            used.update({"SRC1", "SRC2", "CmpX", "CmpY"})
        elif fmt == "2":
                                                                                   
            if opcode in {0x23, 0x25, 0x28, 0x2C}:
                used.add("CondOp")
        elif fmt == "3":
                                                  
            used.add("Bool/Int ID")
        elif fmt in {"5", "5i"}:
            used.update({"DST", "SRC1", "SRC2", "SRC3"})
        return used

    def _refresh_instruction_register_choices(self, inst_idx: Optional[int] = None) -> None:
        if not hasattr(self, "instr_register_widgets"):
            return
        dvle_idx = self._active_dvle_for_instruction(inst_idx)
        opcode, fmt = self._instruction_format_from_editor(inst_idx)
        used_dropdowns = self._used_instruction_dropdowns(opcode, fmt)

        def src_slot_kind(label: str) -> str:
                                                                                                                   
            if fmt in {"1", "1u", "1c"}:
                return "src" if label == "SRC1" else "src5"
            if fmt == "1i":
                return "src5" if label == "SRC1" else "src"
            if fmt == "5":
                return "src" if label == "SRC2" else "src5"
            if fmt == "5i":
                return "src" if label == "SRC3" else "src5"
            return "src"

        for label, combo in self.instr_register_widgets.items():
            if label == "DST":
                combo.configure(values=self.parser.register_display_choices(dvle_idx, "dst"))
            elif label in {"SRC1", "SRC2", "SRC3"}:
                combo.configure(values=self.parser.register_display_choices(dvle_idx, src_slot_kind(label)))
            elif label == "Bool/Int ID":
                combo.configure(values=self.parser.register_display_choices(dvle_idx, "uniform"))
            elif label == "CondOp":
                combo.configure(values=[CONDOP_NAMES[i] for i in sorted(CONDOP_NAMES)])
            elif label in {"CmpX", "CmpY"}:
                combo.configure(values=[CMP_OP_NAMES[i] for i in sorted(CMP_OP_NAMES)])

            combo.configure(state="normal" if label in used_dropdowns else "disabled")


    def _refresh_symbol_editor_choices(self) -> None:
        if self.symbol_scope_combo is not None:
            scopes = ["global"] + [str(dvle.index) for dvle in self.parser.dvles]
            self.symbol_scope_combo.configure(values=scopes)
        if self.symbol_register_combo is not None:
            dvle_idx = self._parse_symbol_scope()
            choices = []
            choices.extend(self.parser.register_display_choices(dvle_idx, "src"))
            choices.extend(self.parser.register_display_choices(dvle_idx, "dst"))
            choices.extend(self.parser.register_display_choices(dvle_idx, "uniform"))
            seen = set()
            unique = []
            for choice in choices:
                key = native_register_from_display(choice)
                if key not in seen:
                    seen.add(key)
                    unique.append(choice)
            self.symbol_register_combo.configure(values=unique)

    def _detected_symbol_rows(self) -> List[Tuple[str, str, str, str]]:
        rows: List[Tuple[str, str, str, str]] = []
        for dvle in self.parser.dvles:
            scope = str(dvle.index)
            for inp in dvle.inputs:
                lo, hi = sorted((inp.start, inp.end))
                for reg_num in range(lo, hi + 1):
                    name = inp.name if lo == hi else f"{inp.name}[{reg_num - lo}]"
                    if name:
                        rows.append((scope, f"v{reg_num}", name, "Input Register Table"))
            for out in dvle.outputs:
                rows.append((scope, f"o{out.register_id}", OUTPUT_TYPES.get(out.output_type, f"output_{out.output_type}"), "Output Register Table"))
            for c in dvle.constants:
                if c.display_name and c.display_name != c.register_name:
                    rows.append((scope, c.register_name, c.display_name, "Constant Table"))
        return rows

    def refresh_symbol_table(self) -> None:
        if self.symbol_tree is None:
            return
        self.symbol_tree.delete(*self.symbol_tree.get_children())
        maps = self.parser._symbol_maps()
        for scope, regs in sorted(maps.items()):
            shown_scope = "global" if scope == "global" else scope.split(":", 1)[-1]
            for reg, sym in sorted(regs.items()):
                if not sym:
                    continue
                iid = f"alias:{shown_scope}:{reg}"
                self.symbol_tree.insert("", "end", iid=iid, values=(shown_scope, reg, sym, "User Alias"))
        for i, (scope, reg, sym, source) in enumerate(self._detected_symbol_rows()):
            iid = f"detected:{i}"
            self.symbol_tree.insert("", "end", iid=iid, values=(scope, reg, sym, source))
        self._refresh_symbol_editor_choices()

    def load_selected_symbol_row(self) -> None:
        if self.symbol_tree is None:
            return
        sel = self.symbol_tree.selection()
        if not sel:
            return
        vals = self.symbol_tree.item(sel[0], "values")
        if len(vals) >= 3:
            self.symbol_dvle_var.set(str(vals[0]))
            self.symbol_register_var.set(str(vals[1]))
            self.symbol_name_var.set(str(vals[2]))
            self._refresh_symbol_editor_choices()

    def on_symbol_table_select(self, _event: Any = None) -> None:
        self.load_selected_symbol_row()

    def delete_register_alias(self) -> None:
        if not self._require_loaded():
            return
        try:
            dvle_idx = self._parse_symbol_scope()
            self.parser.remove_register_alias(self.symbol_register_var.get(), dvle_idx)
            self.refresh_tree()
            self.show_symbol_tools()
            self.preview.set_shader(self.parser)
            self._set_status("Register alias deleted from the symbol map.")
        except Exception as exc:
            messagebox.showerror("Delete alias failed", str(exc))

    def export_symbol_map(self) -> None:
        if not self._require_loaded():
            return
        default = Path(self.parser.filename).with_suffix(".register_symbols.json").name if self.parser.filename else "register_symbols.json"
        path = filedialog.asksaveasfilename(initialfile=default, defaultextension=".json", filetypes=[("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.export_register_symbol_map(path)
            self.show_symbol_tools()
            self._set_status(f"Exported register symbol map to {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("Symbol map export failed", str(exc))

    def import_symbol_map(self) -> None:
        if not self._require_loaded():
            return
        path = filedialog.askopenfilename(filetypes=[("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            count = self.parser.import_register_symbol_map(path)
            self.refresh_tree()
            self.show_symbol_tools()
            self.preview.set_shader(self.parser)
            self._set_status(f"Imported {count} register symbol alias(es).")
        except Exception as exc:
            messagebox.showerror("Symbol map import failed", str(exc))

    def show_symbol_tools(self) -> None:
        if not self._require_loaded():
            return
        self.refresh_symbol_table()
        lines = ["Register Symbol Map", ""]
        maps = self.parser._symbol_maps()
        for scope, regs in maps.items():
            lines.append(f"[{scope}]")
            if regs:
                for reg, sym in sorted(regs.items()):
                    lines.append(f"  {reg:6} = {sym}")
            else:
                lines.append("  <empty>")
            lines.append("")
        lines.append("Detected register-backed symbols available to ASM/dropdowns:")
        for scope, reg, sym, source in self._detected_symbol_rows():
            lines.append(f"  DVLE {scope:>2}  {reg:<6} = {sym}  [{source}]")
        self.symbol_text.configure(state=tk.NORMAL)
        self.symbol_text.delete("1.0", tk.END)
        self.symbol_text.insert(tk.END, "\n".join(lines))
        self.symbol_text.configure(state=tk.DISABLED)
        self.notebook.select(self.symbol_frame)

    def apply_register_alias(self) -> None:
        if not self._require_loaded():
            return
        try:
            dvle_idx = self._parse_symbol_scope()
            self.parser.set_register_alias(self.symbol_register_var.get(), self.symbol_name_var.get(), dvle_idx)
            self.refresh_tree()
            self.show_symbol_tools()
            self._refresh_instruction_register_choices()
            self.preview.set_shader(self.parser)
            self._set_status("Register alias applied to the symbol map.")
        except Exception as exc:
            messagebox.showerror("Alias failed", str(exc))

    def show_register_lifetimes(self) -> None:
        if not self._require_loaded():
            return
        try:
            dvle_idx = int(self.analysis_dvle_var.get().strip() or self.cfg_dvle_var.get().strip() or "0", 0)
        except Exception:
            dvle_idx = 0
        self.analysis_dvle_var.set(str(dvle_idx))
        self._set_text(self.analysis_text, self.parser.register_lifetime_report(dvle_idx))
        self.notebook.select(self.analysis_text.master)

    def refresh_cfg(self, redraw_only: bool = False) -> None:
        if not hasattr(self, "cfg_canvas"):
            return
        self.cfg_canvas.delete("all")
        if not self.parser.loaded or not self.parser.dvlp:
            self.cfg_canvas.create_text(24, 24, anchor=tk.NW, text="Open a shader to view the control-flow graph.", fill="#d0d7e2", font=("Segoe UI", 11, "bold"))
            return
        try:
            dvle_idx = int(self.cfg_dvle_var.get().strip() or "0", 0)
        except Exception:
            dvle_idx = 0
            self.cfg_dvle_var.set("0")
        graph = self.parser.control_flow_graph(dvle_idx)
        nodes = graph.get("nodes", [])
        edges = graph.get("edges", [])
        w = max(600, int(self.cfg_canvas.winfo_width()))
        h = max(420, int(self.cfg_canvas.winfo_height()))
        self.cfg_canvas.create_rectangle(0, 0, w, h, fill="#10141b", outline="")
        if not nodes:
            self.cfg_canvas.create_text(24, 24, anchor=tk.NW, text="No graph nodes decoded.", fill="#d0d7e2")
            return
        node_w, node_h = 220, 54
        x_gap = max(40, (w - node_w) // 2)
        y_gap = 88
        positions: Dict[int, Tuple[int, int]] = {}
        for i, node in enumerate(nodes):
            x = x_gap + (40 if i % 2 else -40)
            y = 30 + i * y_gap
            positions[int(node["start"])] = (x, y)
        for edge in edges:
            src = int(edge.get("from", 0)); dst = int(edge.get("to", 0))
            if src not in positions:
                continue
            dst_start = dst if dst in positions else next((int(n["start"]) for n in nodes if int(n["start"]) >= dst), None)
            if dst_start is None or dst_start not in positions:
                continue
            x1, y1 = positions[src]
            x2, y2 = positions[dst_start]
            sx, sy = x1 + node_w // 2, y1 + node_h
            tx, ty = x2 + node_w // 2, y2
            color = "#6fb2ff" if edge.get("kind") != "fallthrough" else "#73808f"
            self.cfg_canvas.create_line(sx, sy, tx, ty, fill=color, arrow=tk.LAST, width=2, smooth=True)
            self.cfg_canvas.create_text((sx + tx) / 2 + 8, (sy + ty) / 2, text=str(edge.get("kind", "")), fill=color, anchor=tk.W, font=("Segoe UI", 8))
        for node in nodes:
            x, y = positions[int(node["start"])]
            label = f"{node.get('label')}\n{int(node['start']):04d}..{int(node['end']):04d}"
            self.cfg_canvas.create_rectangle(x, y, x + node_w, y + node_h, fill="#1b2533", outline="#86a8d8", width=2)
            self.cfg_canvas.create_text(x + 10, y + 8, anchor=tk.NW, text=label, fill="#eef5ff", font=("Consolas", 10, "bold"))
        if not redraw_only:
            self.notebook.select(self.cfg_frame)
        self._set_status(f"Control-flow graph refreshed for DVLE {graph.get('dvle', dvle_idx)}: {len(nodes)} block(s), {len(edges)} edge(s).")

    def show_validation(self) -> None:
        if not self._require_loaded():
            return
        self._set_text(self.details_text, self.parser.validation_report())
        self.notebook.select(0)

    def _require_loaded(self) -> bool:
        if not self.parser.loaded:
            messagebox.showinfo("No file loaded", "Open a .shbin file first.")
            return False
        return True

    def refresh_tree(self) -> None:
        self.tree.delete(*self.tree.get_children())
        self.item_ranges.clear()
        if not self.parser.loaded:
            return

        needle = self.filter_var.get().strip().lower()
        terms = [t for t in needle.split() if t]

        root = self.tree.insert("", "end", iid="dvlb", text="DVLB Header", values=("Header", f"{len(self.parser.dvles)} DVLE(s)"), open=True)
        self.item_ranges["dvlb"] = (0, min(0x40, len(self.parser.data)))

        if self.parser.dvlp:
            d = self.parser.dvlp
            dvlp_item = self.tree.insert("", "end", iid="dvlp", text="DVLP Program", values=("Program", f"{d.opcode_count} opcodes / {d.opdesc_count} opdescs"), open=True)
            self.item_ranges["dvlp"] = (d.offset, max(d.size, 0x28))
            self.tree.insert(dvlp_item, "end", iid="dvlp_header", text="Header", values=("Header", f"0x{d.offset:X}"))
            self.item_ranges["dvlp_header"] = (d.offset, 0x28)

            instr_parent = self.tree.insert(dvlp_item, "end", iid="dvlp_instructions", text="Decoded Instructions", values=("Code", f"{len(d.instructions)} instruction(s)"), open=True)
            self.item_ranges["dvlp_instructions"] = (d.offset + d.opcode_offset, d.opcode_count * 4)
            self.tree.insert(dvlp_item, "end", iid="dvlp_opcodes", text="Raw Opcode Table", values=("Table", f"{d.opcode_count} x 4 bytes"))
            self.item_ranges["dvlp_opcodes"] = (d.offset + d.opcode_offset, d.opcode_count * 4)
            current_block_parent = None
            current_block_name = ""
            current_block_hay = ""

            for inst in d.instructions:
                ann_disasm = inst.fields.get("annotated_disasm", inst.disasm)
                labels_here = ", ".join(x.get("name", "") for x in inst.fields.get("labels_here", []) if x.get("name"))

                if labels_here or current_block_parent is None:
                    current_block_name = labels_here or f"entry_{inst.index:04d}"
                    current_block_hay = f"{current_block_name} label block instruction group".lower()
                    block_id = f"inst_block:{inst.index}"
                    current_block_parent = self.tree.insert(
                        instr_parent,
                        "end",
                        iid=block_id,
                        text=current_block_name,
                        values=("Label" if labels_here else "Block", f"starts at instruction {inst.index}"),
                        open=True,
                    )
                    self.item_ranges[block_id] = (inst.offset, 4)

                hay = " ".join([inst.disasm, str(ann_disasm), labels_here, current_block_hay, inst.mnemonic, inst.fmt, f"0x{inst.word:08X}"]).lower()
                if terms and not all(term in hay for term in terms):
                    continue

                item_id = f"inst:{inst.index}"
                display_disasm = str(ann_disasm)
                self.tree.insert(
                    current_block_parent,
                    "end",
                    iid=item_id,
                    text=f"{inst.index:04d}: {display_disasm}",
                    values=(inst.fmt, f"0x{inst.word:08X}"),
                )
                self.item_ranges[item_id] = (inst.offset, 4)

            opdesc_parent = self.tree.insert(dvlp_item, "end", iid="dvlp_opdescs", text="Operand Descriptors", values=("Table", f"{d.opdesc_count} x 8 bytes"), open=True)
            self.item_ranges["dvlp_opdescs"] = (d.offset + d.opdesc_offset, d.opdesc_count * 8)
            for i, (desc, flags) in enumerate(d.opdescs):
                dec = pica_decode_opdesc(desc, flags)
                info = f"mask={dec['dest_mask']} s1={'-' if dec['src1_neg'] else ''}{dec['src1_swizzle']} s2={'-' if dec['src2_neg'] else ''}{dec['src2_swizzle']} s3={'-' if dec['src3_neg'] else ''}{dec['src3_swizzle']}"
                hay = f"opdesc {i} 0x{desc:08x} 0x{flags:08x} {info}".lower()
                if terms and not all(term in hay for term in terms):
                    continue
                item_id = f"opdesc:{i}"
                self.tree.insert(opdesc_parent, "end", iid=item_id, text=f"Opdesc {i:03d}", values=("Opdesc", info))
                self.item_ranges[item_id] = (d.offset + d.opdesc_offset + i * 8, 8)

            self.tree.insert(dvlp_item, "end", iid="dvlp_lines", text="Line Number Table", values=("Table", f"{d.line_count} x 8 bytes"))
            self.item_ranges["dvlp_lines"] = (d.offset + d.line_offset, d.line_count * 8)
            self.tree.insert(dvlp_item, "end", iid="dvlp_filenames", text="Source Filename Symbols", values=("Symbols", f"{len(d.filenames)} strings"))
            self.item_ranges["dvlp_filenames"] = (d.offset + d.filename_symbol_offset, d.filename_symbol_size)

        for dvle in self.parser.dvles:
            dvle_item = self.tree.insert("", "end", iid=f"dvle:{dvle.index}", text=f"DVLE {dvle.index} ({dvle.shader_type_name})", values=("Shader", f"entry {dvle.opcode_entry} end {dvle.opcode_end}"), open=True)
            self.item_ranges[f"dvle:{dvle.index}"] = (dvle.offset, max(dvle.size, 0x40))

            self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:header", text="Header", values=("Header", f"0x{dvle.offset:X}"))
            self.item_ranges[f"dvle:{dvle.index}:header"] = (dvle.offset, 0x40)

            const_parent = self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:constants", text="Constants", values=("Table", f"{len(dvle.constants)} entries"), open=True)
            self.item_ranges[f"dvle:{dvle.index}:constants"] = (dvle.offset + dvle.const_offset, dvle.const_count * 0x14)
            for c in dvle.constants:
                hay = " ".join([c.display_name, c.register_name, self.parser.register_alias(c.register_name, dvle.index), c.type_name, str(c.values_for_display)]).lower()
                if terms and not all(term in hay for term in terms):
                    continue
                preview = self._constant_preview(c)
                item_id = f"const:{dvle.index}:{c.index}"
                self.tree.insert(const_parent, "end", iid=item_id, text=c.display_name, values=(c.type_name, f"{c.register_name}  {preview}"))
                self.item_ranges[item_id] = (c.offset, 0x14)

            inputs_parent = self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:inputs", text="Input Register Table", values=("Table", f"{len(dvle.inputs)} entries"), open=True)
            self.item_ranges[f"dvle:{dvle.index}:inputs"] = (dvle.offset + dvle.input_offset, dvle.input_count * 8)
            for inp in dvle.inputs:
                hay = f"{inp.name} 0x{inp.start:02x} 0x{inp.end:02x} input register table".lower()
                if terms and not all(term in hay for term in terms):
                    continue
                item_id = f"input:{dvle.index}:{inp.index}"
                self.tree.insert(inputs_parent, "end", iid=item_id, text=inp.name or f"input_{inp.index}", values=("Input", f"regs 0x{inp.start:02X}..0x{inp.end:02X}"))
                self.item_ranges[item_id] = (inp.offset, 8)

            outputs_parent = self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:outputs", text="Output Register Table", values=("Table", f"{len(dvle.outputs)} entries"), open=True)
            self.item_ranges[f"dvle:{dvle.index}:outputs"] = (dvle.offset + dvle.output_offset, dvle.output_count * 8)
            for out in dvle.outputs:
                type_name = OUTPUT_TYPES.get(out.output_type, f"unknown_{out.output_type}")
                hay = f"{type_name} o{out.register_id} {component_mask(out.mask)} output register table".lower()
                if terms and not all(term in hay for term in terms):
                    continue
                item_id = f"output:{dvle.index}:{out.index}"
                self.tree.insert(outputs_parent, "end", iid=item_id, text=type_name, values=("Output", f"o{out.register_id} mask={component_mask(out.mask)}"))
                self.item_ranges[item_id] = (out.offset, 8)

            labels_parent = self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:labels", text="Label Table", values=("Table", f"{len(dvle.labels)} entries"), open=True)
            self.item_ranges[f"dvle:{dvle.index}:labels"] = (dvle.offset + dvle.label_offset, dvle.label_count * 0x10)
            for lab in dvle.labels:
                label_name = self.parser._label_display_name(lab)
                hay = f"{label_name} {lab.label_id} {lab.opcode_address} label table".lower()
                if terms and not all(term in hay for term in terms):
                    continue
                item_id = f"label:{dvle.index}:{lab.index}"
                self.tree.insert(labels_parent, "end", iid=item_id, text=label_name, values=("Label", f"id={lab.label_id} target={lab.opcode_address}"))
                self.item_ranges[item_id] = (lab.offset, 0x10)

            symbols_parent = self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:symbols", text="Symbol Table", values=("Symbols", f"{len(dvle.symbols)} strings"), open=True)
            self.item_ranges[f"dvle:{dvle.index}:symbols"] = (dvle.offset + dvle.symbol_offset, dvle.symbol_size)
            for sym_i, (rel, text) in enumerate(dvle.symbols):
                hay = f"{text} 0x{rel:04x} symbol table".lower()
                if terms and not all(term in hay for term in terms):
                    continue
                item_id = f"symbol:{dvle.index}:{sym_i}"
                self.tree.insert(symbols_parent, "end", iid=item_id, text=text or f"symbol_{sym_i}", values=("Symbol", f"rel=0x{rel:04X}"))
                self.item_ranges[item_id] = (dvle.offset + dvle.symbol_offset + rel, max(1, len(text) + 1))

        if needle:
            self._set_status(f"Filter active: {needle!r}")

    def _constant_preview(self, c: ShaderConstant) -> str:
        if c.entry_type == 2:
            vals = [pica24_to_float(x) for x in c.raw]
            return "(" + ", ".join(f"{v:.5g}" for v in vals) + ")"
        if c.entry_type == 0:
            return "true" if c.raw[0] else "false"
        return "(" + ", ".join(str(v) for v in c.raw[:4]) + ")"

    def on_tree_select(self, _event: Any = None) -> None:
        sel = self.tree.selection()
        if not sel:
            return
        item = sel[0]
        self.selected_constant = None
        self.selected_instruction = None
        self.selected_opdesc = None
        if item.startswith("const:"):
            _, dvle_s, const_s = item.split(":")
            self.selected_constant = (int(dvle_s), int(const_s))
            self.preview.set_selection(dvle_idx=int(dvle_s), inst_idx=None)
            self.show_constant(int(dvle_s), int(const_s))
            return
        if item.startswith("inst:"):
            _, inst_s = item.split(":")
            self.selected_instruction = int(inst_s)
            self.preview.set_selection(inst_idx=int(inst_s))
            self.show_instruction(int(inst_s))
            return
        if item.startswith("opdesc:"):
            _, opdesc_s = item.split(":")
            self.selected_opdesc = int(opdesc_s)
            self.preview.set_selection(inst_idx=None)
            self.show_opdesc(int(opdesc_s))
            return
        if item.startswith("dvle:"):
            try:
                self.preview.set_selection(dvle_idx=int(item.split(":")[1]), inst_idx=None)
            except Exception:
                pass
        self.show_item(item)

    def show_overview(self) -> None:
        lines = []
        lines.append(f"File: {self.parser.filename}")
        lines.append(f"Size: 0x{len(self.parser.data):X} ({len(self.parser.data):,} bytes)")
        lines.append(f"DVLE count: {len(self.parser.dvles)}")
        lines.append("")
        if self.parser.dvlp:
            d = self.parser.dvlp
            lines.append("DVLP Program")
            lines.append(f"  Offset: 0x{d.offset:X}")
            lines.append(f"  Version: 0x{d.version:04X}")
            lines.append(f"  Opcode table: 0x{d.offset + d.opcode_offset:X}, count={d.opcode_count}")
            lines.append(f"  Opdesc table: 0x{d.offset + d.opdesc_offset:X}, count={d.opdesc_count}")
            lines.append(f"  Line table: 0x{d.offset + d.line_offset:X}, count={d.line_count}")
            lines.append(f"  Filename symbols: 0x{d.offset + d.filename_symbol_offset:X}, size={d.filename_symbol_size}")
            lines.append("")
        for dvle in self.parser.dvles:
            lines.append(f"DVLE {dvle.index} ({dvle.shader_type_name}) @ 0x{dvle.offset:X}")
            lines.append(f"  Entrypoint: {dvle.opcode_entry}  End: {dvle.opcode_end}")
            lines.append(f"  Constants: {len(dvle.constants)}  Inputs: {len(dvle.inputs)}  Outputs: {len(dvle.outputs)}  Labels: {len(dvle.labels)}")
        lines.append("")
        lines.append(self.parser.validation_report())
        self._set_text(self.details_text, "\n".join(lines))
        self._set_text(self.raw_text, json.dumps(self.parser.to_dict(), indent=2))
        self._set_text(self.hex_text, hexdump(self.parser.data, 0, min(0x200, len(self.parser.data))))
        if hasattr(self, "preview"):
            self.preview.redraw()

    def show_item(self, item: str) -> None:
        details = self._details_for_item(item)
        self._set_text(self.details_text, details)
        start, size = self.item_ranges.get(item, (0, min(0x100, len(self.parser.data))))
        self._set_text(self.hex_text, hexdump(self.parser.data, start, min(max(size, 0x80), 0x1000)))
        self._set_text(self.raw_text, self._raw_table_for_item(item))
        self.notebook.select(0)
        self._clear_edit_tab()

    def _details_for_item(self, item: str) -> str:
        if item.startswith("input:"):
            _, dvle_s, inp_s = item.split(":")
            return self._single_input_details(self.parser.dvles[int(dvle_s)], int(inp_s))
        if item.startswith("output:"):
            _, dvle_s, out_s = item.split(":")
            return self._single_output_details(self.parser.dvles[int(dvle_s)], int(out_s))
        if item.startswith("label:"):
            _, dvle_s, lab_s = item.split(":")
            return self._single_label_details(self.parser.dvles[int(dvle_s)], int(lab_s))
        if item.startswith("symbol:"):
            _, dvle_s, sym_s = item.split(":")
            return self._single_symbol_details(self.parser.dvles[int(dvle_s)], int(sym_s))
        if item == "dvlb":
            return "\n".join([
                "DVLB Header",
                f"Magic: DVLB",
                f"DVLE count: {len(self.parser.dvle_offsets)}",
                "DVLE offsets: " + ", ".join(f"0x{x:X}" for x in self.parser.dvle_offsets),
                f"DVLP expected offset: 0x{8 + len(self.parser.dvle_offsets) * 4:X}",
            ])
        if item.startswith("dvlp"):
            return self._dvlp_details(item)
        if item.startswith("dvle:"):
            parts = item.split(":")
            dvle = self.parser.dvles[int(parts[1])]
            if len(parts) == 2 or parts[2] == "header":
                return self._dvle_header_details(dvle)
            if parts[2] == "inputs":
                return self._inputs_details(dvle)
            if parts[2] == "outputs":
                return self._outputs_details(dvle)
            if parts[2] == "labels":
                return self._labels_details(dvle)
            if parts[2] == "symbols":
                return self._symbols_details("DVLE Symbols", dvle.symbols, dvle.offset + dvle.symbol_offset)
            if parts[2] == "constants":
                return self._constants_details(dvle)
        return self.parser.validation_report()

    def _dvlp_details(self, item: str) -> str:
        d = self.parser.dvlp
        if not d:
            return "No DVLP parsed."
        lines = [
            "DVLP Program Opcodes/Opdescs",
            f"Offset: 0x{d.offset:X}",
            f"Version/type: 0x{d.version:04X}",
            f"Unknown: 0x{d.unknown:04X}",
            f"Opcode table: rel=0x{d.opcode_offset:X}, abs=0x{d.offset + d.opcode_offset:X}, count={d.opcode_count}",
            f"Opdesc table: rel=0x{d.opdesc_offset:X}, abs=0x{d.offset + d.opdesc_offset:X}, count={d.opdesc_count}",
            f"Line table: rel=0x{d.line_offset:X}, abs=0x{d.offset + d.line_offset:X}, count={d.line_count}",
            f"Filename symbols: rel=0x{d.filename_symbol_offset:X}, abs=0x{d.offset + d.filename_symbol_offset:X}, size={d.filename_symbol_size}",
            "",
        ]
        if item in {"dvlp_opcodes", "dvlp_instructions"}:
            lines.append(self._opcodes_details(d))
        elif item == "dvlp_opdescs":
            lines.append(self._opdescs_details(d))
        elif item == "dvlp_lines":
            lines.append(self._line_details(d))
        elif item == "dvlp_filenames":
            lines.append(self._symbols_details("DVLP Filename Symbols", d.filenames, d.offset + d.filename_symbol_offset))
        else:
            lines.append("Select Opcode Table, Opdesc Table, Line Number Table, or Source Filename Symbols to inspect their contents.")
        return "\n".join(lines)

    def _opcodes_details(self, d: DVLPInfo, limit: int = 512) -> str:
        lines = ["Opcode Table", "index  abs_off   word"]
        base = d.offset + d.opcode_offset
        for i, opcode in enumerate(d.opcodes[:limit]):
            lines.append(f"{i:04d}   0x{base + i * 4:06X}  0x{opcode:08X}")
        if len(d.opcodes) > limit:
            lines.append(f"... truncated in viewer; JSON export contains all {len(d.opcodes)} opcodes.")
        return "\n".join(lines)

    def _opdescs_details(self, d: DVLPInfo, limit: int = 512) -> str:
        lines = ["Opdesc Table", "index  abs_off   desc        flags"]
        base = d.offset + d.opdesc_offset
        for i, (desc, flags) in enumerate(d.opdescs[:limit]):
            lines.append(f"{i:04d}   0x{base + i * 8:06X}  0x{desc:08X}  0x{flags:08X}")
        if len(d.opdescs) > limit:
            lines.append(f"... truncated in viewer; JSON export contains all {len(d.opdescs)} opdescs.")
        return "\n".join(lines)

    def _line_details(self, d: DVLPInfo) -> str:
        if not d.lines:
            return "Line Number Table is empty."
        lines = ["Line Number Table", "index  file_off  line  filename"]
        for i, (file_off, line, filename) in enumerate(d.lines):
            lines.append(f"{i:04d}   0x{file_off:04X}    {line:<5} {filename}")
        return "\n".join(lines)

    def _dvle_header_details(self, dvle: DVLEInfo) -> str:
        return "\n".join([
            f"DVLE {dvle.index} Header",
            f"Offset: 0x{dvle.offset:X}",
            f"Version/type: 0x{dvle.version:04X}",
            f"Shader type: {dvle.shader_type_name} ({dvle.shader_type})",
            f"Opcode entry address: {dvle.opcode_entry}",
            f"Opcode end address: {dvle.opcode_end}",
            f"Unknown 0x10: 0x{dvle.unknown_10:08X}",
            f"Unknown 0x14: 0x{dvle.unknown_14:08X}",
            f"Constant table: rel=0x{dvle.const_offset:X}, abs=0x{dvle.offset + dvle.const_offset:X}, count={dvle.const_count}",
            f"Label table: rel=0x{dvle.label_offset:X}, abs=0x{dvle.offset + dvle.label_offset:X}, count={dvle.label_count}",
            f"Output table: rel=0x{dvle.output_offset:X}, abs=0x{dvle.offset + dvle.output_offset:X}, count={dvle.output_count}",
            f"Input table: rel=0x{dvle.input_offset:X}, abs=0x{dvle.offset + dvle.input_offset:X}, count={dvle.input_count}",
            f"Symbol table: rel=0x{dvle.symbol_offset:X}, abs=0x{dvle.offset + dvle.symbol_offset:X}, size={dvle.symbol_size}",
        ])

    def _constants_details(self, dvle: DVLEInfo) -> str:
        lines = ["Constants", "idx  offset    type      reg  name                         values"]
        for c in dvle.constants:
            lines.append(f"{c.index:03d}  0x{c.offset:06X}  {c.type_name:<8} {c.register_name:<4} {c.display_name:<28} {self._constant_preview(c)}")
        return "\n".join(lines)

    def _inputs_details(self, dvle: DVLEInfo) -> str:
        lines = ["Input Register Table", "idx  offset    start end   name"]
        for inp in dvle.inputs:
            lines.append(f"{inp.index:03d}  0x{inp.offset:06X}  0x{inp.start:02X}  0x{inp.end:02X}  {inp.name}")
        return "\n".join(lines)

    def _outputs_details(self, dvle: DVLEInfo) -> str:
        lines = ["Output Register Table", "idx  offset    type                  reg  mask  unknown"]
        for out in dvle.outputs:
            type_name = OUTPUT_TYPES.get(out.output_type, f"unknown_{out.output_type}")
            lines.append(f"{out.index:03d}  0x{out.offset:06X}  {type_name:<21} {out.register_id:<4} {component_mask(out.mask):<5} 0x{out.unknown:04X}")
        return "\n".join(lines)

    def _labels_details(self, dvle: DVLEInfo) -> str:
        lines = ["Label Table", "idx  offset    id  opcode_addr  name"]
        for lab in dvle.labels:
            lines.append(f"{lab.index:03d}  0x{lab.offset:06X}  {lab.label_id:<3} {lab.opcode_address:<12} {lab.name}")
        return "\n".join(lines)

    def _symbols_details(self, title: str, symbols: List[Tuple[int, str]], base_abs: int) -> str:
        lines = [title, "rel_off  abs_off   string"]
        for rel, text in symbols:
            lines.append(f"0x{rel:04X}   0x{base_abs + rel:06X}  {text}")
        if len(lines) == 2:
            lines.append("<empty>")
        return "\n".join(lines)

    def _single_input_details(self, dvle: DVLEInfo, inp_idx: int) -> str:
        inp = dvle.inputs[inp_idx]
        used_by = []
        if self.parser.dvlp:
            for inst in self.parser.dvlp.instructions:
                for ann in inst.fields.get("register_annotations", []):
                    if ann.get("dvle") == dvle.index and ann.get("input_index") == inp.index:
                        used_by.append(f"  {inst.index:04d}: {inst.fields.get('annotated_disasm', inst.disasm)}")
                        break
        lines = [
            f"Input Register: {inp.name or f'input_{inp.index}'}",
            f"DVLE: {dvle.index}",
            f"Index: {inp.index}",
            f"Entry offset: 0x{inp.offset:X}",
            f"Name symbol offset: 0x{inp.name_offset:X}",
            f"Register range: 0x{inp.start:02X}..0x{inp.end:02X}",
            "",
            "Decoded instructions using this input/register range:",
        ]
        lines.extend(used_by or ["  <none detected>"])
        return "\n".join(lines)

    def _single_output_details(self, dvle: DVLEInfo, out_idx: int) -> str:
        out = dvle.outputs[out_idx]
        type_name = OUTPUT_TYPES.get(out.output_type, f"unknown_{out.output_type}")
        used_by = []
        if self.parser.dvlp:
            for inst in self.parser.dvlp.instructions:
                for ann in inst.fields.get("register_annotations", []):
                    if ann.get("dvle") == dvle.index and ann.get("kind") == "output" and ann.get("table_index") == out.index:
                        used_by.append(f"  {inst.index:04d}: {inst.fields.get('annotated_disasm', inst.disasm)}")
                        break
        lines = [
            f"Output Register: {type_name}",
            f"DVLE: {dvle.index}",
            f"Index: {out.index}",
            f"Entry offset: 0x{out.offset:X}",
            f"Register: o{out.register_id}",
            f"Mask: {component_mask(out.mask)}",
            f"Unknown: 0x{out.unknown:04X}",
            "",
            "Decoded instructions writing this output:",
        ]
        lines.extend(used_by or ["  <none detected>"])
        return "\n".join(lines)

    def _single_label_details(self, dvle: DVLEInfo, lab_idx: int) -> str:
        lab = dvle.labels[lab_idx]
        label_name = self.parser._label_display_name(lab)
        target_inst = None
        refs = []
        if self.parser.dvlp:
            if 0 <= lab.opcode_address < len(self.parser.dvlp.instructions):
                target_inst = self.parser.dvlp.instructions[lab.opcode_address]
            for inst in self.parser.dvlp.instructions:
                for target in inst.fields.get("target_annotations", []):
                    if target.get("dvle") == dvle.index and target.get("label_index") == lab.index:
                        refs.append(f"  {inst.index:04d}: {inst.fields.get('annotated_disasm', inst.disasm)}")
                        break
        lines = [
            f"Label: {label_name}",
            f"DVLE: {dvle.index}",
            f"Index: {lab.index}",
            f"Entry offset: 0x{lab.offset:X}",
            f"Label ID: {lab.label_id}",
            f"Opcode address: {lab.opcode_address}",
            f"Name symbol offset: 0x{lab.name_offset:X}",
            f"Unknown A: {lab.unknown_a.hex(' ').upper()}",
            f"Unknown B: 0x{lab.unknown_b:08X}",
            "",
            "Target instruction:",
            f"  {target_inst.index:04d}: {target_inst.fields.get('annotated_disasm', target_inst.disasm)}" if target_inst else "  <outside decoded opcode table>",
            "",
            "Instructions referencing this label:",
        ]
        lines.extend(refs or ["  <none detected>"])
        return "\n".join(lines)

    def _single_symbol_details(self, dvle: DVLEInfo, sym_idx: int) -> str:
        rel, text = dvle.symbols[sym_idx]
        refs = []
        for inp in dvle.inputs:
            if inp.name_offset == rel:
                refs.append(f"Input[{inp.index}] regs 0x{inp.start:02X}..0x{inp.end:02X}")
        for lab in dvle.labels:
            if lab.name_offset == rel:
                refs.append(f"Label[{lab.index}] id={lab.label_id} opcode={lab.opcode_address}")
        for c in dvle.constants:
            if c.mapped_input == text or c.name == text or c.name.startswith(text + "["):
                refs.append(f"Constant[{c.index}] {c.register_name} {c.type_name}")
        lines = [
            f"Symbol: {text}",
            f"DVLE: {dvle.index}",
            f"Index: {sym_idx}",
            f"Relative offset: 0x{rel:X}",
            f"Absolute offset: 0x{dvle.offset + dvle.symbol_offset + rel:X}",
            "",
            "Referenced by:",
        ]
        lines.extend(["  " + r for r in refs] or ["  <no parsed reference>"])
        return "\n".join(lines)

    def _raw_table_for_item(self, item: str) -> str:
        if item.startswith("input:"):
            _, dvle_s, inp_s = item.split(":")
            dvle = self.parser.dvles[int(dvle_s)]
            inp = dvle.inputs[int(inp_s)]
            return json.dumps({
                "dvle": dvle.index,
                "input": inp.index,
                "name": inp.name,
                "offset": f"0x{inp.offset:X}",
                "name_offset": f"0x{inp.name_offset:X}",
                "start": f"0x{inp.start:02X}",
                "end": f"0x{inp.end:02X}",
            }, indent=2)
        if item.startswith("output:"):
            _, dvle_s, out_s = item.split(":")
            dvle = self.parser.dvles[int(dvle_s)]
            out = dvle.outputs[int(out_s)]
            return json.dumps({
                "dvle": dvle.index,
                "output": out.index,
                "type": OUTPUT_TYPES.get(out.output_type, f"unknown_{out.output_type}"),
                "type_raw": out.output_type,
                "register": f"o{out.register_id}",
                "mask": component_mask(out.mask),
                "unknown": f"0x{out.unknown:04X}",
                "offset": f"0x{out.offset:X}",
            }, indent=2)
        if item.startswith("label:"):
            _, dvle_s, lab_s = item.split(":")
            dvle = self.parser.dvles[int(dvle_s)]
            lab = dvle.labels[int(lab_s)]
            return json.dumps({
                "dvle": dvle.index,
                "label": lab.index,
                "name": self.parser._label_display_name(lab),
                "id": lab.label_id,
                "opcode_address": lab.opcode_address,
                "name_offset": f"0x{lab.name_offset:X}",
                "unknown_a": lab.unknown_a.hex(" ").upper(),
                "unknown_b": f"0x{lab.unknown_b:08X}",
                "offset": f"0x{lab.offset:X}",
            }, indent=2)
        if item.startswith("symbol:"):
            _, dvle_s, sym_s = item.split(":")
            dvle = self.parser.dvles[int(dvle_s)]
            rel, text = dvle.symbols[int(sym_s)]
            return json.dumps({
                "dvle": dvle.index,
                "symbol": int(sym_s),
                "text": text,
                "relative_offset": f"0x{rel:X}",
                "absolute_offset": f"0x{dvle.offset + dvle.symbol_offset + rel:X}",
            }, indent=2)
        if item.startswith("const:"):
            _, dvle_s, const_s = item.split(":")
            c = self.parser.dvles[int(dvle_s)].constants[int(const_s)]
            return json.dumps({
                "dvle": int(dvle_s),
                "constant": c.index,
                "name": c.display_name,
                "type": c.type_name,
                "register": c.register_name,
                "offset": f"0x{c.offset:X}",
                "raw": [f"0x{x:X}" for x in c.raw],
                "values": c.values_for_display,
            }, indent=2)
        if item.startswith("inst:") and self.parser.dvlp:
            _, inst_s = item.split(":")
            inst = self.parser.dvlp.instructions[int(inst_s)]
            return json.dumps({
                "index": inst.index,
                "offset": f"0x{inst.offset:X}",
                "word": f"0x{inst.word:08X}",
                "mnemonic": inst.mnemonic,
                "format": inst.fmt,
                "disasm": inst.disasm,
                "fields": inst.fields,
            }, indent=2)
        if item.startswith("opdesc:") and self.parser.dvlp:
            _, op_s = item.split(":")
            idx = int(op_s)
            desc, flags = self.parser.dvlp.opdescs[idx]
            return json.dumps({"index": idx, "desc": f"0x{desc:08X}", "flags": f"0x{flags:08X}", **pica_decode_opdesc(desc, flags)}, indent=2)
        if item.startswith("dvlp") and self.parser.dvlp:
            d = self.parser.dvlp
            return json.dumps(self.parser._dvlp_to_dict(), indent=2)
        if item.startswith("dvle:"):
            parts = item.split(":")
            dvle = self.parser.dvles[int(parts[1])]
            return json.dumps(self.parser._dvle_to_dict(dvle), indent=2)
        return json.dumps(self.parser.to_dict(), indent=2)

    def show_constant(self, dvle_idx: int, const_idx: int) -> None:
        c = self.parser.dvles[dvle_idx].constants[const_idx]
        details = [
            f"Constant: {c.display_name}",
            f"DVLE: {dvle_idx}",
            f"Index: {const_idx}",
            f"Offset: 0x{c.offset:X}",
            f"Type: {c.type_name}",
            f"Register: {c.register_name} (id={c.register_id})",
            f"Mapped input: {c.mapped_input or '-'}",
            f"Length hint byte: {c.length_hint}",
            f"Display values: {c.values_for_display}",
            f"Raw values: {[f'0x{x:X}' for x in c.raw]}",
        ]
        self._set_text(self.details_text, "\n".join(details))
        self._set_text(self.hex_text, hexdump(self.parser.data, c.offset, 0x40))
        self._set_text(self.raw_text, self._raw_table_for_item(f"const:{dvle_idx}:{const_idx}"))

        self.edit_name_label.configure(text=f"{c.display_name}   ({c.type_name}, {c.register_name}, offset 0x{c.offset:X})")
        values = c.values_for_display
        values = list(values) + [0, 0, 0, 0]
        for i in range(4):
            if c.entry_type == 2:
                self.edit_vars[i].set(f"{float(values[i]):.8g}")
            elif c.entry_type == 0:
                self.edit_vars[i].set("1" if bool(values[i]) else "0")
            else:
                self.edit_vars[i].set(str(int(values[i])))
            self.raw_vars[i].set(f"0x{c.raw[i]:X}")
        self.notebook.select(1)

    def show_instruction(self, inst_idx: int) -> None:
        if not self.parser.dvlp:
            return
        inst = self.parser.dvlp.instructions[inst_idx]
        f = inst.fields
        annotated = f.get("annotated_disasm", inst.disasm)
        details = [
            f"Instruction {inst.index}",
            f"Offset: 0x{inst.offset:X}",
            f"Raw word: 0x{inst.word:08X}",
            f"Mnemonic: {inst.mnemonic}",
            f"Effective opcode: 0x{inst.opcode:02X}; raw top opcode bits: 0x{inst.raw_opcode:02X}",
            f"Format: {inst.fmt}",
            f"Disasm: {inst.disasm}",
            f"Annotated disasm: {annotated}",
        ]

        source_line = f.get("source_line")
        if source_line:
            details.append(f"Source line: {source_line.get('filename', '')}:{source_line.get('line', '')}")

        if f.get("labels_here"):
            details.append("")
            details.append("Labels at this instruction:")
            for lab in f.get("labels_here", []):
                details.append(f"  DVLE {lab.get('dvle')}: {lab.get('name')} (id={lab.get('label_id')})")

        if f.get("entrypoints") or f.get("end_markers") or f.get("active_dvles"):
            details.append("")
            details.append("DVLE ranges:")
            for ref in f.get("entrypoints", []):
                details.append(f"  Entry for DVLE {ref.get('dvle')} ({ref.get('shader_type')})")
            for ref in f.get("end_markers", []):
                details.append(f"  End marker for DVLE {ref.get('dvle')} ({ref.get('shader_type')})")
            active = ", ".join(f"DVLE {x.get('dvle')}" for x in f.get("active_dvles", []))
            if active:
                details.append(f"  In active range: {active}")

        if f.get("register_annotations"):
            details.append("")
            details.append("Register/symbol mapping:")
            for ann in f.get("register_annotations", []):
                sym = ann.get("symbol") or "-"
                table = ann.get("table") or "-"
                details.append(f"  DVLE {ann.get('dvle')} {ann.get('role')}: {ann.get('register')} -> {sym} ({table})")

        if f.get("target_annotations"):
            details.append("")
            details.append("Branch/call target labels:")
            for ann in f.get("target_annotations", []):
                details.append(f"  DVLE {ann.get('dvle')}: target {ann.get('opcode_address')} -> {ann.get('name')}")

        details.extend(["", "Decoded fields:"])
        hidden = {"opdesc", "source_line", "labels_here", "entrypoints", "end_markers", "active_dvles", "register_annotations", "target_annotations", "annotated_disasm", "annotated_disasm_by_dvle"}
        for key in sorted(k for k in f.keys() if k not in hidden):
            details.append(f"  {key}: {f[key]}")
        if "opdesc" in f:
            details.append("")
            details.append("Referenced operand descriptor:")
            for key, val in f["opdesc"].items():
                details.append(f"  {key}: {val}")
        self._set_text(self.details_text, "\n".join(details))
        self._set_text(self.hex_text, hexdump(self.parser.data, inst.offset, 0x40))
        self._set_text(self.raw_text, self._raw_table_for_item(f"inst:{inst_idx}"))

        self.instr_header_label.configure(text=f"Instruction {inst.index}: {f.get('annotated_disasm', inst.disasm)}")
        dvle_idx = self._active_dvle_for_instruction(inst.index)
        self.instr_raw_var.set(f"0x{inst.word:08X}")
        self.instr_mnemonic_var.set(inst.mnemonic)
        self.instr_asm_var.set(str(annotated))
        self.instr_desc_var.set(str(f.get("desc_id", 0)))
        self.instr_dst_var.set(self._display_register_field(str(f.get("dst", "r0")), dvle_idx))
        self.instr_src1_var.set(self._display_register_field(str(f.get("src1", "v0")), dvle_idx))
        self.instr_src2_var.set(self._display_register_field(str(f.get("src2", "v0")), dvle_idx))
        self.instr_src3_var.set(self._display_register_field(str(f.get("src3", "v0")), dvle_idx))
        self.instr_idx_var.set(str(f.get("idx", 0)))
        self.instr_num_var.set(str(f.get("num", 0)))
        self.instr_target_var.set(str(f.get("target", 0)))
        self.instr_condop_var.set(str(f.get("condop_name", f.get("condop", 0))))
        uid = int(f.get("uniform_id", 0) or 0)
        if "uniform_id" in f:
            uniform_reg = ("i" if inst.opcode == 0x29 else "b") + str(uid)
            self.instr_boolint_var.set(self._display_register_field(uniform_reg, dvle_idx))
        else:
            self.instr_boolint_var.set(str(uid))
        self.instr_refx_var.set(str(f.get("refx", 0)))
        self.instr_refy_var.set(str(f.get("refy", 0)))
        self.instr_cmpx_var.set(str(f.get("cmpx_name", f.get("cmpx", 0))))
        self.instr_cmpy_var.set(str(f.get("cmpy_name", f.get("cmpy", 0))))
        self._refresh_instruction_register_choices(inst.index)
        self.notebook.select(2)

    def show_opdesc(self, opdesc_idx: int) -> None:
        if not self.parser.dvlp:
            return
        desc, flags = self.parser.dvlp.opdescs[opdesc_idx]
        dec = pica_decode_opdesc(desc, flags)
        details = [
            f"Operand Descriptor {opdesc_idx}",
            f"Offset: 0x{self.parser.dvlp.offset + self.parser.dvlp.opdesc_offset + opdesc_idx * 8:X}",
            f"Raw desc: 0x{desc:08X}",
            f"Flags: 0x{flags:08X}",
            "",
            f"Destination mask: {dec['dest_mask']} (raw 0x{dec['dest_mask_raw']:X})",
            f"SRC1: {'-' if dec['src1_neg'] else ''}.{dec['src1_swizzle']} raw=0x{dec['src1_swizzle_raw']:02X}",
            f"SRC2: {'-' if dec['src2_neg'] else ''}.{dec['src2_swizzle']} raw=0x{dec['src2_swizzle_raw']:02X}",
            f"SRC3: {'-' if dec['src3_neg'] else ''}.{dec['src3_swizzle']} raw=0x{dec['src3_swizzle_raw']:02X}",
            "",
            "Instructions using this opdesc:",
        ]
        users = []
        for inst in self.parser.dvlp.instructions:
            if inst.fields.get("desc_id") == opdesc_idx:
                users.append(f"  {inst.index:04d}: {inst.disasm}")
        details.extend(users or ["  <none>"])
        self._set_text(self.details_text, "\n".join(details))
        off = self.parser.dvlp.offset + self.parser.dvlp.opdesc_offset + opdesc_idx * 8
        self._set_text(self.hex_text, hexdump(self.parser.data, off, 0x40))
        self._set_text(self.raw_text, self._raw_table_for_item(f"opdesc:{opdesc_idx}"))

        self.opdesc_header_label.configure(text=f"Operand Descriptor {opdesc_idx}")
        self.opdesc_raw_var.set(f"0x{desc:08X}")
        self.opdesc_flags_var.set(f"0x{flags:08X}")
        self.opdesc_mask_var.set(dec["dest_mask"])
        self.opdesc_src1_swizzle_var.set(dec["src1_swizzle"])
        self.opdesc_src2_swizzle_var.set(dec["src2_swizzle"])
        self.opdesc_src3_swizzle_var.set(dec["src3_swizzle"])
        self.opdesc_src1_neg_var.set(bool(dec["src1_neg"]))
        self.opdesc_src2_neg_var.set(bool(dec["src2_neg"]))
        self.opdesc_src3_neg_var.set(bool(dec["src3_neg"]))
        self.notebook.select(3)

    def _clear_instruction_tab(self) -> None:
        if hasattr(self, "instr_header_label"):
            self.instr_header_label.configure(text="Select a decoded instruction to edit.")
        for v in [self.instr_mnemonic_var, self.instr_raw_var, self.instr_asm_var, self.instr_desc_var,
                  self.instr_dst_var, self.instr_src1_var, self.instr_src2_var, self.instr_src3_var,
                  self.instr_idx_var, self.instr_num_var, self.instr_target_var, self.instr_condop_var,
                  self.instr_boolint_var, self.instr_refx_var, self.instr_refy_var, self.instr_cmpx_var, self.instr_cmpy_var]:
            v.set("")
        self._refresh_instruction_register_choices(None)

    def _clear_opdesc_tab(self) -> None:
        if hasattr(self, "opdesc_header_label"):
            self.opdesc_header_label.configure(text="Select an operand descriptor to edit.")
        for v in [self.opdesc_raw_var, self.opdesc_flags_var, self.opdesc_mask_var,
                  self.opdesc_src1_swizzle_var, self.opdesc_src2_swizzle_var, self.opdesc_src3_swizzle_var]:
            v.set("")
        self.opdesc_src1_neg_var.set(False)
        self.opdesc_src2_neg_var.set(False)
        self.opdesc_src3_neg_var.set(False)

    def _current_instruction_index(self) -> int:
        if self.selected_instruction is None:
            raise ValueError("Select an instruction first.")
        return self.selected_instruction

    def _current_opdesc_index(self) -> int:
        if self.selected_opdesc is None:
            raise ValueError("Select an operand descriptor first.")
        return self.selected_opdesc

    def _refresh_after_instruction_edit(self, inst_idx: Optional[int] = None) -> None:
        self.parser.parse()
        self.refresh_tree()
        if inst_idx is not None and self.parser.dvlp and 0 <= inst_idx < len(self.parser.dvlp.instructions):
            iid = f"inst:{inst_idx}"
            if self.tree.exists(iid):
                self.tree.selection_set(iid)
                self.tree.see(iid)
            self.selected_instruction = inst_idx
            self.show_instruction(inst_idx)
        self.preview.set_shader(self.parser)
        if inst_idx is not None:
            self.preview.set_selection(inst_idx=inst_idx)
        self._set_status("Instruction/opdesc edit applied. Save to write it to disk.")

    def apply_instruction_raw(self) -> None:
        try:
            inst_idx = self._current_instruction_index()
            word = int(self.instr_raw_var.get().strip() or "0", 0)
            self.parser.update_opcode_word(inst_idx, word)
            self._refresh_after_instruction_edit(inst_idx)
        except Exception as exc:
            messagebox.showerror("Instruction raw edit failed", str(exc))

    def apply_instruction_fields(self) -> None:
        try:
            inst_idx = self._current_instruction_index()
            if not self.parser.dvlp:
                return
            base_word = self.parser.dvlp.instructions[inst_idx].word
            labels = self._labels_for_dvle(self._active_dvle_for_instruction(inst_idx))
            word = pica_build_instruction_word(
                self.instr_mnemonic_var.get(),
                base_word=base_word,
                desc_id=int(self.instr_desc_var.get().strip() or "0", 0),
                dst=self._resolve_register_field(self.instr_dst_var.get().strip() or "r0", "dst", inst_idx),
                src1=self._resolve_register_field(self.instr_src1_var.get().strip() or "v0", "src", inst_idx),
                src2=self._resolve_register_field(self.instr_src2_var.get().strip() or "v0", "src", inst_idx),
                src3=self._resolve_register_field(self.instr_src3_var.get().strip() or "v0", "src", inst_idx),
                idx=int(self.instr_idx_var.get().strip() or "0", 0),
                num=int(self.instr_num_var.get().strip() or "0", 0),
                target=parse_target_token(self.instr_target_var.get().strip() or "0", labels),
                condop=parse_condop(self.instr_condop_var.get().strip() or "0"),
                refx=int(self.instr_refx_var.get().strip() or "0", 0),
                refy=int(self.instr_refy_var.get().strip() or "0", 0),
                uniform_id=parse_uniform_token(self._resolve_register_field(self.instr_boolint_var.get().strip() or "0", "uniform", inst_idx)),
                cmpx=parse_cmpop(self.instr_cmpx_var.get().strip() or "0"),
                cmpy=parse_cmpop(self.instr_cmpy_var.get().strip() or "0"),
            )
            self.parser.update_opcode_word(inst_idx, word)
            self._refresh_after_instruction_edit(inst_idx)
        except Exception as exc:
            messagebox.showerror("Instruction field edit failed", str(exc))

    def apply_instruction_asm(self) -> None:
        try:
            inst_idx = self._current_instruction_index()
            if not self.parser.dvlp:
                return
            existing = self.parser.dvlp.instructions[inst_idx]
            desc_id = int(existing.fields.get("desc_id", 0))
            dvle_idx = self._active_dvle_for_instruction(inst_idx)
            word, opdesc_fields = parse_general_asm_line(
                self.instr_asm_var.get(),
                base_word=existing.word,
                default_desc_id=desc_id,
                labels=self._labels_for_dvle(dvle_idx),
                symbol_to_register=self._symbol_map_for_asm_roundtrip(inst_idx, dvle_idx),
            )
            self.parser.update_opcode_word(inst_idx, word)
            if opdesc_fields is not None and 0 <= desc_id < self.parser.dvlp.opdesc_count:
                old_desc, old_flags = self.parser.dvlp.opdescs[desc_id]
                desc, flags = pica_encode_opdesc(
                    opdesc_fields.get("mask", "xyzw"),
                    opdesc_fields.get("src1_swizzle", "xyzw"),
                    opdesc_fields.get("src2_swizzle", "xyzw"),
                    opdesc_fields.get("src3_swizzle", "xyzw"),
                    bool(opdesc_fields.get("src1_neg", False)),
                    bool(opdesc_fields.get("src2_neg", False)),
                    bool(opdesc_fields.get("src3_neg", False)),
                    preserve_flags=old_flags,
                )
                self.parser.update_opdesc(desc_id, desc, flags)
            self._refresh_after_instruction_edit(inst_idx)
        except Exception as exc:
            messagebox.showerror("ASM patch failed", str(exc))


    def insert_nop_before_selected(self) -> None:
        try:
            inst_idx = self._current_instruction_index()
            if not messagebox.askyesno("Insert NOP", "This shifts opcode words down inside the existing opcode table and drops the last opcode. Continue?"):
                return
            self.parser.insert_nop_instruction(inst_idx)
            self._refresh_after_instruction_edit(inst_idx)
        except Exception as exc:
            messagebox.showerror("Insert instruction failed", str(exc))

    def delete_selected_instruction(self) -> None:
        try:
            inst_idx = self._current_instruction_index()
            if not messagebox.askyesno("Delete instruction", "This shifts following opcode words up and fills the final slot with NOP. Continue?"):
                return
            self.parser.delete_instruction_shift_up(inst_idx)
            self._refresh_after_instruction_edit(min(inst_idx, max(0, self.parser.dvlp.opcode_count - 1 if self.parser.dvlp else 0)))
        except Exception as exc:
            messagebox.showerror("Delete instruction failed", str(exc))

    def add_asm_instruction_to_active_dvle(self) -> None:
        if not self._require_loaded():
            return
        asm = simpledialog.askstring("Add ASM instruction", "ASM to insert before the active DVLE end marker:", initialvalue=self.instr_asm_var.get() or "nop")
        if not asm:
            return
        try:
            dvle_idx = self.preview.current_dvle_index if hasattr(self, "preview") and self.preview.current_dvle_index is not None else 0
            idx = self.parser.add_instruction_at_end_of_range(int(dvle_idx), asm)
            self._refresh_after_instruction_edit(idx)
        except Exception as exc:
            messagebox.showerror("Add instruction failed", str(exc))

    def apply_opdesc_raw(self) -> None:
        try:
            idx = self._current_opdesc_index()
            desc = int(self.opdesc_raw_var.get().strip() or "0", 0)
            flags = int(self.opdesc_flags_var.get().strip() or "0", 0)
            self.parser.update_opdesc(idx, desc, flags)
            self.parser.parse()
            self.refresh_tree()
            iid = f"opdesc:{idx}"
            if self.tree.exists(iid):
                self.tree.selection_set(iid)
                self.tree.see(iid)
            self.selected_opdesc = idx
            self.show_opdesc(idx)
            self.preview.set_shader(self.parser)
            self._set_status("Operand descriptor raw edit applied. Save to write it to disk.")
        except Exception as exc:
            messagebox.showerror("Opdesc raw edit failed", str(exc))

    def apply_opdesc_decoded(self) -> None:
        try:
            idx = self._current_opdesc_index()
            flags = int(self.opdesc_flags_var.get().strip() or "0", 0)
            desc, flags = pica_encode_opdesc(
                self.opdesc_mask_var.get() or "xyzw",
                self.opdesc_src1_swizzle_var.get() or "xyzw",
                self.opdesc_src2_swizzle_var.get() or "xyzw",
                self.opdesc_src3_swizzle_var.get() or "xyzw",
                self.opdesc_src1_neg_var.get(),
                self.opdesc_src2_neg_var.get(),
                self.opdesc_src3_neg_var.get(),
                preserve_flags=flags,
            )
            self.parser.update_opdesc(idx, desc, flags)
            self.parser.parse()
            self.refresh_tree()
            iid = f"opdesc:{idx}"
            if self.tree.exists(iid):
                self.tree.selection_set(iid)
                self.tree.see(iid)
            self.selected_opdesc = idx
            self.show_opdesc(idx)
            self.preview.set_shader(self.parser)
            self._set_status("Operand descriptor decoded edit applied. Save to write it to disk.")
        except Exception as exc:
            messagebox.showerror("Opdesc decoded edit failed", str(exc))

    def _clear_edit_tab(self) -> None:
        self.edit_name_label.configure(text="Select a constant to edit.")
        for v in self.edit_vars + self.raw_vars:
            v.set("")
        self._clear_instruction_tab()
        self._clear_opdesc_tab()

    def _current_constant(self) -> Optional[ShaderConstant]:
        if self.selected_constant is None:
            return None
        dvle_idx, const_idx = self.selected_constant
        return self.parser.dvles[dvle_idx].constants[const_idx]

    def apply_display_values(self) -> None:
        c = self._current_constant()
        if c is None or self.selected_constant is None:
            messagebox.showinfo("No constant selected", "Select a constant entry first.")
            return
        try:
            if c.entry_type == 2:
                raw = [float_to_pica24(float(v.get().strip() or "0")) for v in self.edit_vars]
            elif c.entry_type == 0:
                raw = [1 if self._parse_bool(self.edit_vars[0].get()) else 0, 0, 0, 0]
            else:
                raw = [int(v.get().strip() or "0", 0) & 0xFF for v in self.edit_vars]
            dvle_idx, const_idx = self.selected_constant
            self.parser.update_constant(dvle_idx, const_idx, raw)
            self.parser.parse()
            self.refresh_tree()
            self.tree.selection_set(f"const:{dvle_idx}:{const_idx}")
            self.show_constant(dvle_idx, const_idx)
            self.preview.set_shader(self.parser)
            self.preview.set_selection(dvle_idx=dvle_idx, inst_idx=None)
            self._set_status("Applied constant values. Save to write them to disk.")
        except Exception as exc:
            messagebox.showerror("Invalid value", str(exc))

    def apply_raw_values(self) -> None:
        c = self._current_constant()
        if c is None or self.selected_constant is None:
            messagebox.showinfo("No constant selected", "Select a constant entry first.")
            return
        try:
            raw = [int(v.get().strip() or "0", 0) for v in self.raw_vars]
            if c.entry_type == 2:
                raw = [x & 0xFFFFFF for x in raw]
            elif c.entry_type == 1:
                raw = [x & 0xFF for x in raw]
            elif c.entry_type == 0:
                raw = [1 if raw[0] else 0, 0, 0, 0]
            dvle_idx, const_idx = self.selected_constant
            self.parser.update_constant(dvle_idx, const_idx, raw)
            self.parser.parse()
            self.refresh_tree()
            self.tree.selection_set(f"const:{dvle_idx}:{const_idx}")
            self.show_constant(dvle_idx, const_idx)
            self.preview.set_shader(self.parser)
            self.preview.set_selection(dvle_idx=dvle_idx, inst_idx=None)
            self._set_status("Applied raw constant values. Save to write them to disk.")
        except Exception as exc:
            messagebox.showerror("Invalid raw value", str(exc))

    @staticmethod
    def _parse_bool(text: str) -> bool:
        return text.strip().lower() in {"1", "true", "yes", "on"}

    def copy_constant_json(self) -> None:
        c = self._current_constant()
        if c is None or self.selected_constant is None:
            return
        dvle_idx, _const_idx = self.selected_constant
        payload = {
            "dvle": dvle_idx,
            "index": c.index,
            "name": c.display_name,
            "type": c.type_name,
            "register": c.register_name,
            "offset": f"0x{c.offset:X}",
            "values": c.values_for_display,
            "raw": [f"0x{x:X}" for x in c.raw],
        }
        self.clipboard_clear()
        self.clipboard_append(json.dumps(payload, indent=2))
        self._set_status("Copied constant JSON to clipboard.")


def main() -> None:
    App().mainloop()


if __name__ == "__main__":
    main()

__all__ = [name for name in globals() if not name.startswith("__")]
