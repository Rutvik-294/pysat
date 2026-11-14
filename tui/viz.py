"""SAT Solver Visualizer — interactive terminal app for CDCL & DPLL.

Run:  python3 -m tui.viz

Keys:
  ← / h        step back            → / l     step forward
  space        run / pause (auto-play)        r         reset to start
  j / k        scroll clause list   1 / 2     switch DPLL / CDCL
  e            edit formula         q         quit
"""
from __future__ import annotations

import curses
import time

from .dpll_trace import DPLLTracer, fmt_cl as dpll_fmt_cl
from .cdcl_trace import CDCLTracer, fmt_cl

PRESETS = {
    "Simple":          ([[1, 2], [-1, 3], [-2, 3]], 3),
    "UNSAT 2-var":     ([[1, 2], [-1, 2], [1, -2], [-1, -2]], 2),
    "Pigeonhole 3":    ([[1, 2], [3, 4], [5, 6],
                         [-1, -3], [-1, -5], [-3, -5],
                         [-2, -4], [-2, -6], [-4, -6]], 6),
    "Pigeonhole 4":    ([[1, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12],
                         [-1, -4], [-1, -7], [-1, -10], [-4, -7], [-4, -10],
                         [-7, -10], [-2, -5], [-2, -8], [-2, -11], [-5, -8],
                         [-5, -11], [-8, -11], [-3, -6], [-3, -9], [-3, -12],
                         [-6, -9], [-6, -12], [-9, -12]], 12),
    "Implication":     ([[5], [-5, 4], [-4, 3], [-3, 2], [-2, 1], [-1]], 5),
    "Branching demo":  ([[1, 2], [-1, 2], [1, -2], [-1, -2]], 2),
    "Backtrack 3-level": ([[1, 2], [-2, 3], [-3], [1, -3], [2, -1]], 3),
}

# start on the branching demo so the DPLL tree is visible immediately
DEFAULT_PRESET = "Branching demo"

MODES = ["CDCL", "DPLL"]


class App:
    def __init__(self, stdscr):
        self.stdscr = stdscr
        curses.curs_set(0)
        self.mode = 0                      # index into MODES
        self.clauses, self.num_vars = PRESETS[DEFAULT_PRESET]
        self.editing = False
        self.edit_buf = ""
        self.edit_msg = ""
        self.scrolloff = 0
        self.rebuild()

    # ------------------------------------------------------------------
    def rebuild(self):
        """Compute the trace for current formula and mode."""
        if self.mode == 0:
            self.steps = CDCLTracer(self.clauses, self.num_vars).run()
            self.tree_root = None
        else:
            self.steps = DPLLTracer(self.clauses, self.num_vars).run()
            from .tree import build_tree
            self.tree_root = build_tree(self.steps)
        self.pos = 0
        self.playing = False
        self.last_frame = None

    def _tree_lines_cache(self):
        from .tree import render_tree
        return render_tree(self.tree_root, self.pos)

    # ------------------------------------------------------------------
    def draw(self):
        s = self.stdscr
        s.erase()
        H, W = s.getmaxyx()
        step = self.steps[self.pos]

        # ---- header ----
        mode_str = " / ".join(
            ("> " + m + " <") if i == self.mode else m
            for i, m in enumerate(MODES))
        title = f" SAT SOLVER VISUALIZER   [{mode_str}]   "
        s.attron(curses.A_REVERSE)
        s.addnstr(0, 0, title.ljust(W), W - 1)
        s.attroff(curses.A_REVERSE)

        # ---- step banner ----
        kind_colors = {
            "init": curses.COLOR_CYAN, "decide": curses.COLOR_YELLOW,
            "branch": curses.COLOR_YELLOW, "propagate": curses.COLOR_GREEN,
            "unit": curses.COLOR_GREEN, "pure": curses.COLOR_MAGENTA,
            "conflict": curses.COLOR_RED, "learn": curses.COLOR_BLUE,
            "backtrack": curses.COLOR_RED, "backjump": curses.COLOR_BLUE,
            "sat": curses.COLOR_GREEN, "unsat": curses.COLOR_RED,
            "scan": curses.COLOR_CYAN, "resolve": curses.COLOR_MAGENTA,
            "assert": curses.COLOR_BLUE,
        }
        color = kind_colors.get(step.kind, curses.COLOR_WHITE)
        s.attron(curses.color_pair(1) | curses.A_BOLD)
        s.addnstr(1, 0, f" STEP {self.pos + 1}/{len(self.steps)}  ", W - 1)
        s.attroff(curses.color_pair(1) | curses.A_BOLD)
        try:
            s.attron(curses.color_pair(color) | curses.A_BOLD)
            s.addnstr(1, 22, f"[{step.kind.upper()}] {step.desc}", W - 23)
            s.attroff(curses.color_pair(color) | curses.A_BOLD)
        except curses.error:
            pass

        # ---- note line (why the algorithm does this) ----
        note = getattr(step, "note", "") or ""
        if note:
            try:
                s.attron(curses.color_pair(6))  # magenta
                s.addnstr(2, 2, f"ℹ {note}", W - 3)
                s.attroff(curses.color_pair(6))
            except curses.error:
                pass

        # ---- left column: clauses (top) + DPLL search tree (bottom) ----
        left_w = max(24, W * 2 // 5)
        if self.mode == 1 and self.tree_root is not None:
            from .tree import render_tree
            tlines = [t for t in render_tree(self.tree_root, self.pos)
                      if t[0] != "root"]
            # fixed split: bottom 40% of the panel area for the tree
            area_h = H - 5                     # rows 4..H-3 usable
            tree_rows = max(4, min(area_h * 2 // 5, len(tlines) + 1))
            tree_top = H - 2 - tree_rows
            clause_bottom = tree_top
        else:
            tlines = []
            tree_rows = 0
            tree_top = H - 2
            clause_bottom = H - 2
        self._panel(3, 0, clause_bottom - 4, left_w, "Clauses")
        hi = set(step.highlight)
        assign = step.assign
        row = 4
        maxlen = left_w - 4
        all_cls = self._display_clauses(step)
        shown = 0
        for idx, c in enumerate(all_cls):
            if row >= clause_bottom - 1:
                break
            if idx < self.scrolloff:
                continue
            text = fmt_cl(c)
            # annotate truth value under current assignment
            vals = []
            for l in c:
                v = abs(l)
                if v in assign:
                    ok = assign[v] == (l > 0)
                    vals.append(ok)
                else:
                    vals.append(None)
            if any(vals):
                sym = "✓"
            elif all(x is False for x in vals):
                sym = "✗"
            else:
                sym = " "
            line = f"{sym} {text}"
            if idx in hi:
                s.attron(curses.color_pair(kind_color_pair(step.kind)))
            elif sym == "✓":
                s.attron(curses.color_pair(curses.COLOR_GREEN))
            elif sym == "✗":
                s.attron(curses.color_pair(curses.COLOR_RED))
            s.addnstr(row, 2, line[:maxlen], left_w - 3)
            if idx in hi:
                s.attroff(curses.color_pair(kind_color_pair(step.kind)))
            elif sym == "✓":
                s.attroff(curses.color_pair(curses.COLOR_GREEN))
            elif sym == "✗":
                s.attroff(curses.color_pair(curses.COLOR_RED))
            row += 1
            shown += 1
        if not all_cls:
            s.addnstr(4, 2, "∅ all satisfied", left_w - 3)

        # ---- left-bottom: DPLL search tree ----
        if self.mode == 1 and tree_rows:
            self._panel(tree_top, 0, tree_rows + 2, left_w, "Search tree")
            trow = tree_top + 1
            if not tlines:
                s.attron(curses.color_pair(curses.COLOR_CYAN))
                s.addnstr(trow, 2, "branching hasn't started yet…"
                          [:left_w - 3], left_w - 3)
                s.attroff(curses.color_pair(curses.COLOR_CYAN))
                trow += 1
            for txt, pair in tlines[-(tree_rows - 1):]:
                if trow >= H - 2:
                    break
                if pair == "failed":
                    s.attron(curses.color_pair(curses.COLOR_RED) |
                             curses.A_BOLD)
                elif pair == "ok":
                    s.attron(curses.color_pair(curses.COLOR_GREEN) |
                             curses.A_BOLD)
                elif pair == "open":
                    s.attron(curses.color_pair(curses.COLOR_CYAN))
                s.addnstr(trow, 2, txt[:left_w - 3], left_w - 3)
                if pair == "failed":
                    s.attroff(curses.color_pair(curses.COLOR_RED) |
                              curses.A_BOLD)
                elif pair == "ok":
                    s.attroff(curses.color_pair(curses.COLOR_GREEN) |
                              curses.A_BOLD)
                elif pair == "open":
                    s.attroff(curses.color_pair(curses.COLOR_CYAN))
                trow += 1

        # ---- right: assignment / trail / learned ----
        x2 = left_w + 1
        w2 = W - x2 - 1
        self._panel(3, x2, (H - 5) // 2, w2, "Assignment")
        row = 4
        trail_by_var = {tv: why for tv, val, why in getattr(step, "trail", [])}
        for v in range(1, self.num_vars + 1):
            if row >= H // 2:
                break
            mark = ""
            if v in assign:
                mark = "T" if assign[v] else "F"
                why = trail_by_var.get(v, "")
                tag = ""
                if why.startswith("decision"):
                    tag = " ←decision"
                elif why.startswith("unit"):
                    tag = " ←unit"
                elif why.startswith("learned"):
                    tag = " ←learned"
                line = f"  x{v} = {mark}{tag}"
                pair = curses.COLOR_YELLOW if tag == " ←decision" else \
                    curses.COLOR_GREEN if tag == " ←unit" else \
                    curses.COLOR_BLUE if tag == " ←learned" else \
                    curses.COLOR_WHITE
                s.attron(curses.color_pair(pair) if v == step.focus_var else
                         curses.color_pair(pair))
                s.addnstr(row, x2 + 2, line[:w2 - 3], w2 - 3)
                s.attroff(curses.color_pair(pair))
            else:
                if v == step.focus_var:
                    s.attron(curses.A_REVERSE)
                s.addnstr(row, x2 + 2, f"  x{v} = .", w2 - 3)
                if v == step.focus_var:
                    s.attroff(curses.A_REVERSE)
            row += 1

        # learned clauses (CDCL) + clause being built (resolve steps)
        learned = getattr(step, "learned_db", getattr(step, "learned", []))
        learning = getattr(step, "learning", [])
        if learning or learned:
            self._panel(H // 2, x2, (H - 4) - (H // 2) + 1, w2, "Learned")
            row = H // 2 + 1
            if learning:
                s.attron(curses.color_pair(curses.COLOR_MAGENTA) | curses.A_BOLD)
                s.addnstr(row, x2 + 2,
                          f"building: {fmt_cl(learning)}"[:w2 - 3], w2 - 3)
                s.attroff(curses.color_pair(curses.COLOR_MAGENTA) | curses.A_BOLD)
                row += 1
            for lc in learned[-((H - 4) - (H // 2) - 3):]:
                if row >= H - 3:
                    break
                s.attron(curses.color_pair(curses.COLOR_BLUE))
                s.addnstr(row, x2 + 2, fmt_cl(lc)[:w2 - 3], w2 - 3)
                s.attroff(curses.color_pair(curses.COLOR_BLUE))
                row += 1

        # ---- footer ----
        s.attron(curses.A_REVERSE)
        status = " ▶ PLAYING " if self.playing else " ⏸ PAUSED  "
        help_ = ("← → step  space run  r reset  1 DPLL  2 CDCL  "
                 "e edit  q quit")
        s.addnstr(H - 2, 0, (status + help_).ljust(W), W - 1)
        s.attroff(curses.A_REVERSE)

        # progress bar
        if len(self.steps) > 1:
            frac = self.pos / (len(self.steps) - 1)
            bar_w = W - 2
            filled = int(frac * bar_w)
            s.addnstr(H - 1, 0, "█" * filled + "░" * (bar_w - filled), W - 1)
        s.refresh()

    def _display_clauses(self, step):
        if self.mode == 1:
            return step.frame_clauses
        return self.clauses + getattr(step, "learned_db",
                                      getattr(step, "learned", []))

    def _panel(self, y, x, h, w, title):
        s = self.stdscr
        try:
            s.attron(curses.color_pair(2))
            s.addnstr(y, x, f"─ {title} ".ljust(w), w)
            s.attroff(curses.color_pair(2))
        except curses.error:
            pass

    # ------------------------------------------------------------------
    def run(self):
        self.stdscr.nodelay(False)
        self.stdscr.timeout(100)
        while True:
            self.draw()
            key = self.stdscr.getch()
            if key == -1:
                if self.playing:
                    if self.pos < len(self.steps) - 1:
                        self.pos += 1
                    else:
                        self.playing = False
                continue
            if self._handle(key):
                break

    def _handle(self, key) -> bool:
        """Returns True to quit."""
        if key in (ord('q'), ord('Q')):
            return True
        elif key == curses.KEY_RIGHT or key in (ord('l'),):
            if self.pos < len(self.steps) - 1:
                self.pos += 1
            self.playing = False
        elif key == curses.KEY_LEFT or key in (ord('h'),):
            if self.pos > 0:
                self.pos -= 1
            self.playing = False
        elif key == ord(' '):
            if self.pos >= len(self.steps) - 1:
                self.pos = 0
            self.playing = not self.playing
        elif key in (ord('r'), ord('R')):
            self.pos = 0
            self.playing = False
        elif key in (ord('1'),):
            self.mode = 1
            self.rebuild()
        elif key in (ord('2'),):
            self.mode = 0
            self.rebuild()
        elif key in (ord('e'), ord('E')):
            self._edit_formula()
        elif key == curses.KEY_DOWN or key in (ord('j'),):
            self.scrolloff = min(self.scrolloff + 1,
                                 max(0, len(self.clauses) - 3))
        elif key == curses.KEY_UP or key in (ord('k'),):
            self.scrolloff = max(0, self.scrolloff - 1)
        return False

    # ------------------------------------------------------------------
    def _edit_formula(self):
        """Simple modal editor: type DIMACS-style clause list."""
        self.editing = True
        curses.curs_set(1)
        s = self.stdscr
        buf = ""
        msg = ("Enter clauses, e.g. 1 2 0 -1 3 0 -2 3 0  (0 ends a clause;"
               " digits only, spaces optional between clauses)")
        while True:
            s.erase()
            H, W = s.getmaxyx()
            s.addnstr(1, 2, "EDIT FORMULA", W - 3)
            s.addnstr(3, 2, msg[:W - 3], W - 3)
            s.addnstr(5, 2, ("> " + buf)[-W + 3:], W - 3)
            s.addnstr(7, 2, "Enter = parse & animate · Esc = cancel", W - 3)
            s.refresh()
            k = s.getch()
            if k == 27:  # ESC
                break
            elif k in (10, 13):  # enter
                parsed = self._parse_buf(buf)
                if parsed is None:
                    s.addnstr(8, 2, "✗ invalid — use ints, 0 ends a clause",
                              W - 3)
                    s.refresh()
                    s.getch()
                    continue
                clauses, nv = parsed
                if not clauses:
                    s.addnstr(8, 2, "✗ need at least one clause", W - 3)
                    s.refresh()
                    s.getch()
                    continue
                if nv > 12:
                    s.addnstr(8, 2, "✗ max 12 variables for animation", W - 3)
                    s.refresh()
                    s.getch()
                    continue
                self.clauses, self.num_vars = clauses, nv
                self.rebuild()
                break
            elif k in (curses.KEY_BACKSPACE, 127, 8):
                buf = buf[:-1]
            elif 32 <= k < 127:
                buf += chr(k)
        curses.curs_set(0)
        self.editing = False

    def _parse_buf(self, buf):
        try:
            toks = buf.split()
            if not toks:
                return None
            clauses, cur = [], []
            nv = 0
            for t in toks:
                l = int(t)
                if l == 0:
                    if not cur:
                        return None
                    clauses.append(cur)
                    cur = []
                else:
                    if abs(l) > 12:
                        return None
                    nv = max(nv, abs(l))
                    cur.append(l)
            if cur:
                clauses.append(cur)
            return clauses, nv
        except ValueError:
            return None


def kind_color_pair(kind):
    mapping = {
        "conflict": curses.COLOR_RED, "backtrack": curses.COLOR_RED,
        "learn": curses.COLOR_BLUE, "backjump": curses.COLOR_BLUE,
        "decide": curses.COLOR_YELLOW, "branch": curses.COLOR_YELLOW,
    }
    return mapping.get(kind, curses.COLOR_WHITE)


def main(stdscr):
    curses.start_color()
    curses.use_default_colors()
    for i, c in enumerate([curses.COLOR_CYAN, curses.COLOR_GREEN,
                           curses.COLOR_YELLOW, curses.COLOR_RED,
                           curses.COLOR_BLUE, curses.COLOR_MAGENTA,
                           curses.COLOR_WHITE], 1):
        curses.init_pair(i, c, -1)
    app = App(stdscr)
    app.run()


def entry():
    curses.wrapper(main)


if __name__ == "__main__":
    entry()
