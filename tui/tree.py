"""DPLL search-tree visualization.

Reconstructs the recursion tree from a DPLL trace: each branch/decision
is a node, conflicts are leaves (✗), the satisfying assignment is a
leaf (✓). Backtracks are drawn as dashed returns to the sibling branch.
The tree is rendered as an ASCII/Unicode panel that fills in as you
step through the trace.
"""
from __future__ import annotations


def build_tree(steps):
    """Walk a DPLL trace and return a nested tree structure.

    The recursion in dpll_trace looks like:
      branch   — "Branch 1: xV = True"        (creates the True child)
      backtrack — "...try xV = False"          (creates the False child)
      backtrack — "both values exhausted"      (marks node failed, pops)
      conflict — "this branch fails"           (marks current node failed)
      sat      — "all satisfied"               (marks current node ok)
    """
    root = {"var": None, "value": None, "children": [],
            "status": "pending", "step_at": 0, "done_at": None}
    stack = [root]  # stack[d] = node whose recursion is at depth d
    for idx, s in enumerate(steps):
        d = s.depth
        if s.kind == "branch":
            node = {"var": s.focus_var, "value": True, "children": [],
                    "status": "pending", "step_at": idx, "done_at": None}
            stack[min(d, len(stack) - 1)]["children"].append(node)
            stack = stack[:d + 1]
            stack.append(node)
        elif s.kind == "backtrack":
            if s.desc.startswith("x") and "led to a conflict" in s.desc:
                # "try xV = False": create the False sibling
                node = {"var": s.focus_var, "value": False, "children": [],
                        "status": "pending", "step_at": idx, "done_at": None}
                stack[min(d, len(stack) - 1)]["children"].append(node)
                stack = stack[:d + 1]
                stack.append(node)
            else:
                # both values exhausted: current node failed, pop it
                if len(stack) > 1:
                    stack[-1]["status"] = "failed"
                    stack[-1]["done_at"] = idx
                stack = stack[:max(d, 1)]
        elif s.kind == "conflict":
            if len(stack) > 1:
                stack[-1]["status"] = "failed"
                stack[-1]["done_at"] = idx
        elif s.kind == "sat":
            if len(stack) > 1:
                stack[-1]["status"] = "ok"
                stack[-1]["done_at"] = idx
            else:
                root["status"] = "ok"
                root["done_at"] = idx
    return root


def render_tree(root, upto_step, width=34):
    """Render the tree as it looks after `upto_step` steps.

    Nodes not yet created (step_at > upto_step) are hidden. Nodes whose
    status is only known later show as pending '?'. Returns list of lines.
    """
    lines = []
    has_children_shown = [False]

    def render(node, prefix, is_last, depth):
        if depth > 0 and node["step_at"] > upto_step:
            return
        if depth > 0:
            conn = "└─ " if is_last else "├─ "
            label = f"x{node['var']}={node['value'] and 'T' or 'F'}"
            pair = "open"
            # status as of upto_step
            if node["status"] == "ok" and (node["done_at"] or 10**9) <= upto_step:
                mark, pair = " ✓", "ok"
            elif node["status"] == "failed" and (node["done_at"] or 10**9) <= upto_step:
                mark, pair = " ✗", "failed"
            elif node["status"] != "pending":
                # status known but only later — still pending visually
                mark = " …"
            elif node["children"]:
                mark = ""
            else:
                mark = " …"
            lines.append((prefix + conn + label + mark, pair))
            prefix2 = prefix + ("   " if is_last else "│  ")
        else:
            prefix2 = prefix
        # children that exist so far
        kids = [k for k in node["children"] if k["step_at"] <= upto_step]
        for i, k in enumerate(kids):
            render(k, prefix2, i == len(kids) - 1, depth + 1)

    lines.append(("root", "root"))
    render(root, "", True, 0)
    return lines


def tree_summary(root, upto_step):
    """Counts for the header: nodes shown, failed, open."""
    counts = {"total": 0, "failed": 0, "ok": 0, "open": 0}

    def walk(node):
        if node["step_at"] > upto_step:
            return
        if node["status"] == "failed" and (node["done_at"] or 10**9) <= upto_step:
            counts["failed"] += 1
        elif node["status"] == "ok" and (node["done_at"] or 10**9) <= upto_step:
            counts["ok"] += 1
        else:
            counts["open"] += 1
        counts["total"] += 1
        for k in node["children"]:
            walk(k)

    walk(root)
    return counts
