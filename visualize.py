#!/usr/bin/env python3
"""Launch the SAT solver visualizer.

Usage: python3 visualize.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from tui.viz import entry

if __name__ == "__main__":
    entry()
