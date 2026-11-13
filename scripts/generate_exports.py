#!/usr/bin/env python3
from pathlib import Path
from build_support import generate_exports
if __name__=='__main__': generate_exports(Path(__file__).resolve().parents[1])
