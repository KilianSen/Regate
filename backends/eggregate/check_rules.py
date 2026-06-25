#!/usr/bin/env python
"""CI gate: fail the build if any rewrite rule is unsound.

    python check_rules.py [trials]

Exits 0 if every rule in the catalogue is a sound, definedness-preserving
equality (under its guards); non-zero with a counterexample otherwise.
"""
from eggregate.audit import main

if __name__ == "__main__":
    raise SystemExit(main())
