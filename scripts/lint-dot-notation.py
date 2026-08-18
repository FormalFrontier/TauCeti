#!/usr/bin/env python3
"""Command-line wrapper for the shared Lean source parser's dot-notation lint."""

from lean_source import (
    find_violations,
    main,
    own_declaration_paths,
    strip_comments_and_strings,
)


if __name__ == "__main__":
    raise SystemExit(main())
