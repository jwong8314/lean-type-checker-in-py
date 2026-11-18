"""Generate the student package `kernel/` from the reference `solution/kernel/`.

Everything between `# BEGIN SOLUTION` and `# END SOLUTION` is removed:

- inside a function, it becomes `raise NotImplementedError(...)`;
- at class or module level (a block of helper functions), it becomes a comment.

Run from the repository root:

    python3 tools/make_template.py            # refuses to overwrite existing work
    python3 tools/make_template.py --force
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "solution" / "kernel"
TARGET = ROOT / "kernel"


def strip_solutions(text: str) -> str:
    out: list[str] = []
    lines = text.splitlines()
    function = "this function"
    i = 0
    while i < len(lines):
        line = lines[i]
        definition = re.match(r"\s*def (\w+)", line)
        if definition:
            function = definition.group(1)
        if line.strip() != "# BEGIN SOLUTION":
            out.append(line)
            i += 1
            continue
        indent = line[: len(line) - len(line.lstrip())]
        end = next(j for j in range(i, len(lines)) if lines[j].strip() == "# END SOLUTION")
        body = [body_line for body_line in lines[i + 1 : end] if body_line.strip()]
        if body and body[0].lstrip().startswith("def "):
            out.append(f"{indent}# (Add helper functions here as you need them.)")
        else:
            out.append(f'{indent}raise NotImplementedError("TODO: {function}")')
        i = end + 1
    return "\n".join(out) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--force", action="store_true", help="overwrite an existing kernel/ directory")
    args = parser.parse_args()
    if TARGET.exists() and not args.force:
        sys.exit(f"{TARGET} already exists; pass --force to overwrite it")
    TARGET.mkdir(exist_ok=True)
    for source in sorted(SOURCE.glob("*.py")):
        (TARGET / source.name).write_text(strip_solutions(source.read_text()))
        print(f"wrote kernel/{source.name}")


if __name__ == "__main__":
    main()
