#!/usr/bin/env bash
# Verification gate for the CausalInference library.
#
#   1. source scan for placeholders and trust escapes (comments and strings ignored)
#   2. every file under CausalInference/ is imported directly by CausalInference.lean
#   3. `lake build` succeeds with no warning from this project's files
#   4. `lake env lean scripts/AxiomCheck.lean` succeeds (only standard axioms are used)
#
# Usage: scripts/check.sh (from any directory). Exits nonzero if any step fails.
set -euo pipefail

cd "$(dirname "$0")/.."

read -r -d '' PY <<'EOF' || true
import pathlib, re, sys

# Identifiers rejected anywhere in code, with the reason printed on a hit.
BANNED = {
    "sorry": "sorry",
    "admit": "admit",
    "axiom": "axiom declaration",
    "unsafe": "unsafe",
    "native_decide": "native_decide",
    "implemented_by": "implemented_by",
    "extern": "extern",
    "ofReduceBool": "ofReduceBool",
    "skipKernelTC": "debug.skipKernelTC",
}
# Linters the lakefile may turn off, written without the `weak.` prefix.
LAKEFILE_LINTER_OFF_ALLOWED = {"linter.style.header"}

IDENT = re.compile(r"[^\W\d][\w'!?]*")
CHAR_LIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")
RAW_STR = re.compile(r'r(#*)"')
SET_OPTION_OFF = re.compile(r"\bset_option\s+([\w.'!?]+)\s+false\b")
TOML_LINTER_OFF = re.compile(r"(?<![\w.])(?:-D)?((?:\w+\.)*linter\.[\w.]*)\s*=\s*false\b")


class ScanError(Exception):
    pass


def strip_lean(src):
    """Blank out comments, docstrings, string and char literals, keeping offsets and newlines."""
    out = list(src)
    n = len(src)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    i = 0
    while i < n:
        c = src[i]
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if depth:
                raise ScanError(f"unterminated comment starting at offset {i}")
            blank(i, j)
            i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            if j >= n:
                raise ScanError(f"unterminated string starting at offset {i}")
            blank(i, j + 1)
            i = j + 1
        elif c == "'":
            m = CHAR_LIT.match(src, i)
            if m:
                blank(i, m.end())
                i = m.end()
            else:
                i += 1
        elif IDENT.match(src, i):
            m = RAW_STR.match(src, i)
            if m:
                close = '"' + m.group(1)
                j = src.find(close, m.end())
                if j < 0:
                    raise ScanError(f"unterminated raw string starting at offset {i}")
                blank(i, j + len(close))
                i = j + len(close)
            else:
                i = IDENT.match(src, i).end()
        else:
            i += 1
    return "".join(out)


def strip_toml(src):
    """Blank out `#` comments in TOML, keeping strings (they can carry Lean options)."""
    lines = []
    for line in src.split("\n"):
        quote, k = None, 0
        while k < len(line):
            ch = line[k]
            if quote:
                if ch == "\\" and quote == '"':
                    k += 1
                elif ch == quote:
                    quote = None
            elif ch in "\"'":
                quote = ch
            elif ch == "#":
                line = line[:k]
                break
            k += 1
        lines.append(line)
    return "\n".join(lines)


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def scan_code(path, code):
    hits = []
    for m in IDENT.finditer(code):
        if m.group() in BANNED:
            hits.append((line_of(code, m.start()), BANNED[m.group()]))
    if path.suffix == ".lean":
        for m in SET_OPTION_OFF.finditer(code):
            if "linter" in m.group(1).split("."):
                hits.append((line_of(code, m.start()), f"set_option {m.group(1)} false"))
    else:
        for m in TOML_LINTER_OFF.finditer(code):
            name = m.group(1).removeprefix("weak.")
            if name not in LAKEFILE_LINTER_OFF_ALLOWED:
                hits.append((line_of(code, m.start()), f"{m.group(1)} = false"))
    return sorted(hits)


def lean_files():
    return sorted(pathlib.Path("CausalInference").rglob("*.lean"))


def cmd_scan():
    paths = [pathlib.Path("CausalInference.lean"), *lean_files(), pathlib.Path("lakefile.toml")]
    bad = 0
    for p in paths:
        if not p.is_file():
            print(f"{p}: missing")
            bad += 1
            continue
        src = p.read_text(encoding="utf-8")
        try:
            code = strip_lean(src) if p.suffix == ".lean" else strip_toml(src)
        except ScanError as e:
            print(f"{p}: {e}")
            bad += 1
            continue
        for line, what in scan_code(p, code):
            print(f"{p}:{line}: rejected: {what}")
            bad += 1
    print(f"scanned {len(paths)} files, {bad} problems")
    return bad == 0


def cmd_imports():
    root = pathlib.Path("CausalInference.lean")
    if not root.is_file():
        print("CausalInference.lean: missing")
        return False
    code = strip_lean(root.read_text(encoding="utf-8"))
    imported = set(re.findall(
        r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.'!?]+)", code, re.M))
    missing = [p for p in lean_files() if ".".join(p.with_suffix("").parts) not in imported]
    for p in missing:
        print(f"{p}: not imported by CausalInference.lean")
    print(f"{len(lean_files())} library files, {len(missing)} not imported")
    return not missing


sys.exit(0 if {"scan": cmd_scan, "imports": cmd_imports}[sys.argv[1]]() else 1)
EOF

failed=()
build_failed=0

step() {
  local name=$1
  shift
  echo "==> $name"
  if "$@"; then
    echo "PASS: $name"
  else
    echo "FAIL: $name"
    failed+=("$name")
  fi
}

build_without_warnings() {
  local log status=0
  log=$(mktemp)
  lake build 2>&1 | tee "$log" || status=$?
  if [ "$status" -ne 0 ]; then
    build_failed=1
    rm -f "$log"
    return 1
  fi
  if grep -E 'warning:' "$log" | grep -E 'CausalInference(/|\.lean)' | grep -v '\.lake/'; then
    echo "the build printed warnings from project files (listed above)"
    rm -f "$log"
    return 1
  fi
  rm -f "$log"
}

step "1. source scan" python3 -c "$PY" scan
step "2. root imports every library file" python3 -c "$PY" imports
step "3. lake build without project warnings" build_without_warnings
if [ "$build_failed" -eq 1 ]; then
  # Without a fresh build the check would read stale .olean files.
  echo "==> 4. axiom check: skipped because lake build failed"
  failed+=("4. axiom check (skipped)")
else
  step "4. axiom check" lake env lean scripts/AxiomCheck.lean
fi

echo
if [ ${#failed[@]} -eq 0 ]; then
  echo "All checks passed."
else
  echo "Failed steps:"
  printf '  %s\n' "${failed[@]}"
  exit 1
fi
