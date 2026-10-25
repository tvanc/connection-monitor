#!/bin/bash
# Double-click to start monitoring. Close this window (or press q / Ctrl+C) to stop.
cd "$(dirname "$0")" || exit 1

# The full-screen dashboard needs the 'rich' package. Install it once into a private
# folder (.venv) next to this script, so nothing system-wide is touched.
PY=python3
[ -x .venv/bin/python ] || python3 -m venv .venv >/dev/null 2>&1
if [ -x .venv/bin/python ]; then
    PY=.venv/bin/python
    "$PY" -c "import rich" 2>/dev/null || {
        echo "Installing the 'rich' display package (one time only)..."
        "$PY" -m pip install --quiet rich || echo "Couldn't install it; using the plain display."
    }
fi

"$PY" main.py
echo
read -n 1 -s -r -p "Press any key to close this window."
