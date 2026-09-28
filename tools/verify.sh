#!/bin/sh
# Everything CI checks, locally, before a push.
#   tools/verify.sh [calamine tests dir] [python with openpyxl and python-calamine] [node_modules with xlsx]
set -e
lake build
lake exe xlsxlean write out/example.xlsx > /dev/null
lake exe xlsxlean check out/example.xlsx > /dev/null
rm -rf out/lab
lake exe xlsxlean lab out/lab 300
if [ -n "$1" ]; then
  lake exe xlsxlean check --json "$1"/*.xlsx > out/calamine.json || true
  python3 tools/summarize_checks.py out/calamine.json --expect-files 66 --expect-unreadable 2 --expect-pass 62
fi
if [ -n "$2" ] && [ -n "$3" ]; then
  "$2" tools/differential.py out/lab --sheetjs "$3" --json out/lab/results.json | tail -6
fi
