#!/bin/bash
set -e

if [ -f "$1" ]; then
  ./check_file.sh "$1"
  fswatcher --path "$1" -- ./check_file.sh "$1"
else
  echo "usage:" 2>&1
  echo "  $0 FILE.agda" 2>&1
fi
