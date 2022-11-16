#!/bin/bash
set -e

if [ -f "$1" ]; then
  clear
  agda "$1" && echo "** OK **" || true
else
  echo "usage:" 2>&1
  echo "  $0 FILE.agda" 2>&1
  false
fi
