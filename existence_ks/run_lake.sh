#!/bin/sh
set -eu
project_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$project_dir"
if ! command -v lake >/dev/null 2>&1; then
  echo "Lake not found. Install elan (https://github.com/leanprover/elan) and add its bin directory to PATH." >&2
  exit 127
fi
exec lake "$@"
