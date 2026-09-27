#!/bin/sh
set -eu
repo_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
fetch_cache=false
case "${1:-}" in
  "") ;;
  --fetch-cache) fetch_cache=true ;;
  *) echo "Usage: sh build_all.sh [--fetch-cache]" >&2; exit 2 ;;
esac
for project in existence_ms ms existence_ks ks existence_higher_rank_ks higher_rank_ks; do
  echo "Building $project"
  if "$fetch_cache"; then
    sh "$repo_dir/$project/run_lake.sh" exe cache get
  fi
  sh "$repo_dir/$project/run_lake.sh" build
done
