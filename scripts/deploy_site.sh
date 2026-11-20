#!/usr/bin/env bash
# Publishes dist/ (scripts/build_site.py's) to the orphan `gh-pages` branch on GitHub Pages, as a single
# root commit whose message is dist/VERSION's line:
#   scripts/deploy_site.sh [REMOTE]
# It refuses a dist/ without VERSION, one built from a tree with uncommitted changes, one built with
# --stale-ok (VERSION says both), and one without 404.html or .nojekyll.
set -euo pipefail
cd "$(dirname "$0")/.."
die() { echo "deploy_site.sh: $*" >&2; exit 1; }
[ -f dist/VERSION ] || die "no dist/VERSION: build the site first (scripts/build_site.py, README.md)"
version=$(head -n 1 dist/VERSION)
case "$version" in
  "ecma-formal "*) ;;
  *) die "dist/VERSION is not a build's stamp: $version" ;;
esac
case "$version" in
  *"with uncommitted changes"*) die "dist/ was built from a tree with uncommitted changes ($version): commit, then build again" ;;
esac
case "$version" in
  *"stale"*) die "dist/ was built with --stale-ok ($version): build the Lean products (lake build), then the site again" ;;
esac
[ -f dist/404.html ] || die "no dist/404.html: build the site again"
[ -f dist/.nojekyll ] || die "no dist/.nojekyll: build the site again"
remote="${1:-origin}"
tmp_idx=$(mktemp "${TMPDIR:-/tmp}/gh-pages-index.XXXXXX")
trap 'rm -f "$tmp_idx"' EXIT
rm -f "$tmp_idx"
GIT_INDEX_FILE="$tmp_idx" git --work-tree=dist add -A
tree=$(GIT_INDEX_FILE="$tmp_idx" git write-tree)
commit=$(git commit-tree "$tree" -m "$version")
git push --force "$remote" "$commit:refs/heads/gh-pages"
