"""git-remote-zrdt: a git remote helper for zrdt channels (SHA-256 repositories only).

Modules:
  objects    raw canonical git objects, ids, the commit-header allow-list, ref names
  endpoint   the client for the desktop's local JSON endpoint (ENDPOINT.md)
  gitcmd     the git plumbing the helper uses (cat-file, hash-object, rev-list)
  helper     the remote-helper protocol (git-remote-zrdt)
  porcelain  git zrdt log | status | share
"""

PROTOCOL = 1
APP = "git-sha256"
