"""Raw canonical git objects for SHA-256 repositories.

A raw object is ``b"<type> <decimal length>\\0" + content``; its id is SHA-256(raw), which is the
object id in a SHA-256 repository. No zlib, no pack: this is the form zrdt pieces carry
(BUILD_M1 §4.1), so the desktop's zrdtd can recompute every id.

The checks here mirror BUILD_M1 §4.1's ``checkObjects`` (the Lean version is authoritative once
it exists): commit, tree and blob only; a commit header allow-list (tree, parent*, author,
committer, optional encoding), so gpgsig, mergetag and unknown headers are refused; no gitlinks.
"""

from __future__ import annotations

import hashlib
import re

OID_HEX = re.compile(r"^[0-9a-f]{64}$")
OID_LEN = 32
KINDS = ("commit", "tree", "blob")
TREE_MODES = {b"100644": "blob", b"100755": "blob", b"120000": "blob", b"40000": "tree"}
GITLINK_MODE = b"160000"


class ObjectError(Exception):
    """A raw object, or a stream of them, is not acceptable."""

    def __init__(self, message: str, oid: str | None = None):
        super().__init__(message)
        self.oid = oid


def is_oid(s: object) -> bool:
    return isinstance(s, str) and OID_HEX.match(s) is not None


def object_id(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def make_raw(kind: str, content: bytes) -> bytes:
    if kind not in KINDS and kind != "tag":
        raise ObjectError("unknown object type %r" % kind)
    return kind.encode("ascii") + b" " + str(len(content)).encode("ascii") + b"\0" + content


def _parse_header(buf: bytes, start: int) -> tuple[str, int, int]:
    """Parse ``<type> <len>\\0`` at buf[start:]; return (kind, content start, content length)."""
    sp = buf.find(b" ", start, start + 8)
    if sp < 0:
        raise ObjectError("malformed object header")
    kind_b = buf[start:sp]
    try:
        kind = kind_b.decode("ascii")
    except UnicodeDecodeError:
        raise ObjectError("malformed object type")
    if kind == "tag":
        raise ObjectError("tag objects are not supported (lightweight tags only)")
    if kind not in KINDS:
        raise ObjectError("unknown object type %r" % kind)
    nul = buf.find(b"\0", sp + 1, sp + 1 + 21)
    if nul < 0:
        raise ObjectError("malformed object length")
    digits = buf[sp + 1:nul]
    if not digits or not digits.isdigit() or (len(digits) > 1 and digits[:1] == b"0"):
        raise ObjectError("malformed object length")
    return kind, nul + 1, int(digits)


def split_raw(raw: bytes) -> tuple[str, bytes]:
    """Split one raw object into (kind, content); the declared length must be exact."""
    kind, body, length = _parse_header(raw, 0)
    if len(raw) - body != length:
        raise ObjectError("object length does not match its header")
    return kind, raw[body:]


def parse_commit(content: bytes) -> tuple[str, list[str]]:
    """Return (tree, parents). Refuse any header outside the allow-list, and continuation lines."""
    end = content.find(b"\n\n")
    header = content if end < 0 else content[:end]
    if end < 0:
        raise ObjectError("commit has no message separator")
    lines = header.split(b"\n")
    tree = None
    parents: list[str] = []
    state = 0  # 0 expect tree, 1 parents, 2 after author, 3 after committer, 4 after encoding
    for line in lines:
        key, _, value = line.partition(b" ")
        if key == b"tree" and state == 0:
            tree = _hex_oid(value, "commit tree")
            state = 1
        elif key == b"parent" and state == 1:
            parents.append(_hex_oid(value, "commit parent"))
        elif key == b"author" and state == 1:
            state = 2
        elif key == b"committer" and state == 2:
            state = 3
        elif key == b"encoding" and state == 3:
            state = 4
        else:
            name = key.decode("utf-8", "replace") or "(continuation line)"
            raise ObjectError("commit header %r is not allowed (no signatures, no extra headers)" % name)
    if state < 3 or tree is None:
        raise ObjectError("commit lacks tree, author or committer")
    if len(set(parents)) != len(parents):
        raise ObjectError("commit repeats a parent")
    return tree, parents


def _hex_oid(value: bytes, what: str) -> str:
    try:
        s = value.decode("ascii")
    except UnicodeDecodeError:
        raise ObjectError("%s is not an object id" % what)
    if not is_oid(s):
        raise ObjectError("%s is not a SHA-256 object id" % what)
    return s


def parse_tree(content: bytes) -> list[tuple[str, str, bytes]]:
    """Return [(kind, oid, name)] for a tree; refuse gitlinks and malformed entries."""
    out = []
    i = 0
    n = len(content)
    while i < n:
        sp = content.find(b" ", i, i + 7)
        if sp < 0:
            raise ObjectError("malformed tree entry mode")
        mode = content[i:sp]
        if mode == GITLINK_MODE:
            raise ObjectError("gitlink (submodule) entries are not supported")
        kind = TREE_MODES.get(mode)
        if kind is None:
            raise ObjectError("tree entry mode %r is not supported" % mode.decode("ascii", "replace"))
        nul = content.find(b"\0", sp + 1)
        if nul < 0 or nul + 1 + OID_LEN > n:
            raise ObjectError("truncated tree entry")
        name = content[sp + 1:nul]
        if not name or b"/" in name or name in (b".", b".."):
            raise ObjectError("bad tree entry name")
        oid = content[nul + 1:nul + 1 + OID_LEN].hex()
        out.append((kind, oid, name))
        i = nul + 1 + OID_LEN
    return out


def references(kind: str, content: bytes) -> list[str]:
    """Ids an object names: a commit's tree and parents, a tree's entries; a blob names none."""
    if kind == "commit":
        tree, parents = parse_commit(content)
        return [tree] + parents
    if kind == "tree":
        return [oid for (_, oid, _) in parse_tree(content)]
    return []


def check_object(kind: str, content: bytes) -> None:
    """Refuse an object the zrdt checks would refuse (parse commits and trees fully)."""
    if kind == "commit":
        parse_commit(content)
    elif kind == "tree":
        parse_tree(content)
    elif kind != "blob":
        raise ObjectError("object type %r is not supported" % kind)


def check_stream(stream: bytes) -> list[tuple[str, str, int, int]]:
    """Walk a stream of raw objects; return [(oid, kind, offset, length)].

    The stream must be raw objects back to back, strictly increasing by id, each a well-formed
    commit, tree or blob. Every id is recomputed here.
    """
    out = []
    pos = 0
    last = ""
    while pos < len(stream):
        kind, body, length = _parse_header(stream, pos)
        end = body + length
        if end > len(stream):
            raise ObjectError("stream ends inside an object")
        raw = stream[pos:end]
        oid = object_id(raw)
        try:
            check_object(kind, stream[body:end])
        except ObjectError as e:
            raise ObjectError(str(e), oid)
        if oid <= last:
            raise ObjectError("objects are not strictly increasing by id", oid)
        out.append((oid, kind, pos, end - pos))
        last = oid
        pos = end
    return out


# ---------------------------------------------------------------------------------------------
# Ref names (GIT_PLAN §2.3 validRefName, narrowed for M1: refs/heads and refs/tags only).

_BAD_REF_BYTES = set(b"~^:?*[\\") | set(range(0, 0x21)) | {0x7F}


def ref_name_problem(name: str) -> str | None:
    """Return why a ref name is refused, or None if it is acceptable."""
    if not isinstance(name, str):
        return "not a string"
    try:
        b = name.encode("utf-8")
    except UnicodeEncodeError:
        return "not UTF-8"
    if not (name.startswith("refs/heads/") or name.startswith("refs/tags/")):
        return "only refs/heads/* and refs/tags/* are supported"
    if len(b) > 255:
        return "longer than 255 bytes"
    if ".zrdt-" in name:
        return "names containing .zrdt- are reserved for diverged branches"
    if any(c in _BAD_REF_BYTES for c in b):
        return "contains a space, a control character or one of ~^:?*[\\"
    if ".." in name or "@{" in name or "//" in name:
        return "contains .., @{ or //"
    if name.endswith("/") or name.endswith("."):
        return "ends with / or ."
    for comp in name.split("/"):
        if not comp:
            return "has an empty component"
        if comp.startswith("."):
            return "has a component starting with ."
        if comp.endswith(".lock"):
            return "has a component ending in .lock"
    return None


def valid_ref_name(name: str) -> bool:
    return ref_name_problem(name) is None


# Group aliases and repository names in zrdt::<group>/<repo>.
_REPO_RE = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9._-]{0,63}$")


def repo_name_problem(name: str) -> str | None:
    if not _REPO_RE.match(name) or name.endswith(".lock"):
        return "a repository name is 1-64 characters of A-Z a-z 0-9 . _ -, not starting with . or -"
    return None


def group_name_problem(name: str) -> str | None:
    b = name.encode("utf-8", "surrogateescape")
    if not (1 <= len(b) <= 64):
        return "a group alias is 1-64 bytes"
    if "/" in name or any(ord(c) < 0x20 or ord(c) == 0x7F for c in name) or name != name.strip():
        return "a group alias has no '/', no control character and no outer spaces"
    return None
