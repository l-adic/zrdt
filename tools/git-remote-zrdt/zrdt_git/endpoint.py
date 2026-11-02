"""Client for the desktop's local git endpoint (see ../ENDPOINT.md).

The endpoint is HTTP/1.1 with JSON bodies, on loopback TCP (``http://127.0.0.1:<port>``) or on a
Unix stream socket (``unix:/path/to/zrdt-apps.sock``). Every request carries the git app's token
as ``Authorization: Bearer <token>``.
"""

from __future__ import annotations

import base64
import hashlib
import http.client
import json
import os
import socket
import urllib.parse

from . import PROTOCOL


class EndpointError(Exception):
    """The endpoint could not be reached, or answered with an error (not a push refusal)."""


class Refused(Exception):
    """A push the desktop refused (status "refused"); ``info`` is the JSON reply."""

    def __init__(self, info: dict):
        super().__init__(info.get("message") or info.get("reason") or "refused")
        self.info = info

    @property
    def reason(self) -> str:
        return str(self.info.get("reason", ""))


class _UnixHTTPConnection(http.client.HTTPConnection):
    def __init__(self, path: str, timeout: float):
        super().__init__("localhost", timeout=timeout)
        self._unix_path = path

    def connect(self) -> None:
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.settimeout(self.timeout)
        s.connect(self._unix_path)
        self.sock = s


def b64(data: bytes) -> str:
    return base64.b64encode(data).decode("ascii")


def unb64(text: str) -> bytes:
    return base64.b64decode(text.encode("ascii"), validate=True)


class Endpoint:
    def __init__(self, base: str, token: str, timeout: float = 600.0):
        self.base = base
        self.token = token
        self.timeout = timeout
        if base.startswith("unix:"):
            self._unix = base[len("unix:"):]
            self._host = None
        else:
            u = urllib.parse.urlsplit(base)
            if u.scheme != "http" or not u.hostname:
                raise EndpointError("zrdt endpoint must be http://127.0.0.1:<port> or unix:<path>, got %r" % base)
            if u.hostname not in ("127.0.0.1", "localhost", "::1"):
                raise EndpointError("zrdt endpoint must be on loopback, got %r" % u.hostname)
            self._unix = None
            self._host = (u.hostname, u.port or 80)
        self._hello: dict | None = None

    # -- transport --------------------------------------------------------------------------

    def _conn(self) -> http.client.HTTPConnection:
        if self._unix is not None:
            return _UnixHTTPConnection(self._unix, self.timeout)
        return http.client.HTTPConnection(self._host[0], self._host[1], timeout=self.timeout)

    def call(self, method: str, path: str, body: dict | None = None) -> tuple[int, dict]:
        data = None if body is None else json.dumps(body, separators=(",", ":")).encode("utf-8")
        headers = {"Authorization": "Bearer " + self.token, "Accept": "application/json",
                   "X-Zrdt-Protocol": str(PROTOCOL)}
        if data is not None:
            headers["Content-Type"] = "application/json"
        conn = self._conn()
        try:
            conn.request(method, path, body=data, headers=headers)
            resp = conn.getresponse()
            raw = resp.read()
            status = resp.status
        except (OSError, http.client.HTTPException) as e:
            raise EndpointError("cannot reach the zrdt desktop at %s (is Signal running?): %s" % (self.base, e))
        finally:
            conn.close()
        try:
            reply = json.loads(raw.decode("utf-8")) if raw else {}
        except ValueError:
            raise EndpointError("the zrdt desktop sent a reply that is not JSON (HTTP %d)" % status)
        if not isinstance(reply, dict):
            raise EndpointError("the zrdt desktop sent a reply that is not a JSON object")
        if status == 409 and reply.get("status") == "refused":
            return status, reply
        if status >= 400:
            raise EndpointError("zrdt desktop: %s (HTTP %d %s)" % (reply.get("message", "error"), status,
                                                                reply.get("error", "")))
        return status, reply

    # -- API --------------------------------------------------------------------------------

    @staticmethod
    def repo_path(group: str, repo: str) -> str:
        return "/v1/git/%s/%s" % (urllib.parse.quote(group, safe=""), urllib.parse.quote(repo, safe=""))

    def hello(self) -> dict:
        if self._hello is None:
            _, h = self.call("GET", "/v1/hello")
            if h.get("protocol") != PROTOCOL or h.get("objectFormat") != "sha256":
                raise EndpointError("the zrdt desktop speaks endpoint protocol %r (%r); this helper needs %d (sha256)"
                                    % (h.get("protocol"), h.get("objectFormat"), PROTOCOL))
            self._hello = h
        return self._hello

    def state(self, group: str, repo: str) -> dict:
        _, s = self.call("GET", self.repo_path(group, repo))
        return s

    def upload(self, group: str, repo: str, stream: bytes) -> str | None:
        """Hand the raw-object stream to the desktop in pieces; return the upload id."""
        if not stream:
            return None
        h = self.hello()
        if len(stream) > int(h.get("maxStream", 0)):
            raise EndpointError("this push carries %d bytes of objects; the limit is %d (chains are not in M1)"
                                % (len(stream), int(h.get("maxStream", 0))))
        _, u = self.call("POST", self.repo_path(group, repo) + "/uploads", {"size": len(stream)})
        size = int(u["pieceSize"])
        count = int(u["pieces"])
        if size <= 0 or count != (len(stream) + size - 1) // size:
            raise EndpointError("the zrdt desktop proposed an inconsistent piece layout")
        for i in range(count):
            piece = stream[i * size:(i + 1) * size]
            self.call("PUT", "%s/uploads/%s/pieces/%d" % (self.repo_path(group, repo),
                                                          urllib.parse.quote(u["upload"], safe=""), i),
                      {"sha256": hashlib.sha256(piece).hexdigest(), "data": b64(piece)})
        return u["upload"]

    def push(self, group: str, repo: str, request: dict) -> dict:
        """Publish (or dry-run) a push record. Raises Refused on a refusal."""
        _, r = self.call("POST", self.repo_path(group, repo) + "/pushes", request)
        if r.get("status") == "refused":
            raise Refused(r)
        if r.get("status") != "ok":
            raise EndpointError("the zrdt desktop answered a push with status %r" % r.get("status"))
        return r

    def objects(self, group: str, repo: str, ids: list[str]) -> tuple[dict[str, bytes], list[str]]:
        """Fetch raw objects by id, in batches; return ({id: raw}, missing ids)."""
        h = self.hello()
        batch = max(1, int(h.get("maxObjectsPerRequest", 256)))
        got: dict[str, bytes] = {}
        missing: list[str] = []
        for i in range(0, len(ids), batch):
            part = ids[i:i + batch]
            _, r = self.call("POST", self.repo_path(group, repo) + "/objects", {"ids": part})
            asked = set(part)
            for o in r.get("objects", []):
                oid = o.get("id")
                if oid not in asked or oid in got:
                    raise EndpointError("the zrdt desktop sent object %r, which was not asked for" % (oid,))
                got[oid] = unb64(o["raw"])
            missing.extend(m for m in r.get("missing", []) if m in asked)
        return got, missing


def resolve(git_config_get) -> Endpoint:
    """Find the endpoint and token: environment first, then git config.

    ZRDT_ENDPOINT / zrdt.endpoint, ZRDT_TOKEN / zrdt.token, ZRDT_TOKEN_FILE / zrdt.tokenFile.
    """
    base = os.environ.get("ZRDT_ENDPOINT") or git_config_get("zrdt.endpoint")
    if not base:
        raise EndpointError("no zrdt desktop endpoint: set ZRDT_ENDPOINT or `git config zrdt.endpoint` "
                            "(http://127.0.0.1:<port> or unix:<path>)")
    token = os.environ.get("ZRDT_TOKEN") or git_config_get("zrdt.token")
    if not token:
        path = os.environ.get("ZRDT_TOKEN_FILE") or git_config_get("zrdt.tokenFile")
        if path:
            try:
                with open(os.path.expanduser(path), "r", encoding="utf-8") as f:
                    token = f.read().strip()
            except OSError as e:
                raise EndpointError("cannot read the zrdt token file %s: %s" % (path, e))
    if not token:
        raise EndpointError("no zrdt token: set ZRDT_TOKEN, `git config zrdt.token` or `git config zrdt.tokenFile`")
    return Endpoint(base, token)
