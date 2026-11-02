#!/usr/bin/env python3
"""Call the endpoint directly: call.py METHOD PATH [JSON-BODY]. Uses ZRDT_ENDPOINT and ZRDT_TOKEN
(the admin token for /fake/... calls). Prints the JSON reply; exit 0 on 2xx and on a 409 refusal."""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
from zrdt_git.endpoint import Endpoint, EndpointError  # noqa: E402


def main() -> int:
    method, path = sys.argv[1], sys.argv[2]
    body = json.loads(sys.argv[3]) if len(sys.argv) > 3 else None
    ep = Endpoint(os.environ["ZRDT_ENDPOINT"], os.environ["ZRDT_TOKEN"])
    try:
        _, reply = ep.call(method, path, body)
    except EndpointError as e:
        print(json.dumps({"error": str(e)}))
        return 1
    print(json.dumps(reply, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
