#!/usr/bin/env ipy
"""Compile recovered sources with the exact IronPython interpreter in use."""

from __future__ import print_function

import json
import os
import sys


def main(root):
    paths = []
    for directory, _, names in os.walk(root):
        for name in names:
            if name.endswith(".py"):
                paths.append(os.path.join(directory, name))
    failures = []
    for path in sorted(paths):
        try:
            stream = open(path, "rb")
            try:
                source = stream.read()
            finally:
                stream.close()
            compile(source, path, "exec", 0, True)
        except Exception as error:
            failure = {
                "path": path,
                "type": type(error).__name__,
                "error": str(error),
            }
            for name in ("lineno", "offset", "text"):
                value = getattr(error, name, None)
                if value is not None:
                    failure[name] = value
            failures.append(failure)
    result = {
        "interpreter": sys.version,
        "sources": len(paths),
        "compile_failures": failures,
    }
    print(json.dumps(result, sort_keys=True))
    return 0 if not failures else 1


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_recovered_python.py SOURCE_ROOT")
    raise SystemExit(main(os.path.abspath(sys.argv[1])))
