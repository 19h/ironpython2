#!/usr/bin/env ipy
"""Read IronPython cached-code metadata without executing the cached modules.

The input is one absolute assembly path per line on standard input.  The output
is one JSON object per line on standard output.  This script is intentionally
compatible with IronPython 2.7 because the assemblies reconstructed by
``Util/reconstruct_eas.py`` target IronPython 2.7.12.
"""

from __future__ import print_function

import json
import os
import sys

import System
from System.Reflection import Assembly, AssemblyName


def text(value):
    if value is None:
        return None
    return str(value)


def attribute_names(method):
    for attribute in method.GetCustomAttributes(False):
        if attribute.GetType().FullName == (
                "Microsoft.Scripting.Runtime.CachedOptimizedCodeAttribute"):
            return [text(name) for name in attribute.Names]
    return []


def inspect(path):
    result = {
        "path": path,
        "reflection_ok": False,
        "assembly_full_name": None,
        "assembly_name": None,
        "assembly_version": None,
        "dlr_cached_code": False,
        "cached_languages": [],
        "cached_modules": [],
        "error": None,
    }

    try:
        identity = AssemblyName.GetAssemblyName(path)
        result["assembly_full_name"] = text(identity.FullName)
        result["assembly_name"] = text(identity.Name)
        result["assembly_version"] = text(identity.Version)

        # PE32+ images in this corpus deliberately declare AMD64 and therefore
        # cannot be loaded into an arm64 process.  Cached IronPython assemblies
        # contain this generated type name in the metadata string heap and are
        # AnyCPU PE32 images; avoid loading every conventional assembly merely
        # to prove the generated type is absent.
        with open(path, "rb") as stream:
            if b"DLRCachedCode" not in stream.read():
                result["reflection_ok"] = True
                return result

        assembly = Assembly.LoadFile(path)
        cached_type = assembly.GetType("DLRCachedCode", False, False)
        if cached_type is None:
            result["reflection_ok"] = True
            return result

        result["dlr_cached_code"] = True
        if cached_type.TypeInitializer is not None:
            raise RuntimeError(
                "DLRCachedCode has a static initializer; refusing invocation")
        method = cached_type.GetMethod("GetScriptCodeInfo")
        if method is None:
            raise RuntimeError("DLRCachedCode.GetScriptCodeInfo is absent")

        has_marker = any(
            attr.GetType().FullName ==
            "Microsoft.Scripting.Runtime.DlrCachedCodeAttribute"
            for attr in method.GetCustomAttributes(False)
        )
        if not has_marker:
            raise RuntimeError("GetScriptCodeInfo lacks DlrCachedCodeAttribute")

        # The generated method only constructs arrays of Type, Delegate, and
        # string.  It does not invoke any cached module delegate.
        info = method.Invoke(None, None)
        language_types = info.Item000
        delegates = info.Item001
        source_paths = info.Item002
        custom_data = info.Item003

        for language_index in range(language_types.Length):
            language_name = text(language_types[language_index].FullName)
            result["cached_languages"].append(language_name)

            if delegates[language_index].Length != source_paths[language_index].Length:
                raise RuntimeError("delegate/source-path cardinality mismatch")
            if delegates[language_index].Length != custom_data[language_index].Length:
                raise RuntimeError("delegate/custom-data cardinality mismatch")

            for module_index in range(delegates[language_index].Length):
                delegate = delegates[language_index][module_index]
                result["cached_modules"].append({
                    "language": language_name,
                    "source_path": text(source_paths[language_index][module_index]),
                    "module_name": text(custom_data[language_index][module_index]),
                    "delegate_method": text(delegate.Method.Name),
                    "delegate_metadata_token": int(delegate.Method.MetadataToken),
                    "global_names": attribute_names(delegate.Method),
                })

        result["reflection_ok"] = True
    except Exception as error:
        result["error"] = "%s: %s" % (error.GetType().FullName, text(error)) \
            if isinstance(error, System.Exception) else \
            "%s: %s" % (type(error).__name__, text(error))

    return result


def main():
    for raw_path in sys.stdin:
        path = os.path.abspath(raw_path.rstrip("\r\n"))
        if not path:
            continue
        print(json.dumps(inspect(path), sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
