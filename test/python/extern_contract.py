"""Host contract used to test direct Sail extern linkage."""

from __future__ import annotations


def reset() -> None:
    pass


def finish() -> None:
    pass


def python_missing_host_value() -> int:
    return 41


def c_host_value() -> int:
    return 73


def python_missing_host_pair() -> None:
    return None
