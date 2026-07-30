#!/usr/bin/env python3
"""Executable and differential tests for the Sail Python backend."""

from __future__ import annotations

import argparse
import ast
import builtins
import dataclasses
import difflib
import importlib.util
import inspect
import os
from pathlib import Path
import re
import shlex
import subprocess
import symtable
import sys
import tempfile
import types
import typing
from typing import Any, Callable


sys.dont_write_bytecode = True


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DEFAULT_SAIL = ROOT / "_build/default/src/bin/sail.exe"
DEFAULT_PLUGIN = ROOT / "_build/default/src/sail_python_backend/sail_plugin_python.cmxs"
SOURCE_GOLDEN_NAMES = (
    "Pair",
    "MaybeByte",
    "NoByte",
    "SomeByte",
    "Traffic",
    "sum_bits",
    "update_pair",
    "pair_pattern_score",
    "head_or",
    "first_at_least",
)


def command(
    args: list[str],
    *,
    cwd: Path = ROOT,
    extra_env: dict[str, str] | None = None,
    expect_success: bool = True,
) -> subprocess.CompletedProcess[str]:
    print("+", shlex.join(args))
    environment = os.environ.copy()
    environment.setdefault("SAIL_DIR", str(ROOT))
    if extra_env:
        environment.update(extra_env)
    result = subprocess.run(args, cwd=cwd, env=environment, capture_output=True, text=True)
    if expect_success and result.returncode != 0:
        raise RuntimeError(
            f"command exited with status {result.returncode}: {shlex.join(args)}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    if not expect_success and result.returncode == 0:
        raise RuntimeError(f"command unexpectedly succeeded: {shlex.join(args)}")
    return result


def import_file(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import generated module {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def import_package(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(
        name,
        path / "__init__.py",
        submodule_search_locations=[str(path)],
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import generated package {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def sail_format(module: Any, value: Any) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, module.Bits):
        digits = max(1, (value.width + 3) // 4)
        return f"0x{value.value:0{digits}X}"
    return str(value)


def oracle_values(module: Any) -> list[str]:
    bits = module.Bits
    module.reset()
    values = [
        module.sum_int(2, 3),
        module.sum_int(10**30, 7),
        module.sum_bits(bits(8, 0xFF), bits(8, 0x01)),
        module.sum_bits(bits(8, 0xFE), bits(8, 0x05)),
        module.shift_left(bits(8, 0x81), 1),
        module.shift_right(bits(8, 0x81), 1),
        module.shift_right_arithmetic(bits(8, 0x81), 1),
        module.concat_bits(bits(4, 0xA), bits(4, 0x5)),
        module.low_nibble(bits(8, 0xAB)),
        module.signed_byte(bits(8, 0xFF)),
        module.add_integer_to_byte(bits(8, 0xFF), 2),
        module.high_nibble(bits(8, 0xAB)),
        module.byte_leading_zeros(bits(8, 0x0F)),
        module.byte_trailing_zeros(bits(8, 0x30)),
        module.choose(True, 17, 99),
        module.triangular(4),
        module.vector_pick([bits(8, 0x10), bits(8, 0x20), bits(8, 0x30), bits(8, 0x40)]),
        module.record_update_score(),
        module.traffic_score(module.Traffic.Ready),
        module.guarded_score(12),
        module.guarded_score(4),
        module.head_or([7, 8], 99),
        module.head_or([], 99),
        module.count_while(4),
        module.count_until(3),
        module.first_at_least(10, 4),
        module.require_nonnegative(6),
        module.catches_exception(),
        module.bump_counter(3),
        module.bump_counter(4),
    ]
    return [sail_format(module, value) for value in values]


def assert_lines(label: str, actual: list[str], expected: list[str]) -> None:
    if actual == expected:
        return
    diff = "\n".join(
        difflib.unified_diff(expected, actual, fromfile=f"{label}.expected", tofile=f"{label}.actual", lineterm="")
    )
    raise AssertionError(f"{label} differs:\n{diff}")


def expect_raises(exception: type[BaseException], call: Callable[[], Any]) -> BaseException:
    try:
        call()
    except exception as error:
        return error
    raise AssertionError(f"expected {exception.__name__}")


def generated_modules(module: Any, objects: dict[str, Any]) -> set[types.ModuleType]:
    modules = {module}
    namespace = module.__name__
    for value in objects.values():
        owner = inspect.getmodule(value)
        if owner is not None and (owner.__name__ == namespace or owner.__name__.startswith(namespace + ".")):
            modules.add(owner)
    return modules


def undefined_name_checks(modules: set[types.ModuleType]) -> None:
    failures: list[str] = []
    builtin_names = set(dir(builtins))
    for module in sorted(modules, key=lambda item: item.__name__):
        source_path = Path(getattr(module, "__file__", None) or "")
        if not source_path.is_file():
            continue
        source = source_path.read_text()
        table = symtable.symtable(source, str(source_path), "exec")
        module_names = set(module.__dict__) | {
            symbol.get_name()
            for symbol in table.get_symbols()
            if symbol.is_assigned() or symbol.is_imported() or symbol.is_namespace()
        }

        def visit(scope: symtable.SymbolTable) -> None:
            if scope is not table:
                for symbol in scope.get_symbols():
                    name = symbol.get_name()
                    if symbol.is_referenced() and symbol.is_global() and name not in module_names | builtin_names:
                        failures.append(f"{module.__name__}:{scope.get_name()}: undefined global {name}")
            for child in scope.get_children():
                visit(child)

        visit(table)
    assert not failures, "generated code contains unresolved names:\n" + "\n".join(failures)


def annotation_checks(module: Any) -> None:
    objects = {
        **module.__sail_functions__,
        **module.__sail_types__,
    }
    modules = generated_modules(module, objects)
    undefined_name_checks(modules)

    failures: list[str] = []
    for owner in sorted(modules, key=lambda item: item.__name__):
        try:
            typing.get_type_hints(owner, include_extras=True)
        except Exception as error:  # Report every generated module in one failure.
            failures.append(f"module {owner.__name__}: {type(error).__name__}: {error}")
    for sail_name, value in sorted(objects.items()):
        if not (inspect.isfunction(value) or inspect.isclass(value)):
            continue
        try:
            typing.get_type_hints(value, include_extras=True)
        except Exception as error:  # Report every generated declaration in one failure.
            failures.append(f"{sail_name}: {type(error).__name__}: {error}")
    assert not failures, "generated annotations do not resolve:\n" + "\n".join(failures)


def api_checks(module: Any) -> None:
    annotation_checks(module)

    assert type(module.keep_nat(12)) is module.Uint
    assert type(module.keep_natural(12)) is module.Uint
    assert type(module.keep_u8(255)) is module.U8
    small = module.keep_small_range(3)
    assert isinstance(small, module.Unsigned)
    assert small == 3
    assert type(module.keep_quotient_range(7)) is module.Uint
    assert module.identity_range_name(9) == 9
    expect_raises(OverflowError, lambda: module.keep_small_range(2))
    expect_raises(OverflowError, lambda: module.keep_small_range(11))

    for width in (8, 16, 32, 64, 256):
        uint = getattr(module, f"U{width}")
        keep = getattr(module, f"keep_u{width}")
        maximum = (1 << width) - 1
        assert type(uint(maximum)) is uint
        assert keep(maximum) == maximum
        expect_raises(OverflowError, lambda uint=uint, width=width: uint(1 << width))

    expect_raises(OverflowError, lambda: module.Uint(0) - module.Uint(1))
    expect_raises(OverflowError, lambda: module.U8(255) + module.U8(1))
    expect_raises(OverflowError, lambda: module.U8(0) - module.U8(1))
    expect_raises(OverflowError, lambda: module.U8(17) * module.U8(17))
    assert module.U8(255).wrapping_add(module.U8(1)) == module.U8(0)
    assert module.U8(0).wrapping_sub(module.U8(1)) == module.U8(255)
    assert module.U8(17).wrapping_mul(module.U8(17)) == module.U8(33)
    assert module.Bits(8, 0xFF) + module.Bits(8, 1) == module.Bits(8, 0)
    expect_raises(ValueError, lambda: module.sum_bits(module.Bits(7, 1), module.Bits(8, 1)))
    expect_raises(ValueError, lambda: module.Bits(8, 1) + module.Bits(7, 1))
    assert module.polymorphic_first(module.Bits(7, 0x55), module.Bits(7, 0x2A)) == module.Bits(7, 0x55)
    assert module.polymorphic_zeros(11) == module.Bits(11, 0)
    assert module.dependent_bounded_identity(12) == 12
    assert module.Bits(8, 0x11) * module.Bits(8, 0x11) == module.Bits(8, 0x21)
    assert module.Bits(4, 0xA).concat(module.Bits(4, 5)) == module.Bits(8, 0xA5)
    assert module.Bits(8, 0xAB).slice(0, 4) == module.Bits(4, 0xB)
    assert module.Bits(8, 0xFF).signed() == -1
    assert module.vector_fill(module.Bits(8, 0xA5)) == [module.Bits(8, 0xA5)] * 4
    assert module.shadowed_name(4) == 5
    assert module.local_shadows_function(4) == 4
    assert module.undefined_user_value(4) == 5

    for generated_name in ("undefined_Pair", "undefined_Direction", "undefined_Traffic"):
        assert not hasattr(module, generated_name)
        assert generated_name not in module.__sail_functions__
        assert generated_name not in module.__sail_source_signatures__

    assert dataclasses.is_dataclass(module.Pair)
    assert [field.name for field in dataclasses.fields(module.Pair)] == ["left", "right"]
    assert module.__sail_types__["Pair"] is module.Pair
    assert module.__sail_types__["Direction"] is module.Direction
    assert module.__sail_types__["Traffic"] is module.Traffic
    assert module.__sail_functions__["sum_int"] is module.sum_int
    assert module.__sail_signatures__["sum_int"] == module.sum_int.__annotations__
    assert "sum_bits" in module.__sail_source_signatures__
    assert module.__sail_effects__["sum_int"] == "pure"
    assert module.__sail_effects__["bump_counter"] == "effectful"
    assert module.__sail_externs__["host_value"] == "python_missing_host_value"
    assert module.__sail_externs__["c_host_value"] == "c_host_value"
    pair = module.Pair(left=9, right=module.Bits(8, 0xFF))
    swapped = module.swap_pair(pair)
    assert isinstance(swapped, module.Pair)
    assert swapped.left == -1
    assert swapped.right == module.Bits(8, 0)
    assert isinstance(module.SomeByte(module.Bits(8, 0xA5)), module.MaybeByte)
    assert dataclasses.is_dataclass(module.Bounded)
    assert module.Bounded(12).value == 12
    assert module.unwrap_or_zero(module.SomeByte(module.Bits(8, 0xA5))) == module.Bits(8, 0xA5)
    assert module.unwrap_or_zero(module.NoByte()) == module.Bits(8, 0)
    assert module.option_or_zero(None) == 0
    assert module.option_or_zero(7) == 7
    assert module.optional_positive(-1) is None
    assert module.optional_positive(7) == 7
    assert not hasattr(module, "sail_None")
    assert not hasattr(module, "Some")
    assert module.traffic_score(module.Traffic.Stop) == 0
    assert module.traffic_score(module.Traffic.Go) == 2
    assert module.Direction(0) is module.Direction.North
    assert module.Direction(2) is module.Direction.East
    assert module.Direction.South.value == 1
    assert module.direction_from_number(2) is module.Direction.East
    assert module.direction_number(module.Direction.South) == 1
    expect_raises(ValueError, lambda: module.Direction(3))
    for generated_name in ("Direction_of_num", "num_of_Direction"):
        assert not hasattr(module, generated_name)
        assert generated_name not in module.__sail_functions__
        assert generated_name not in module.__sail_source_signatures__
    assert module.pair_pattern_score(module.Pair(3, module.Bits(8, 0))) == 3
    assert module.pair_pattern_score(module.Pair(3, module.Bits(8, 0xFF))) == 2
    original = module.Pair(1, module.Bits(8, 2))
    updated = module.update_pair(original, 7, module.Bits(8, 3))
    assert original == module.Pair(1, module.Bits(8, 2))
    assert updated == module.Pair(7, module.Bits(8, 3))
    assert module.first_at_least(2, 9) == 2
    error = expect_raises(module.SailError, lambda: module.require_nonnegative(-1))
    assert "value must be non-negative" in str(error)
    signature = inspect.signature(module.sum_int)
    assert list(signature.parameters) == ["x", "y"]
    assert all(parameter.kind is inspect.Parameter.POSITIONAL_OR_KEYWORD for parameter in signature.parameters.values())

    module.reset()
    assert module.bump_counter(2) == 2
    module.reset()
    assert module.bump_counter(2) == 2
    module.reset()
    assert module.discard_bump_result(5) == 5

    error = expect_raises(module.SailUnsupportedError, module.call_host)
    message = str(error)
    assert "python_missing_host_value" in message
    assert "register_extern" in message
    module.register_extern("python_missing_host_value", lambda: 41)
    assert module.call_host() == 41
    error = expect_raises(module.SailUnsupportedError, module.call_c_host)
    assert "c_host_value" in str(error)
    module.register_extern("c_host_value", lambda: 73)
    assert module.call_c_host() == 73
    host_pair = module.Pair(5, module.Bits(8, 6))
    module.register_extern("python_missing_host_pair", lambda: host_pair)
    assert module.call_host_pair() is host_pair
    expect_raises(module.SailUndefinedError, module.call_undefined)


def pydantic_record_checks(module: Any) -> None:
    validity = module.BoundedCursorValidity(maximum=8)
    cursor = module.BoundedCursor(
        validity=validity,
        count=module.Uint(3),
        position=module.Uint(4),
    )
    assert module.make_bounded_cursor(3, 4) == cursor
    assert module.copy_bounded_cursor(cursor) == cursor
    assert module.copy_bounded_cursor(cursor).validity.maximum == 8

    expect_raises(ValueError, lambda: module.BoundedCursorValidity(maximum=0))
    expect_raises(ValueError, lambda: module.BoundedCursorValidity(maximum=17))
    expect_raises(
        ValueError,
        lambda: module.BoundedCursor(
            validity=module.BoundedCursorValidity(maximum=8),
            count=module.Uint(9),
            position=module.Uint(0),
        ),
    )
    expect_raises(
        ValueError,
        lambda: module.BoundedCursor(
            validity=module.BoundedCursorValidity(maximum=8),
            count=module.Uint(0),
            position=module.Uint(8),
        ),
    )
    expect_raises(
        ValueError,
        lambda: module.BoundedCursor(
            validity=module.BoundedCursorValidity(maximum=8),
            count="1",
            position=module.Uint(0),
        ),
    )
    expect_raises(ValueError, lambda: setattr(cursor, "count", module.Uint(9)))
    cursor = module.BoundedCursor(
        validity=validity,
        count=module.Uint(3),
        position=module.Uint(4),
    )
    expect_raises(
        ValueError,
        lambda: setattr(
            cursor,
            "validity",
            module.BoundedCursorValidity(maximum=3),
        ),
    )

    pre_blob = module.make_conditional_profile(10, 7)
    assert pre_blob.limit == 0
    blob = module.make_conditional_profile(11, 7)
    assert blob.limit == 1792
    nominal_pre_blob = module.make_conditional_profile(module.Uint(10), module.Uint(7))
    assert nominal_pre_blob.limit == 0
    nominal_blob = module.make_conditional_profile(module.Uint(11), module.Uint(7))
    assert nominal_blob.limit == 1792
    expect_raises(
        ValueError,
        lambda: module.ConditionalProfile(
            validity=module.ConditionalProfileValidity(fork=10, denominator=7),
            fork=10,
            denominator=7,
            limit=1792,
        ),
    )


def source_projection(source: str) -> str:
    tree = ast.parse(source)
    declarations = {
        node.name: node
        for node in tree.body
        if isinstance(node, (ast.ClassDef, ast.FunctionDef))
    }
    lines = source.splitlines()
    blocks: list[str] = []
    for name in SOURCE_GOLDEN_NAMES:
        node = declarations[name]
        starts = [node.lineno]
        if node.decorator_list:
            starts.extend(decorator.lineno for decorator in node.decorator_list)
        block = "\n".join(lines[min(starts) - 1 : node.end_lineno])
        blocks.append(re.sub(r"_sail_([a-z_]+)_\d+", r"_sail_\1_N", block))
    return "\n\n".join(blocks)


def source_checks(path: Path, golden_name: str = "source.expect") -> None:
    source = path.read_text()
    assert " import *" not in source
    assert "_sail_discarded_" not in source
    assert "@dataclass(slots=True)\nclass Pair:" in source
    assert "class MaybeByte:" in source
    assert "class Traffic(Enum):" in source
    assert "Stop = auto()" in source
    assert "class Direction(UintEnum):" in source
    assert "North = Uint(0)" in source
    assert "def sum_int(x: int, y: int) -> int:" in source
    assert "def update_pair(pair: Pair, left: int, right: Annotated[Bits, BitWidth(8)]) -> Pair:" in source
    assert "def Direction_of_num(" not in source
    assert "def num_of_Direction(" not in source
    assert "p0_u0023_" not in source
    assert "IntegerRange(e, e)" not in source
    assert "match pair:" in source
    for erased_form in ("_SAIL_PROGRAM", "_MODEL.call_public", "class SailModel", "class SailStruct", "class SailVariant"):
        assert erased_form not in source
    assert_lines(
        "generated source golden",
        source_projection(source).splitlines(),
        (HERE / golden_name).read_text().splitlines(),
    )


def assert_no_generated_coercions(source: str) -> None:
    assert not any(
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id.startswith("coerce_")
        for node in ast.walk(ast.parse(source))
    )


def preserved_structure_checks(path: Path) -> None:
    source = path.read_text()
    source_checks(path, "source_preserve.expect")
    declarations = (
        "class Pair:",
        "def sum_int(",
        "def catches_exception(",
        "COUNTER_BASE:",
        "def bump_counter(",
        "def call_host(",
    )
    positions = [source.index(declaration) for declaration in declarations]
    assert positions == sorted(positions)
    assert "_sail_result_" not in source_projection(source)
    assert_no_generated_coercions(source)


def split_structure_checks(path: Path) -> None:
    expected_files = (
        "__init__.py",
        "_runtime.py",
        "_types.py",
        "basic.py",
        "_sail/__init__.py",
        "_sail/flow.py",
    )
    for relative_path in expected_files:
        assert (path / relative_path).is_file(), relative_path

    types_source = (path / "_types.py").read_text()
    basic_source = (path / "basic.py").read_text()
    init_source = (path / "__init__.py").read_text()

    assert not (path / "_model.py").exists()
    assert "class Pair:" not in types_source
    assert "class MaybeByte:" not in types_source
    assert "class Traffic(Enum):" not in types_source
    assert "from .basic import (" in types_source
    assert "    Pair as Pair," in types_source
    assert "    MaybeByte as MaybeByte," in types_source
    assert "    Traffic as Traffic," in types_source
    assert "@dataclass(slots=True)\nclass Pair:" in basic_source
    assert "class MaybeByte:" in basic_source
    assert "class Traffic(Enum):" in basic_source
    assert "def sum_int(x: int, y: int) -> int:" in basic_source
    assert "_model.update_pair" not in basic_source
    assert "updated = update_pair(" in basic_source
    assert_no_generated_coercions(basic_source)
    assert re.search(r"(?<!\w)_model(?!\w)", basic_source) is None
    assert re.search(r"^COUNTER_BASE: .* = 0$", basic_source, flags=re.MULTILINE)
    assert re.search(r"^COUNTER_INITIAL: .* = COUNTER_BASE$", basic_source, flags=re.MULTILINE)
    assert re.search(r"^COUNTER: .* = COUNTER_INITIAL$", basic_source, flags=re.MULTILINE)
    bump_node = next(
        node for node in ast.parse(basic_source).body if isinstance(node, ast.FunctionDef) and node.name == "bump_counter"
    )
    assert any(
        isinstance(node, ast.Global) and "COUNTER" in node.names
        for node in bump_node.body
    )
    reset_node = next(
        node
        for node in ast.parse(basic_source).body
        if isinstance(node, ast.FunctionDef) and node.name == "_reset_registers"
    )
    reset_source = ast.get_source_segment(basic_source, reset_node)
    assert reset_source is not None
    reset_assignments = {
        target.id
        for node in ast.walk(reset_node)
        if isinstance(node, (ast.Assign, ast.AnnAssign))
        for target in ([node.target] if isinstance(node, ast.AnnAssign) else node.targets)
        if isinstance(target, ast.Name)
    }
    assert "COUNTER_BASE" not in reset_assignments
    assert "COUNTER_INITIAL" not in reset_assignments
    assert "COUNTER" in reset_assignments
    assert "from . import basic as _register_basic" in init_source
    assert '"COUNTER": _register_basic' in init_source
    assert "_module._reset_registers()" in init_source
    assert "def __getattr__(name: str):" in init_source
    assert "# Sail source: basic.sail" in basic_source
    assert str(HERE) not in basic_source
    for source in path.rglob("*.py"):
        generated_source = source.read_text()
        assert " import *" not in generated_source
        assert re.search(r"(?<!\w)_model(?!\w)", generated_source) is None
        ast.parse(generated_source, filename=str(source))


def nested_split_checks(path: Path) -> None:
    types_source = (path / "_types.py").read_text()
    main_source = (path / "main.py").read_text()
    helper_source = (path / "lib" / "helpers.py").read_text()
    imports = {
        (node.module, alias.name, alias.asname)
        for source in (main_source, helper_source)
        for node in ast.parse(source).body
        if isinstance(node, ast.ImportFrom)
        for alias in node.names
    }
    assert "class SplitValue:" not in types_source
    assert "from .lib.helpers import (" in types_source
    assert "    SplitValue as SplitValue," in types_source
    assert "from .main import (" in types_source
    assert "    SplitValueAlias as SplitValueAlias," in types_source
    assert "# Sail source: main.sail" in main_source
    assert "# Sail source: lib/helpers.sail" in helper_source
    assert "SplitValueAlias: TypeAlias = helpers.SplitValue" in main_source
    assert "@dataclass(slots=True)\nclass SplitValue:" in helper_source
    assert "def split_twice(" in main_source
    assert "def split_value_score(" in main_source
    assert "def main(" in main_source
    assert "def split_increment(" in helper_source
    assert "def choose_named(" in helper_source
    assert "if condition:\n        selected = 1\n    else:\n        selected = 2\n    return selected" in helper_source
    assert "def split_cycle(" in helper_source
    assert "SPLIT_INITIAL: int = 1" in helper_source
    assert "SPLIT_COUNTER: int = SPLIT_INITIAL" in helper_source
    assert "def _reset_registers() -> None:" in helper_source
    assert "global SPLIT_COUNTER" in helper_source
    assert "_model.split_increment" not in main_source
    assert "return helpers.split_increment(helpers.split_increment(value))" in main_source
    assert ("nested_model.lib.helpers", "SplitValue", None) not in imports
    assert ("nested_model.lib.helpers", "split_increment", None) not in imports
    assert "_model.split_twice" not in helper_source
    assert "return (int(main_1.split_twice(value)) - 2)" in helper_source
    assert ("nested_model", "main", "main_1") in imports
    assert ("nested_model.lib", "helpers", None) in imports
    assert "helpers.SPLIT_COUNTER = (int(helpers.SPLIT_COUNTER) + int(amount))" in main_source
    assert "return helpers.SPLIT_COUNTER" in main_source
    assert "return helpers.SPLIT_INITIAL" in main_source
    assert ("nested_model.lib.helpers", "SPLIT_INITIAL", None) not in imports
    assert "_sail_module_" not in main_source
    assert "_sail_module_" not in helper_source
    assert re.search(r"(?<!\w)_model(?!\w)", main_source) is None
    assert re.search(r"(?<!\w)_model(?!\w)", helper_source) is None
    for source in path.rglob("*.py"):
        parsed = ast.parse(source.read_text(), filename=str(source))
        seen_non_import = False
        body = parsed.body
        if (
            body
            and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)
        ):
            body = body[1:]
        for node in body:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                assert not seen_non_import, f"non-top-level import in {source}"
            else:
                seen_non_import = True
        assert "# noqa: E402" not in source.read_text()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sail", default=os.environ.get("SAIL", str(DEFAULT_SAIL if DEFAULT_SAIL.exists() else "sail")))
    parser.add_argument("--plugin", default=str(DEFAULT_PLUGIN) if DEFAULT_PLUGIN.exists() else None)
    args = parser.parse_args()

    sail_path = Path(args.sail)
    sail = [str(sail_path.resolve()) if sail_path.exists() else args.sail]
    if args.plugin:
        plugin_path = Path(args.plugin)
        sail += ["-plugin", str(plugin_path.resolve()) if plugin_path.exists() else args.plugin]

    help_result = command(sail + ["--help"])
    help_text = help_result.stdout + help_result.stderr
    assert "Options for target python" in help_text
    assert "--python-preserve-structure" in help_text
    assert "--python-split" in help_text
    assert "--python-source-root <directory>" in help_text
    assert "--python-runtime-module <module>" in help_text
    assert "--python-extern-module <module>" in help_text
    assert "--python-import-file <file>" in help_text
    assert "--python-ethereum-types" not in help_text
    assert "--python-int-ranges" not in help_text
    assert "--python-pydantic" in help_text
    assert "--python-ethereum-fixed-bytes <SailType=BytesN>" in help_text
    command(
        sail + ["--python-runtime-module", "invalid..module", "--help"],
        expect_success=False,
    )
    command(
        sail + ["--python-runtime-module", "class", "--help"],
        expect_success=False,
    )

    temp_root = Path(os.environ.get("AGENT_TMPDIR", ROOT / ".agent-tmp"))
    temp_root.mkdir(parents=True, exist_ok=True)
    expected = (HERE / "oracle.expect").read_text().splitlines()

    with tempfile.TemporaryDirectory(prefix="python-backend-test-", dir=temp_root) as directory:
        output = Path(directory)
        obsolete_profile = command(
            sail
            + [
                "--python",
                "--python-ethereum-types",
                "-o",
                str(output / "obsolete.py"),
                str(HERE / "ethereum_types.sail"),
            ],
            expect_success=False,
        )
        assert "usage: sail" in (obsolete_profile.stdout + obsolete_profile.stderr)
        obsolete_ranges = command(
            sail
            + [
                "--python",
                "--python-int-ranges",
                "-o",
                str(output / "obsolete_ranges.py"),
                str(HERE / "ethereum_types.sail"),
            ],
            expect_success=False,
        )
        assert "usage: sail" in (obsolete_ranges.stdout + obsolete_ranges.stderr)
        interpreter = command(
            sail
            + [
                "-is",
                str(HERE / "oracle.isail"),
                str(HERE / "basic.sail"),
            ],
            cwd=output,
        )
        interpreter_values = re.findall(r"^Result = (.*)$", interpreter.stdout, flags=re.MULTILINE)
        assert_lines("Sail interpreter", interpreter_values, expected)

        embedded_path = output / "embedded.py"
        command(sail + ["--python", "-o", str(embedded_path), str(HERE / "basic.sail")])
        command([sys.executable, "-m", "py_compile", str(embedded_path)])
        source_checks(embedded_path)
        embedded = import_file("sail_python_test_embedded", embedded_path)
        assert_lines("embedded Python", oracle_values(embedded), expected)
        api_checks(embedded)
        fixed_bytes = type("FixedBytes", (bytes,), {})
        updated_fixed_bytes = embedded.sail_vector_update(
            fixed_bytes(b"\x00\x00"), 0, embedded.Bits(8, 7), False
        )
        assert isinstance(updated_fixed_bytes, fixed_bytes)
        assert updated_fixed_bytes == b"\x00\x07"
        assert embedded.sail_vector_access(updated_fixed_bytes, 0, False) == embedded.Bits(8, 7)

        runtime_dir = ROOT / "src/sail_python_backend"
        sys.path.insert(0, str(runtime_dir))
        external_path = output / "external.py"
        command(
            sail
            + [
                "--python",
                "--python-preserve-structure",
                "--python-runtime-module",
                "sail_runtime",
                "-o",
                str(external_path),
                str(HERE / "basic.sail"),
            ]
        )
        command(
            [sys.executable, "-m", "py_compile", str(runtime_dir / "sail_runtime.py"), str(external_path)],
            extra_env={"PYTHONPYCACHEPREFIX": str(output / "pycache")},
        )
        preserved_structure_checks(external_path)
        external = import_file("sail_python_test_external", external_path)
        assert_lines("external-runtime Python", oracle_values(external), expected)
        api_checks(external)

        ethereum_path = output / "ethereum_types.py"
        command(
            sail
            + [
                "--python",
                "--python-ethereum-fixed-bytes",
                "address=Bytes20",
                "--python-ethereum-fixed-bytes",
                "hash=Bytes32",
                "-o",
                str(ethereum_path),
                str(HERE / "ethereum_types.sail"),
            ]
        )
        command([sys.executable, "-m", "py_compile", str(ethereum_path)])
        ethereum_source = ethereum_path.read_text()
        assert "from ethereum_types.numeric import (" in ethereum_source
        assert "    U8 as U8," in ethereum_source
        assert "from ethereum_types.bytes import (" in ethereum_source
        assert "    Bytes20 as Bytes20," in ethereum_source
        assert "    Bytes32 as Bytes32," in ethereum_source
        assert "class Uint(" not in ethereum_source
        assert "class _FixedUint(" not in ethereum_source
        assert "class U256(" not in ethereum_source
        assert "class Bits:" in ethereum_source
        assert ethereum_source.index("from typing import") < ethereum_source.index(
            "from ethereum_types.numeric import"
        )
        assert ethereum_source.index("from ethereum_types.bytes import") < ethereum_source.index(
            "class SailError"
        )
        assert "# noqa: E402" not in ethereum_source
        assert "address: TypeAlias = Bytes20" in ethereum_source
        assert "hash: TypeAlias = Bytes32" in ethereum_source
        assert "word: TypeAlias = U256" in ethereum_source
        assert "class word_below_max(Unsigned):" in ethereum_source
        assert "def _in_range(self, value: int) -> bool:" in ethereum_source
        assert "def keep_address(value: address) -> address:" in ethereum_source
        assert "def update_hash(value: hash," in ethereum_source
        assert_no_generated_coercions(ethereum_source)
        assert "def keep_word(value: word) -> word:" in ethereum_source
        ethereum = import_file("sail_python_test_ethereum", ethereum_path)
        assert ethereum.word is ethereum.U256
        assert issubclass(ethereum.word_below_max, ethereum.Unsigned)
        assert ethereum.word_below_max(0) == 0
        assert ethereum.word_below_max((1 << 256) - 2) == (1 << 256) - 2
        expect_raises(OverflowError, lambda: ethereum.word_below_max(-1))
        expect_raises(OverflowError, lambda: ethereum.word_below_max((1 << 256) - 1))
        incremented = ethereum.increment_word(ethereum.word_below_max((1 << 256) - 2))
        assert type(incremented) is ethereum.U256
        assert incremented == (1 << 256) - 1

        pydantic_path = output / "dependent_records.py"
        command(
            sail
            + [
                "--python",
                "--python-pydantic",
                "-o",
                str(pydantic_path),
                str(HERE / "dependent_records.sail"),
            ]
        )
        command([sys.executable, "-m", "py_compile", str(pydantic_path)])
        pydantic_source = pydantic_path.read_text()
        assert "class BoundedCursorValidity:" in pydantic_source
        assert "maximum: int" in pydantic_source
        assert "count: Uint" in pydantic_source
        assert "position: Uint" in pydantic_source
        assert "field_validator" not in pydantic_source
        assert "ValidationInfo" not in pydantic_source
        assert '@model_validator(mode="after")' in pydantic_source
        assert "def validate(self) -> Self:" in pydantic_source
        assert "validity: BoundedCursorValidity" in pydantic_source
        assert "0 <= int(self.count) <= self.validity.maximum" in pydantic_source
        assert "int(self.position) <= (self.validity.maximum - 1)" in pydantic_source
        assert "BoundedCursorValidity(maximum=8)" in pydantic_source
        assert "BoundedCursorValidity(maximum=cursor.validity.maximum)" in pydantic_source
        assert (
            "int(self.limit) == (0 if (self.validity.fork < 11) else "
            "(256 * self.validity.denominator))"
        ) in pydantic_source
        assert_no_generated_coercions(pydantic_source)
        if importlib.util.find_spec("pydantic") is not None:
            pydantic_module = import_file("sail_python_test_pydantic", pydantic_path)
            pydantic_record_checks(pydantic_module)

        ethereum_package = output / "ethereum_package"
        command(
            sail
            + [
                "--python",
                "--python-split",
                "--python-ethereum-fixed-bytes",
                "address=Bytes20",
                "--python-ethereum-fixed-bytes",
                "hash=Bytes32",
                "-o",
                str(ethereum_package),
                str(HERE / "ethereum_types.sail"),
            ]
        )
        ethereum_runtime = ethereum_package / "_runtime.py"
        ethereum_runtime_source = ethereum_runtime.read_text()
        assert not ethereum_runtime_source.endswith("\n\n")
        assert "from ethereum_types.numeric import" in ethereum_runtime_source
        assert "from ethereum_types.bytes import" in ethereum_runtime_source
        assert "class Uint(" not in ethereum_runtime_source
        assert "class _FixedUint(" not in ethereum_runtime_source
        assert "class U256(" not in ethereum_runtime_source
        assert "class Bits:" in ethereum_runtime_source
        for python_file in ethereum_package.rglob("*.py"):
            if python_file == ethereum_runtime:
                continue
            source = python_file.read_text()
            assert "from ethereum_types." not in source
        ethereum_module_source = (ethereum_package / "ethereum_types.py").read_text()
        assert "from ._runtime import (" in ethereum_module_source
        assert "Bytes20" in ethereum_module_source
        assert "Bytes32" in ethereum_module_source
        assert "U256" in ethereum_module_source

        split_path = output / "split_model"
        command(
            sail
            + [
                "--python",
                "--python-split",
                "--python-preserve-structure",
                "--python-source-root",
                str(HERE),
                "-o",
                str(split_path),
                str(HERE / "basic.sail"),
            ]
        )
        command(
            [sys.executable, "-m", "compileall", "-q", str(split_path)],
            extra_env={"PYTHONPYCACHEPREFIX": str(output / "pycache")},
        )
        split_structure_checks(split_path)
        split = import_package("split_model", split_path)
        assert split.Pair.__module__ == "split_model.basic"
        assert split.MaybeByte.__module__ == "split_model.basic"
        assert split.Traffic.__module__ == "split_model.basic"
        assert_lines("split-package Python", oracle_values(split), expected)
        api_checks(split)

        contract_path = output / "contract_model"
        command(
            sail
            + [
                "--python",
                "--python-split",
                "--python-preserve-structure",
                "--python-source-root",
                str(HERE),
                "--python-extern-module",
                "contract_model.extern_contract",
                "--python-import-file",
                str(HERE / "extern_contract.py"),
                "-o",
                str(contract_path),
                str(HERE / "basic.sail"),
            ]
        )
        command(
            [sys.executable, "-m", "compileall", "-q", str(contract_path)],
            extra_env={"PYTHONPYCACHEPREFIX": str(output / "pycache")},
        )
        assert (contract_path / "extern_contract.py").read_text() == (HERE / "extern_contract.py").read_text()
        for python_file in contract_path.rglob("*.py"):
            source = python_file.read_text()
            assert "call_extern" not in source
            assert "register_extern" not in source
            assert "_sail_extern." not in source
        basic_contract_source = (contract_path / "basic.py").read_text()
        assert (
            "python_missing_host_value as _host_python_missing_host_value"
            in basic_contract_source
        )
        assert "_host_python_missing_host_value()" in basic_contract_source
        contract = import_package("contract_model", contract_path)
        assert not hasattr(contract, "call_extern")
        assert not hasattr(contract, "register_extern")
        assert contract.call_host() == 41
        assert contract.call_c_host() == 73

        nested_path = output / "nested_model"
        nested_fixture = HERE / "split" / "main.sail"
        command(
            sail
            + [
                "--python",
                "--python-split",
                "--python-preserve-structure",
                "--python-source-root",
                str(nested_fixture.parent),
                "-o",
                str(nested_path),
                str(nested_fixture),
            ]
        )
        command(
            [sys.executable, "-m", "compileall", "-q", str(nested_path)],
            extra_env={"PYTHONPYCACHEPREFIX": str(output / "pycache")},
        )
        nested_split_checks(nested_path)
        nested = import_package("nested_model", nested_path)
        assert nested.SplitValue.__module__ == "nested_model.lib.helpers"
        assert nested.SplitValueAlias is nested.SplitValue
        assert nested.split_value_score(nested.SplitValue(value=9)) == 9
        assert nested.split_twice(40) == 42
        assert nested.choose_named(True) == 1
        assert nested.choose_named(False) == 2
        assert nested.split_cycle(40) == 40
        assert nested.SPLIT_COUNTER == 1
        assert nested.split_bump(4) == 5
        assert nested.SPLIT_COUNTER == 5
        assert nested.split_initial() == 1
        nested.reset()
        assert nested.SPLIT_COUNTER == 1
        assert callable(nested.main)
        assert nested.main() is None
        assert nested.main.__module__ == "nested_model.main"

    print("Sail Python backend tests: ok")


if __name__ == "__main__":
    main()
