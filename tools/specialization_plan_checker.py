#!/usr/bin/env python3
"""Independent structural checker and proof-fixture adapter for Sail plans."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from typing import Any

SCHEMA = "https://sail-lang.org/schemas/specialization-plan/v1"
REQUIRED_OBLIGATIONS = {
    "representation_adequacy",
    "operation_refinement",
    "conversion_correctness",
    "call_compatibility",
    "path_condition_soundness",
    "exception_equivalence",
    "extern_refinement",
    "ownership_lifetime",
}


class InvalidPlan(Exception):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidPlan(message)


def require_sorted_unique(records: list[dict[str, Any]], label: str) -> set[str]:
    identities = [record.get("id") for record in records]
    require(all(isinstance(identity, str) and identity for identity in identities), f"{label}: missing id")
    require(identities == sorted(identities), f"{label}: records are not in canonical id order")
    require(len(identities) == len(set(identities)), f"{label}: duplicate id")
    return set(identities)


def load_plan(path: pathlib.Path) -> tuple[dict[str, Any], bytes]:
    raw = path.read_bytes()
    try:
        plan = json.loads(raw)
    except json.JSONDecodeError as error:
        raise InvalidPlan(f"malformed JSON: {error}") from error
    require(isinstance(plan, dict), "plan root must be an object")
    return plan, raw


def check(plan: dict[str, Any]) -> dict[str, int]:
    require(plan.get("schema") == SCHEMA, "unsupported schema")
    require(plan.get("schema_version") == "1.0.0", "unsupported schema version")
    require(isinstance(plan.get("producer"), dict), "missing producer identity")
    require(isinstance(plan.get("configuration", {}).get("id"), str), "missing configuration identity")

    inputs = plan.get("inputs")
    clones = plan.get("clones")
    require(isinstance(inputs, list), "inputs must be an array")
    require(isinstance(clones, list), "clones must be an array")
    input_ids = require_sorted_unique(inputs, "inputs")
    clone_ids = require_sorted_unique(clones, "clones")

    obligation_ids: set[str] = set()
    call_count = 0
    conversion_count = 0
    for clone in clones:
        require(clone.get("clone_key") == clone.get("id"), f"{clone.get('id')}: clone key mismatch")
        require(clone.get("location", {}).get("input") in input_ids, f"{clone.get('id')}: dangling input reference")
        require(isinstance(clone.get("source"), str), f"{clone.get('id')}: missing source identity")
        require(isinstance(clone.get("semantic_signature"), dict), f"{clone.get('id')}: missing semantic signature")
        require(isinstance(clone.get("represented_signature"), dict), f"{clone.get('id')}: missing represented signature")

        calls = clone.get("call_edges")
        conversions = clone.get("conversions")
        obligations = clone.get("obligations")
        require(isinstance(calls, list), f"{clone.get('id')}: call_edges must be an array")
        require(isinstance(conversions, list), f"{clone.get('id')}: conversions must be an array")
        require(isinstance(obligations, list), f"{clone.get('id')}: obligations must be an array")
        require_sorted_unique(calls, f"{clone.get('id')}.call_edges")
        require_sorted_unique(conversions, f"{clone.get('id')}.conversions")
        current_obligations = require_sorted_unique(obligations, f"{clone.get('id')}.obligations")
        require(not (obligation_ids & current_obligations), "duplicate obligation id across clones")
        obligation_ids |= current_obligations

        kinds = {obligation.get("kind") for obligation in obligations}
        missing = REQUIRED_OBLIGATIONS - kinds
        require(not missing, f"{clone.get('id')}: missing obligations: {', '.join(sorted(missing))}")
        statuses = {"reconstructible", "requires_proof", "unresolved", "not_applicable", "discharged"}
        require(
            all(obligation.get("status") in statuses for obligation in obligations),
            f"{clone.get('id')}: invalid obligation status",
        )
        for call in calls:
            require(isinstance(call.get("callee"), str), f"{clone.get('id')}: call has no callee identity")
            if call.get("callee", "").startswith("clone:"):
                require(call["callee"] in clone_ids, f"{clone.get('id')}: dangling clone call")
        call_count += len(calls)
        conversion_count += len(conversions)

    unresolved = plan.get("unresolved_obligations")
    require(isinstance(unresolved, list), "unresolved_obligations must be an array")
    require(unresolved == sorted(unresolved), "unresolved obligations are not canonically ordered")
    require(len(unresolved) == len(set(unresolved)), "duplicate unresolved obligation reference")
    require(set(unresolved) <= obligation_ids, "dangling unresolved obligation reference")
    actual_unresolved = {
        obligation["id"]
        for clone in clones
        for obligation in clone["obligations"]
        if obligation["status"] == "unresolved"
    }
    require(set(unresolved) == actual_unresolved, "unresolved obligation index is incomplete")

    return {
        "inputs": len(inputs),
        "clones": len(clones),
        "calls": call_count,
        "conversions": conversion_count,
        "obligations": len(obligation_ids),
        "unresolved": len(unresolved),
    }


def emit_lean(path: pathlib.Path, plan: dict[str, Any], raw: bytes) -> None:
    clones = plan["clones"]
    require(clones, "cannot emit proof fixture for a plan with no clones")
    representative = clones[0]
    bound_witness: tuple[str, int, int] | None = None
    for clone in clones:
        for choice in clone.get("representation_choices", []):
            bound = choice.get("inferred_bound")
            represented = choice.get("represented_type")
            bound_match = re.fullmatch(r"0\.\.(\d+)", bound or "")
            width_match = re.fullmatch(r"%u(\d+)", represented or "")
            if bound_match and width_match:
                upper = int(bound_match.group(1))
                capacity = (1 << int(width_match.group(1))) - 1
                if upper <= capacity:
                    bound_witness = (choice["position"], upper, capacity)
                    break
        if bound_witness:
            break
    require(bound_witness is not None, "no unsigned representation-adequacy witness in plan")
    witness_position, inferred_upper, represented_upper = bound_witness
    identity = representative["id"].replace("\\", "\\\\").replace('"', '\\"')
    source_digest = hashlib.sha256(raw).hexdigest()
    contents = f"""-- Generated by specialization_plan_checker.py.
-- Plan SHA-256: {source_digest}

def specializationPlanSchema : String := "1.0.0"
def representativeCloneIdentity : String := "{identity}"
def representativeBoundPosition : String := "{witness_position}"
def representativeInferredUpper : Nat := {inferred_upper}
def representativeRepresentationUpper : Nat := {represented_upper}
def specializationCloneCount : Nat := {len(clones)}
def specializationObligationCount : Nat := {sum(len(clone["obligations"]) for clone in clones)}

theorem schema_is_consumed : specializationPlanSchema = "1.0.0" := by rfl
theorem representative_identity_is_consumed :
    representativeCloneIdentity = "{identity}" := by rfl
theorem representative_representation_adequacy :
    representativeInferredUpper ≤ representativeRepresentationUpper := by decide
theorem plan_contains_specialization : 0 < specializationCloneCount := by decide
theorem plan_contains_required_obligations :
    8 * specializationCloneCount ≤ specializationObligationCount := by decide
"""
    path.write_text(contents, encoding="utf-8")


def compare(previous: dict[str, Any], current: dict[str, Any]) -> str:
    old = {clone["id"]: clone for clone in previous.get("clones", [])}
    new = {clone["id"]: clone for clone in current.get("clones", [])}
    added = sorted(new.keys() - old.keys())
    removed = sorted(old.keys() - new.keys())
    shared = old.keys() & new.keys()
    changed = sorted(
        identity
        for identity in shared
        if json.dumps(old[identity], sort_keys=True) != json.dumps(new[identity], sort_keys=True)
    )
    lines = [
        "# Specialization Plan Comparison",
        "",
        f"- Added clones: {len(added)}",
        f"- Removed clones: {len(removed)}",
        f"- Changed clones: {len(changed)}",
    ]
    for label, identities in (("Added", added), ("Removed", removed), ("Changed", changed)):
        if identities:
            lines.extend(["", f"## {label}", ""])
            lines.extend(f"- `{identity}`" for identity in identities)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("plan", type=pathlib.Path)
    parser.add_argument("--emit-lean", type=pathlib.Path)
    parser.add_argument("--compare", type=pathlib.Path)
    parser.add_argument("--comparison-output", type=pathlib.Path)
    args = parser.parse_args()

    try:
        plan, raw = load_plan(args.plan)
        counts = check(plan)
        if args.emit_lean:
            emit_lean(args.emit_lean, plan, raw)
        if args.compare:
            previous, _ = load_plan(args.compare)
            check(previous)
            report = compare(previous, plan)
            if args.comparison_output:
                args.comparison_output.write_text(report, encoding="utf-8")
            else:
                sys.stdout.write(report)
        else:
            sys.stdout.write(
                "valid specialization plan: "
                + ", ".join(f"{key}={value}" for key, value in counts.items())
                + "\n"
            )
    except (InvalidPlan, OSError) as error:
        print(f"invalid specialization plan: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
