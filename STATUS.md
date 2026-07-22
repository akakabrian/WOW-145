# WOW II Conjecture 145 — CI Status

## STATEMENT

**PROVEN (audit).** The theorem candidate preserves the exact authoritative theorem statement.

## SEARCH

**PROVEN (bounded evidence).** Exhaustive connected unlabeled graphs through seven vertices and independent random exact checks found no counterexample. Search evidence is not used as proof.

## PROOF

**PROVEN (human mathematics).** The `localIndependenceMin Gᶜ = 1` branch forces `G.radius.toNat = 2`; the remaining arithmetic reduces to the independently audited six-vertex exceptional induced-tree theorem from WOW II Conjecture 146.

## LEAN

**BLOCKED (GitHub Actions launch gate).** The repository contains:

- exact Lean 4.27.0 toolchain configuration;
- a pinned dependency on audited WOW-146 commit `18201d492b52a2f82a2966551aed1640c45ec13b`;
- `lake build WOW145` and warning-as-error audit commands;
- forbidden-token and source-hash checks;
- a run-start marker and committed compiler-evidence mechanism;
- push, pull-request, manual, scheduled, and `issues: opened` triggers.

The `issues: opened` trigger was committed to `main`, and one-purpose issue #1 (`Trigger Lean verification`) was opened on July 21, 2026. No `ci-run-started.txt` marker appeared after that event. Earlier normal content pushes and scheduled boundaries also produced no marker. Therefore no evidence shows that a GitHub-hosted runner began executing the workflow. This is not a Lean success or Lean failure.

## REVIEW

**OPEN.** Exact integrated kernel result and final axiom output pending.

## SUBMISSION

**STOPPED.** No upstream pull request, maintainer contact, or solved claim is authorized.

## NEXT

The remaining blocker is repository-level GitHub Actions enablement or policy. Once Actions is enabled, any new issue, push, scheduled boundary, or manual dispatch should launch `Verify WOWII 145`; the workflow will commit `ci-run-started.txt` and then `lean-ci.log`. Read that log, repair any elaboration errors without changing the theorem statement, and repeat until the exact kernel and axiom audits pass.
