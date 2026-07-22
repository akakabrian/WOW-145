# WOW II Conjecture 145 — CI Status

## STATEMENT

**PROVEN (audit).** The theorem candidate preserves the exact authoritative theorem statement.

## SEARCH

**PROVEN (bounded evidence).** Exhaustive connected unlabeled graphs through seven vertices and independent random exact checks found no counterexample. Search evidence is not used as proof.

## PROOF

**PROVEN (human mathematics).** The `localIndependenceMin Gᶜ = 1` branch forces `G.radius.toNat = 2`; the remaining arithmetic reduces to the independently audited six-vertex exceptional induced-tree theorem from WOW II Conjecture 146.

## LEAN

**IN PROGRESS.** GitHub Actions is configured to use Lean 4.27.0, pin the audited WOW-146 dependency commit, build `WOW145`, compile `WOW145/Audit.lean` with warnings as errors, print theorem axioms, reject forbidden shortcuts, and publish the compiler log.

## REVIEW

**OPEN.** Exact integrated kernel result and final axiom output pending.

## SUBMISSION

**STOPPED.** No upstream pull request, maintainer contact, or solved claim is authorized.

## NEXT

Read `lean-ci.log`, repair any elaboration errors without changing the theorem statement, and repeat until the exact kernel and axiom audits pass.
