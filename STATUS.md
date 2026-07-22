# WOW II Conjecture 145 — Final Status

## STATEMENT

**PROVEN.** The exact authoritative theorem statement and hypotheses were preserved unchanged.

## SEARCH

**PROVEN (bounded supporting evidence).** Exhaustive connected unlabeled graphs through seven vertices and independent exact random checks found no counterexample. This search evidence is supporting evidence only, not part of the proof.

## PROOF

**PROVEN.** The product inequality is split by `localIndependenceMin Gᶜ`.

- If the value is at least two, the peripheral-eccentricity/diameter bound and a diametral induced tree finish the estimate.
- If the value is one, a minimizing complement-local-independence vertex is within distance two of every vertex, hence radius is at most two and diameter at most four.
- The only sharp metric case is peripheral eccentricity three and diameter four; then radius is exactly two, and a local explicit six-vertex induced-tree construction proves the remaining bound.

## LEAN

**PROVEN.** Exact green candidate:

`bebf8938b85520d777ebec7c61e7466a7053d4fb`

Lean 4.27.0 x86-64 run `29890955237` passed:

- `lake build WOW145`
- `lake env lean -DwarningAsError=true WOW145/Audit.lean`
- `lake --wfail build`
- forbidden-token scan
- source-hash recording
- `#print axioms`

No `sorry`, `admit`, custom axiom, or `native_decide` occurs. No `WOW146` / `wow_146` package dependency occurs. The printed axioms are only standard Lean foundations (`propext`, `Classical.choice`, and `Quot.sound`).

## REVIEW

**PROVEN.** Independent ARM64 Lean 4.27.0 run `29891321009` checked the same exact commit and passed all gates.

## SUBMISSION

**APPROVED by Brian on July 21, 2026 HST.** An upstream submission already exists as `google-deepmind/formal-conjectures#4520`, so no duplicate PR was opened. This repository is published as an independently kernel-checked alternate proof artifact. An attempted verification comment on upstream PR #4520 was rejected with HTTP 403 because the connected GitHub App lacks write permission on the upstream repository.

## NEXT

Post the prepared independent-verification note on upstream PR #4520 using Brian's GitHub account, then await maintainer review. Do not claim priority over the existing submitter; present this package as independent verification and an alternate immutable proof.
