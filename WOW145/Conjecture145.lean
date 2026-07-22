/-
Copyright 2026 The WOW-145 Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import WOW145.ExceptionalCase
import WOW145.RadiusBridge

/-!
# Written on the Wall II — Conjecture 145

A standalone proof of the exact Formal Conjectures statement.  The exceptional
six-vertex argument is included locally; no Conjecture 146 module is imported.
-/

namespace WrittenOnTheWallII.GraphConjecture145

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Exact theorem statement from the authoritative Formal Conjectures source. -/
theorem conjecture145 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hlMin : 0 < localIndependenceMin Gᶜ) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * localIndependenceMin Gᶜ := by
  set p := eccSet G (maxEccentricityVertices G : Set α)
  set d := G.diam
  set t := largestInducedTreeSize G
  set ell := localIndependenceMin Gᶜ

  have hpDiam : p + 1 ≤ d := by
    simpa [p, d] using eccSet_periphery_add_one_le_diam h
  have hDiamTree : d + 1 ≤ t := by
    simpa [d, t] using diam_succ_le_largestInducedTreeSize h

  by_cases hellTwo : 2 ≤ ell
  · have hpTree : p ≤ t := by omega
    calc
      2 * p ≤ 2 * t := Nat.mul_le_mul_left 2 hpTree
      _ = t * 2 := by omega
      _ ≤ t * ell := Nat.mul_le_mul_left t hellTwo
  · have hellOne : ell = 1 := by
      have hellPos : 0 < ell := by simpa [ell] using hlMin
      omega
    have hr : G.radius.toNat = 2 := by
      apply radius_toNat_eq_two_of_localIndependenceMin_eq_one G h
      simpa [ell] using hellOne
    have hDiamRad : d ≤ 4 := by
      have hbound := diam_le_two_mul_radius_toNat h
      simpa [d, hr] using hbound
    have hpLeThree : p ≤ 3 := by omega
    by_cases hpThree : p = 3
    · have hdFour : d = 4 := by omega
      have htreeSix : 6 ≤ t := by
        simpa [t] using WOW145.exceptional_case G h hr
          (by simpa [d] using hdFour) (by simpa [p] using hpThree)
      simpa [p, t, ell, hpThree, hellOne] using htreeSix
    · have hpLeTwo : p ≤ 2 := by omega
      have htwoP : 2 * p ≤ t := by omega
      simpa [p, t, ell, hellOne] using htwoP

#print axioms WrittenOnTheWallII.GraphConjecture145.conjecture145

end WrittenOnTheWallII.GraphConjecture145
