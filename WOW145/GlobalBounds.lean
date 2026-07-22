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

import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture142Proof
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Global metric and induced-tree bounds for WOWII Conjecture 145

These are generic graph lemmas.  They are stated locally so the Conjecture 145
artifact does not depend on the Conjecture 146 package.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

/-- A diametral geodesic supplies an induced tree on `diam + 1` vertices. -/
lemma diam_succ_le_largestInducedTreeSize (hG : G.Connected) :
    G.diam + 1 ≤ largestInducedTreeSize G :=
  diam_add_one_le_largestInducedTreeSize_splice hG

omit [DecidableEq α] in
/-- The eccentricity of the peripheral set is strictly below the diameter. -/
lemma eccSet_periphery_add_one_le_diam (hG : G.Connected) :
    eccSet G (maxEccentricityVertices G : Set α) + 1 ≤ G.diam := by
  by_cases hp : eccSet G (maxEccentricityVertices G : Set α) = 0
  · have hd : G.diam ≠ 0 := (connected_iff_diam_ne_zero).mp hG
    omega
  · exact eccSet_maxEccentricityVertices_add_one_le_diam_splice hG
      (Nat.pos_of_ne_zero hp)

omit [DecidableEq α] in
/-- In a finite connected graph, diameter is at most twice natural-valued radius. -/
lemma diam_le_two_mul_radius_toNat (hG : G.Connected) :
    G.diam ≤ 2 * G.radius.toNat := by
  have hr : G.radius ≠ ⊤ := radius_ne_top_iff.mpr hG
  have hmul : (2 : ℕ∞) * G.radius ≠ ⊤ :=
    WithTop.mul_ne_top (ENat.coe_ne_top 2) hr
  have h := ENat.toNat_le_toNat (ediam_le_two_mul_radius (G := G)) hmul
  simpa [diam] using h

#print axioms SimpleGraph.diam_succ_le_largestInducedTreeSize
#print axioms SimpleGraph.eccSet_periphery_add_one_le_diam
#print axioms SimpleGraph.diam_le_two_mul_radius_toNat

end SimpleGraph
