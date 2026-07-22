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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture145
import WOW145.Metric

/-!
# The local-independence-one radius bridge

If the complement local-independence minimum is one, a minimizing vertex is at
distance at most two from every vertex.  The exceptional branch later combines
this with diameter four to obtain radius exactly two.
-/

open Classical SimpleGraph
open WrittenOnTheWallII.GraphConjecture145

namespace WOW145

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

private lemma exists_localIndependenceMin_eq (H : SimpleGraph α) :
    ∃ v : α, indepNeighborsCard H v = localIndependenceMin H := by
  obtain ⟨v, _, hv⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (indepNeighborsCard H)
  exact ⟨v, hv.symm⟩

private lemma nonadjacent_nonneighbors_of_indepNeighborsCard_compl_eq_one
    (G : SimpleGraph α) [DecidableRel G.Adj] {v : α}
    (hv : indepNeighborsCard Gᶜ v = 1) :
    ∀ ⦃x y : α⦄, Gᶜ.Adj v x → Gᶜ.Adj v y → ¬G.Adj x y := by
  intro x y hvx hvy hxy
  let x' : (Gᶜ).neighborSet v := ⟨x, hvx⟩
  let y' : (Gᶜ).neighborSet v := ⟨y, hvy⟩
  have hxy' : x' ≠ y' := by
    intro h
    apply hxy.ne
    exact congrArg Subtype.val h
  have hind : ((Gᶜ).induce ((Gᶜ).neighborSet v)).IsIndepSet
      ({x', y'} : Finset ((Gᶜ).neighborSet v)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · simp [x', y', hxy]
    · simp [x', y', hxy.symm]
    · exact (hab rfl).elim
  have hle := hind.card_le_indepNum
  have htwo : 2 ≤ indepNeighborsCard Gᶜ v := by
    simpa [indepNeighborsCard, Finset.card_pair hxy'] using hle
  omega

/-- If `localIndependenceMin Gᶜ = 1`, some vertex is within distance two of all
vertices. -/
lemma exists_center_dist_le_two_of_localIndependenceMin_compl_eq_one
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hm : localIndependenceMin Gᶜ = 1) :
    ∃ v : α, ∀ x : α, G.dist v x ≤ 2 := by
  obtain ⟨v, hv⟩ := exists_localIndependenceMin_eq (Gᶜ)
  have hvone : indepNeighborsCard Gᶜ v = 1 := hv.trans hm
  have hnon := nonadjacent_nonneighbors_of_indepNeighborsCard_compl_eq_one G hvone
  refine ⟨v, fun x => ?_⟩
  by_cases hxv : x = v
  · subst x
    simp
  by_cases hvx : G.Adj v x
  · exact (G.dist_le hvx.toWalk).trans (by norm_num)
  have hvne : v ≠ x := Ne.symm hxv
  have hcvx : Gᶜ.Adj v x := by
    simp [hvne, hvx]
  have hxs : x ∈ G.support := by
    rw [hG.preconnected.support_eq_univ]
    simp
  obtain ⟨z, hxz⟩ := (mem_support G).mp hxs
  have hvz : G.Adj v z := by
    by_contra hn
    have hzv : z ≠ v := by
      intro hzv
      subst z
      exact hvx hxz.symm
    have hvz_ne : v ≠ z := Ne.symm hzv
    have hcvz : Gᶜ.Adj v z := by
      simp [hvz_ne, hn]
    exact (hnon hcvx hcvz) hxz
  exact WOW145.dist_le_two_of_adj_adj G hvz hxz.symm

/-- The natural-valued radius is at most two in the hard local branch. -/
lemma radius_toNat_le_two_of_localIndependenceMin_compl_eq_one
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hm : localIndependenceMin Gᶜ = 1) :
    G.radius.toNat ≤ 2 := by
  obtain ⟨v, hv⟩ :=
    exists_center_dist_le_two_of_localIndependenceMin_compl_eq_one G hG hm
  have hecc : G.eccent v ≤ (2 : ℕ∞) := by
    rw [eccent_le_iff]
    intro x
    rw [← (hG v x).coe_dist_eq_edist]
    exact_mod_cast hv x
  have hr : G.radius ≤ (2 : ℕ∞) := radius_le_eccent.trans hecc
  simpa using ENat.toNat_le_toNat hr (by simp)

#print axioms WOW145.exists_center_dist_le_two_of_localIndependenceMin_compl_eq_one
#print axioms WOW145.radius_toNat_le_two_of_localIndependenceMin_compl_eq_one

end WOW145
