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

import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity
import Lean.Elab.Tactic.Omega

/-!
# The local-independence-one radius bridge

The only new graph-theoretic input needed for WOWII Conjecture 145: if the
minimum local independence number of the complement is one, then the graph has
radius exactly two.
-/

namespace WrittenOnTheWallII.GraphConjecture145

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The minimum local independence number, copied verbatim from the target. -/
noncomputable def localIndependenceMin (G : SimpleGraph α) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (indepNeighborsCard G)

lemma localIndependenceMin_le (G : SimpleGraph α) (v : α) :
    localIndependenceMin G ≤ indepNeighborsCard G v := by
  unfold localIndependenceMin
  exact Finset.inf'_le _ (Finset.mem_univ v)

lemma exists_indepNeighborsCard_eq_localIndependenceMin (G : SimpleGraph α) :
    ∃ v : α, indepNeighborsCard G v = localIndependenceMin G := by
  obtain ⟨v, _, hv⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (indepNeighborsCard G)
  exact ⟨v, hv.symm⟩

/-- Positive local independence at a vertex forces a complement neighbor. -/
lemma exists_neighbor_of_indepNeighborsCard_pos
    (G : SimpleGraph α) (v : α) (hpos : 0 < indepNeighborsCard G v) :
    ∃ w : α, G.Adj v w := by
  change 0 < (G.induce (G.neighborSet v)).indepNum at hpos
  obtain ⟨s, hs⟩ := (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
  have hscard : 0 < s.card := by simpa [hs.card_eq] using hpos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hscard
  exact ⟨w.1, by simpa using w.2⟩

/-- If the complement local independence at `c` is one, then the nonneighbors
of `c` in the original graph form an independent set. -/
lemma compl_neighborSet_isIndepSet_of_indepNeighborsCard_eq_one
    (G : SimpleGraph α) (c : α)
    (hc : indepNeighborsCard Gᶜ c = 1) :
    G.IsIndepSet (Gᶜ.neighborSet c) := by
  intro z hz w hw hzw
  intro hGzw
  let z' : Gᶜ.neighborSet c := ⟨z, hz⟩
  let w' : Gᶜ.neighborSet c := ⟨w, hw⟩
  have hzw' : z' ≠ w' := by
    intro heq
    exact hzw (congrArg Subtype.val heq)
  let s : Finset (Gᶜ.neighborSet c) := {z', w'}
  have hsind : (Gᶜ.induce (Gᶜ.neighborSet c)).IsIndepSet (s : Set _) := by
    intro a ha b hb hab
    simp only [s, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · simpa [SimpleGraph.induce_adj, SimpleGraph.compl_adj, hGzw]
    · simpa [SimpleGraph.induce_adj, SimpleGraph.compl_adj, hGzw.symm]
    · exact (hab rfl).elim
  have hcard := hsind.card_le_indepNum
  have hscard : s.card = 2 := by simp [s, hzw']
  change (Gᶜ.induce (Gᶜ.neighborSet c)).indepNum = 1 at hc
  omega

/-- The hard local branch has radius exactly two. -/
lemma radius_toNat_eq_two_of_localIndependenceMin_eq_one
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hl : localIndependenceMin Gᶜ = 1) :
    G.radius.toNat = 2 := by
  obtain ⟨c, hcmin⟩ := exists_indepNeighborsCard_eq_localIndependenceMin Gᶜ
  have hc : indepNeighborsCard Gᶜ c = 1 := hcmin.trans hl
  have hNind : G.IsIndepSet (Gᶜ.neighborSet c) :=
    compl_neighborSet_isIndepSet_of_indepNeighborsCard_eq_one G c hc

  have hallPos : ∀ v : α, 0 < indepNeighborsCard Gᶜ v := by
    intro v
    have hle := localIndependenceMin_le Gᶜ v
    omega

  have hallDist : ∀ z : α, G.dist c z ≤ 2 := by
    intro z
    by_cases hzc : z = c
    · subst z
      simp
    by_cases hcz : G.Adj c z
    · have : G.dist c z = 1 := dist_eq_one_iff_adj.mpr hcz
      omega
    · have hzN : z ∈ Gᶜ.neighborSet c := by
        rw [mem_neighborSet, compl_adj]
        exact ⟨hzc.symm, hcz⟩
      obtain ⟨w, hzw⟩ := hG.preconnected.exists_adj_of_nontrivial z
      have hwc : w ≠ c := by
        intro hwc
        subst w
        exact hcz hzw.symm
      have hcw : G.Adj c w := by
        by_contra hn
        have hwN : w ∈ Gᶜ.neighborSet c := by
          rw [mem_neighborSet, compl_adj]
          exact ⟨hwc.symm, hn⟩
        exact hNind hzN hwN hzw.ne hzw
      simpa using G.dist_le (.cons hcw (.cons hzw.symm .nil))

  have heccLe : G.eccent c ≤ (2 : ℕ∞) := by
    rw [eccent_le_iff]
    intro z
    rw [← (hG c z).coe_dist_eq_edist]
    exact ENat.coe_le_coe.mpr (hallDist z)
  have hrLe : G.radius ≤ (2 : ℕ∞) := radius_le_eccent.trans heccLe

  have hrGe : (2 : ℕ∞) ≤ G.radius := by
    rw [radius]
    apply le_iInf
    intro v
    obtain ⟨w, hvwCompl⟩ := exists_neighbor_of_indepNeighborsCard_pos Gᶜ v (hallPos v)
    have hvwNe : v ≠ w := Gᶜ.ne_of_adj hvwCompl
    have hvwNot : ¬ G.Adj v w := (compl_adj.mp hvwCompl).2
    have hdist : 2 ≤ G.dist v w := by
      have := (hG v w).one_lt_dist_of_ne_of_not_adj hvwNe hvwNot
      omega
    calc
      (2 : ℕ∞) ≤ G.dist v w := ENat.coe_le_coe.mpr hdist
      _ = G.edist v w := (hG v w).coe_dist_eq_edist
      _ ≤ G.eccent v := edist_le_eccent

  have hr : G.radius = (2 : ℕ∞) := le_antisymm hrLe hrGe
  simpa [hr]

end WrittenOnTheWallII.GraphConjecture145
