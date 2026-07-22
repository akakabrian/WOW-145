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

import WOW145.GlobalBounds

/-!
# Short metric lemmas for the standalone Conjecture 145 exceptional case
-/

open Classical SimpleGraph

namespace WOW145

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Radius two provides a center at original distance at most two from every vertex. -/
lemma exists_center_dist_le_two_of_radius_eq_two
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hr : G.radius.toNat = 2) :
    ∃ c : α, ∀ v : α, G.dist c v ≤ 2 := by
  obtain ⟨c, hc⟩ := G.exists_eccent_eq_radius
  have hefin : G.eccent c ≠ ⊤ := by
    rw [hc]
    exact radius_ne_top_iff.mpr hG
  refine ⟨c, fun v => ?_⟩
  change (G.edist c v).toNat ≤ 2
  calc
    (G.edist c v).toNat ≤ (G.eccent c).toNat :=
      ENat.toNat_le_toNat edist_le_eccent hefin
    _ = G.radius.toNat := congrArg ENat.toNat hc
    _ = 2 := hr

/-- A pair at distance two has a common intermediate neighbor. -/
lemma exists_middle_of_dist_eq_two (G : SimpleGraph α) (hG : G.Connected)
    {u v : α} (huv : G.dist u v = 2) :
    ∃ w : α, G.Adj u w ∧ G.Adj w v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  have hlen : p.length = 2 := hp.trans huv
  let w := p.getVert 1
  refine ⟨w, ?_, ?_⟩
  · have h := p.adj_getVert_succ (show 0 < p.length by omega)
    simpa [w] using h
  · have h := p.adj_getVert_succ (show 1 < p.length by omega)
    have hlast : p.getVert 2 = v := by simpa [hlen] using p.getVert_length
    rw [hlast] at h
    simpa [w] using h

/-- A pair at distance three has a geodesic with two internal vertices. -/
lemma exists_two_middle_of_dist_eq_three (G : SimpleGraph α) (hG : G.Connected)
    {u v : α} (huv : G.dist u v = 3) :
    ∃ b a : α, G.Adj u b ∧ G.Adj b a ∧ G.Adj a v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  have hlen : p.length = 3 := hp.trans huv
  let b := p.getVert 1
  let a := p.getVert 2
  refine ⟨b, a, ?_, ?_, ?_⟩
  · have h := p.adj_getVert_succ (show 0 < p.length by omega)
    simpa [b] using h
  · have h := p.adj_getVert_succ (show 1 < p.length by omega)
    simpa [b, a] using h
  · have h := p.adj_getVert_succ (show 2 < p.length by omega)
    have hlast : p.getVert 3 = v := by simpa [hlen] using p.getVert_length
    rw [hlast] at h
    simpa [a] using h

lemma dist_le_two_of_adj_adj (G : SimpleGraph α) {a b c : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) : G.dist a c ≤ 2 := by
  simpa using G.dist_le (.cons hab (.cons hbc .nil))

lemma dist_le_three_of_adj_adj_adj (G : SimpleGraph α) {a b c d : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) : G.dist a d ≤ 3 := by
  simpa using G.dist_le (.cons hab (.cons hbc (.cons hcd .nil)))

/-- Vertices at distance at least two are nonadjacent. -/
lemma not_adj_of_two_le_dist (G : SimpleGraph α) {u v : α} (h : 2 ≤ G.dist u v) :
    ¬G.Adj u v := by
  intro huv
  have hdist : G.dist u v = 1 := dist_eq_one_iff_adj.mpr huv
  omega

#print axioms WOW145.exists_center_dist_le_two_of_radius_eq_two
#print axioms WOW145.exists_middle_of_dist_eq_two
#print axioms WOW145.exists_two_middle_of_dist_eq_three
#print axioms WOW145.dist_le_two_of_adj_adj
#print axioms WOW145.dist_le_three_of_adj_adj_adj
#print axioms WOW145.not_adj_of_two_le_dist

end WOW145
