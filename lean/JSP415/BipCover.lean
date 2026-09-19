import JSP415.BipLemmas

/-!
# Bipartite covering lemmas (PVW24 Lemmas 2.2–2.4)

Path-covering lemmas for bipartite graphs with degree conditions.
-/

open Finset

namespace JSP415

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PVW24 Lemma 2.2.**  If every vertex of `Y` has degree at least
`(|X| + |Y|)/2` in the bipartite graph `G`, then `G` contains a path covering
all of `Y`, with `2|Y|` vertices. -/
theorem path_cover_two_mul (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (hbip : BipartiteOn G X Y)
    (hdeg : ∀ y ∈ Y, 2 * (G.neighborFinset y).card ≥ X.card + Y.card) :
    ∃ p : VertPath V, p.toList.IsChain G.Adj ∧
      (∀ v ∈ p.toList, v ∈ X ∪ Y) ∧ (∀ y ∈ Y, y ∈ p) ∧
      p.toList.length = 2 * Y.card := by
  sorry

/-- **PVW24 Lemma 2.3.**  If `|X| ≥ |Y| + 2m` and every `y ∈ Y` has degree at
least `|X| − m`, then at most `⌊|X|/|Y|⌋` paths cover all of `Y` and all but
`|Y| + 2m` vertices of `X`. -/
theorem few_paths_of_min_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (m : ℕ) (hbip : BipartiteOn G X Y)
    (hY : 0 < Y.card)
    (hcard : Y.card + 2 * m ≤ X.card)
    (hdeg : ∀ y ∈ Y, (G.neighborFinset y).card ≥ X.card - m) :
    ∃ P : Finset (VertPath V),
      (∀ p ∈ P, p.toList.IsChain G.Adj) ∧
      (∀ p ∈ P, ∀ v ∈ p.toList, v ∈ X ∪ Y) ∧
      (∀ y ∈ Y, ∃ p ∈ P, y ∈ p) ∧
      P.card ≤ X.card / Y.card ∧
      (X \ P.biUnion VertPath.verts).card ≤ Y.card + 2 * m := by
  sorry

/-- **PVW24 Lemma 2.4.**  Refined covering lemma: with
`X₀ = {x ∈ X : d(x) = |Y|}`, `X₁ = X ∖ X₀`, `Y₀ = {y ∈ Y : d(y) = |X|} ≠ ∅`,
`Y₁ = Y ∖ Y₀`, if `|X| > |Y|` and either `X₁ = Y₁ = ∅` or
`|X₀|/|Y₁| > 2|X₁|/|Y₀|`, then `⌈|X|/(|Y|+1)⌉` paths cover all of `X ∪ Y`. -/
theorem refined_path_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (hbip : BipartiteOn G X Y)
    (hcard : Y.card < X.card)
    (hY0 : (fullNbr G Y X).Nonempty)
    (hcond : (X \ fullNbr G X Y = ∅ ∧ Y \ fullNbr G Y X = ∅) ∨
      ((fullNbr G X Y).card : ℝ) / ((Y \ fullNbr G Y X).card : ℝ) >
        2 * ((X \ fullNbr G X Y).card : ℝ) / ((fullNbr G Y X).card : ℝ)) :
    ∃ P : Finset (VertPath V),
      (∀ p ∈ P, p.toList.IsChain G.Adj) ∧
      (∀ v ∈ X ∪ Y, ∃ p ∈ P, v ∈ p) ∧
      P.card ≤ (X.card + Y.card) / (Y.card + 1) := by
  sorry

end JSP415
