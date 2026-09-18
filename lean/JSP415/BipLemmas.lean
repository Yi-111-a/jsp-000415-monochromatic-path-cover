import JSP415.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Bipartite lemmas (PVW24 Section 2)

Lemmas 2.1–2.4 of Pokrovskiy–Versteegen–Williams.  A "bipartite graph on
`X ∪ Y`" is a `SimpleGraph V` all of whose edges cross `X`–`Y`; in the
red–blue setting, blue adjacency across the bipartition means non-`G`-adjacent
pairs `(x, y)` with `x ∈ X, y ∈ Y` (in either order).
-/

open Finset

namespace JSP415

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both endpoints lie in the bipartition, on opposite sides. -/
def acrossXY (X Y : Finset V) (a b : V) : Prop :=
  (a ∈ X ∧ b ∈ Y) ∨ (a ∈ Y ∧ b ∈ X)

/-- Colour-`c` adjacency restricted to the bipartition `X Y`: an edge of the
(complete) bipartite graph coloured `c`. -/
def Color.adjXY (G : SimpleGraph V) (X Y : Finset V) : Color → V → V → Prop
  | .red, a, b => acrossXY X Y a b ∧ G.Adj a b
  | .blue, a, b => acrossXY X Y a b ∧ ¬G.Adj a b

/-- `G` is a bipartite graph with parts `X`, `Y`: every edge crosses. -/
def BipartiteOn (G : SimpleGraph V) (X Y : Finset V) : Prop :=
  Disjoint X Y ∧ ∀ a b : V, G.Adj a b → acrossXY X Y a b

/-- Vertices of one part adjacent to *all* vertices of the other part
(the `X₀`/`Y₀` of Lemma 2.4). -/
def fullNbr (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : Finset V :=
  X.filter fun x ↦ (G.neighborFinset x).card = Y.card

/-- **Gyárfás–Lehel 1973** (PVW24 Lemma 2.1).  For distinct `k ℓ`, every
red–blue edge colouring of the complete bipartite graph
`K_{⌈(k+ℓ)/2⌉,⌈(k+ℓ)/2⌉}` contains a red path on `k+1` vertices or a blue
path on `ℓ+1` vertices. -/
theorem bip_ramsey_path (G : SimpleGraph V) (X Y : Finset V)
    (hXY : Disjoint X Y) {k ℓ : ℕ} (hkl : k ≠ ℓ)
    (hX : X.card = (k + ℓ + 1) / 2) (hY : Y.card = (k + ℓ + 1) / 2) :
    ∃ p : VertPath V,
      (p.toList.IsChain (Color.adjXY G X Y .red) ∧ k + 1 ≤ p.toList.length) ∨
      (p.toList.IsChain (Color.adjXY G X Y .blue) ∧ ℓ + 1 ≤ p.toList.length) := by
  sorry

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
