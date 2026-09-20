import JSP415.BipLemmas

/-!
# Shared interface for the `bip_ramsey_path` effort.

Everything here depends only on `JSP415.BipLemmas`.  Each trial agent proves
its assigned lemma(s) in its own scratch file under the agreed names; the
coordinator integrates them into `BipLemmas.lean`.
-/

open Finset
open Classical

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The conclusion of `bip_ramsey_path` and of every milestone lemma:
a red `acrossXY`-chain on `k + 1` vertices or a blue one on `ℓ + 1`. -/
abbrev BipGoal (G : SimpleGraph V) (X Y : Finset V) (k ℓ : ℕ) : Prop :=
  ∃ p : VertPath V,
    (p.toList.IsChain (Color.adjXY G X Y .red) ∧ k + 1 ≤ p.toList.length) ∨
    (p.toList.IsChain (Color.adjXY G X Y .blue) ∧ ℓ + 1 ≤ p.toList.length)

/-- **Case (iii) data** (Gyárfás–Lehel Thm 3): a maximal red-first bipath
`(A, z, B)` whose endpoints `A.head`, `B.getLast` lie in `Y`, whose midpoint
`z` lies in `X`, with leftover vertices in *both* classes.  The killing
lemmas (`bipathO_leftover_opp_of_diff_ends`,
`bipathO_leftover_opp_of_same_ends`) reduce `bip_ramsey_path` to this
configuration. -/
structure Case3Data (G : SimpleGraph V) (X Y : Finset V) where
  A : List V
  z : V
  B : List V
  hb : IsBipath G X Y A z B
  hmax : ∀ A' z' B', IsBipathO G X Y A' z' B' →
    bipathLen A' z' B' ≤ bipathLen A z B
  hz : z ∈ X
  hA : A ≠ []
  hB : B ≠ []
  hhead : A.head hA ∈ Y
  hlast : B.getLast hB ∈ Y
  ux : V
  hux : ux ∈ X ∧ ux ∉ A ++ z :: B
  uy : V
  huy : uy ∈ Y ∧ uy ∉ A ++ z :: B

namespace Case3Data

variable {G : SimpleGraph V} {X Y : Finset V} (c3 : Case3Data G X Y)

/-- The vertex list of the bipath. -/
abbrev S (c3 : Case3Data G X Y) : List V := c3.A ++ c3.z :: c3.B

/-- The red branch `S₁ = A ++ [z]`. -/
abbrev S1 (c3 : Case3Data G X Y) : List V := c3.A ++ [c3.z]

/-- The blue branch `S₂ = z :: B`. -/
abbrev S2 (c3 : Case3Data G X Y) : List V := c3.z :: c3.B

/-- Upper (`Y`-side) vertices of `S₁`: the odd-indexed `Aᵢ`. -/
abbrev S1U (c3 : Case3Data G X Y) : Finset V :=
  (c3.S1.toFinset).filter (· ∈ Y)

/-- Upper (`Y`-side) vertices of `S₂`: the odd-indexed `Bⱼ`. -/
abbrev S2U (c3 : Case3Data G X Y) : Finset V :=
  (c3.S2.toFinset).filter (· ∈ Y)

/-- All lower (`X`-side) vertices of `S`: the even-indexed `Aᵢ`, `z`, and
the even-indexed `Bⱼ`. -/
abbrev SL (c3 : Case3Data G X Y) : Finset V :=
  (c3.S.toFinset).filter (· ∈ X)

/-- Upper (`Y`-side) leftover vertices joined to `z` by a red edge. -/
noncomputable abbrev sc1 (c3 : Case3Data G X Y) : Finset V :=
  (Y \ c3.S.toFinset).filter (fun w ↦ G.Adj w c3.z)

/-- Upper leftover vertices joined to `z` by a blue edge. -/
noncomputable abbrev sc2 (c3 : Case3Data G X Y) : Finset V :=
  (Y \ c3.S.toFinset).filter (fun w ↦ ¬ G.Adj w c3.z)

/-- The two red complete-bipartite blocks of the GL decomposition. -/
noncomputable abbrev U1 (c3 : Case3Data G X Y) : Finset V := c3.S1U ∪ c3.sc1
noncomputable abbrev U2 (c3 : Case3Data G X Y) : Finset V := c3.S2U ∪ c3.sc2
abbrev L1 (c3 : Case3Data G X Y) : Finset V := c3.SL
abbrev L2 (c3 : Case3Data G X Y) : Finset V := X \ c3.S.toFinset

/-- **Internal facts E+F** (the target of the "internal claims" agent):
the red branch `S₁` is red-complete towards every `X`-side vertex of `S`,
and the blue branch `S₂` is blue-complete towards every `X`-side vertex of
`S`. -/
abbrev InternalFacts (c3 : Case3Data G X Y) : Prop :=
  (∀ u ∈ c3.S1U, ∀ l ∈ c3.SL, G.Adj u l) ∧
  (∀ u ∈ c3.S2U, ∀ l ∈ c3.SL, ¬ G.Adj u l)

/-- **Leftover facts C+G+H** (the target of the "leftover claims" agent):
lower leftovers are blue to `S₁`-upper and red to `S₂`-upper; upper
leftovers inherit their `z`-colour towards all of `SL`; lower leftovers
are blue to `sc1` and red to `sc2`. -/
abbrev LeftoverFacts (c3 : Case3Data G X Y) : Prop :=
  (∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u) ∧
  (∀ w ∈ c3.L2, ∀ u ∈ c3.S2U, G.Adj w u) ∧
  (∀ w ∈ c3.sc1, ∀ l ∈ c3.SL, G.Adj w l) ∧
  (∀ w ∈ c3.sc2, ∀ l ∈ c3.SL, ¬ G.Adj w l) ∧
  (∀ w ∈ c3.L2, ∀ u ∈ c3.sc1, ¬ G.Adj w u) ∧
  (∀ w ∈ c3.L2, ∀ u ∈ c3.sc2, G.Adj w u)

end Case3Data

end JSP415
