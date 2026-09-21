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
`z` lies in `X`, with a leftover vertex `ux` in `z`'s class `X`.  The killing
lemmas (`bipathO_leftover_opp_of_diff_ends`,
`bipathO_leftover_opp_of_same_ends`) reduce `bip_ramsey_path` to this
configuration.  (In the "proper" case (iii) a `Y`-leftover exists as well;
the tight parity subcase has `Y ⊆ S` and only the `X`-leftover — the claims
below are stated so that they only ever need `ux` plus the vertex being
classified.) -/
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

/-- **Claim A** (GL73): the outer edges `A₁–X` (red) and `X–Bₛ` (blue) are
forced by maximality; proved by the equal-length rotations
`S' = (A.tail.reverse, A.head, z::B)` and `S' = (A++[z], B.getLast,
B.dropLast.reverse)` killed by `bipathO_kill_Ymid`. -/
abbrev ClaimA (c3 : Case3Data G X Y) : Prop :=
  Color.adjXY G X Y .red (c3.A.head c3.hA) c3.z ∧
  Color.adjXY G X Y .blue c3.z (c3.B.getLast c3.hB)

/-- **Claim F** (GL73): `Y`-side vertices of `S₁` are red-joined to
`X`-side vertices of `B`; `X`-side vertices of `A` are blue-joined to
`Y`-side vertices of `S₂`.  (`l ∈ c3.B` / `l ∈ c3.A` is `List.mem`.) -/
abbrev ClaimF (c3 : Case3Data G X Y) : Prop :=
  (∀ u ∈ c3.S1U, ∀ l ∈ c3.SL, l ∈ c3.B → G.Adj u l) ∧
  (∀ l ∈ c3.SL, l ∈ c3.A → ∀ u ∈ c3.S2U, ¬ G.Adj l u)

/-- **Claims C+C'** (GL73): every lower leftover `w` is blue to `S₁`-uppers
and red to `S₂`-uppers — the first two clauses of `LeftoverFacts`. -/
abbrev LeftoverC (c3 : Case3Data G X Y) : Prop :=
  (∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u) ∧
  (∀ w ∈ c3.L2, ∀ u ∈ c3.S2U, G.Adj w u)

/-- **Claims G+H** (GL73): upper leftovers inherit their `z`-colour towards
`SL`, and lower leftovers are blue to `sc1`, red to `sc2` — the last four
clauses of `LeftoverFacts`. -/
abbrev GHfacts (c3 : Case3Data G X Y) : Prop :=
  (∀ w ∈ c3.sc1, ∀ l ∈ c3.SL, G.Adj w l) ∧
  (∀ w ∈ c3.sc2, ∀ l ∈ c3.SL, ¬ G.Adj w l) ∧
  (∀ w ∈ c3.L2, ∀ u ∈ c3.sc1, ¬ G.Adj w u) ∧
  (∀ w ∈ c3.L2, ∀ u ∈ c3.sc2, G.Adj w u)

/-- A second distinct lower leftover; available whenever `|X ∖ S| ≥ 2`
(proper case (iii)).  Claim-D rotations thread both `ux` and `u₂`. -/
abbrev HasUx2 (c3 : Case3Data G X Y) : Prop :=
  ∃ u₂, u₂ ∈ X ∧ u₂ ∉ c3.A ++ c3.z :: c3.B ∧ u₂ ≠ c3.ux

theorem leftoverFacts_of_C_GH (c3 : Case3Data G X Y) (hC : LeftoverC c3)
    (hGH : GHfacts c3) : c3.LeftoverFacts :=
  ⟨hC.1, hC.2, hGH.1, hGH.2.1, hGH.2.2.1, hGH.2.2.2⟩

/-- Claim E (GL73): the red branch `S₁` is internally red-complete — every
`Y`-side vertex of `S₁` is `G`-adjacent to every `X`-side vertex of `S` that
lies in `S₁` (i.e. in `A` or equal to `z`). -/
abbrev ClaimE (c3 : Case3Data G X Y) : Prop :=
  ∀ u ∈ c3.S1U, ∀ l ∈ c3.SL, (l ∈ c3.A ∨ l = c3.z) → G.Adj u l

/-- Claim E′ (mirror of E): the blue branch `S₂` is internally blue-complete —
every `Y`-side vertex of `S₂` is non-`G`-adjacent to every `X`-side vertex of
`S` lying in `S₂` (i.e. in `B` or equal to `z`). -/
abbrev ClaimE' (c3 : Case3Data G X Y) : Prop :=
  ∀ u ∈ c3.S2U, ∀ l ∈ c3.SL, (l ∈ c3.B ∨ l = c3.z) → ¬ G.Adj u l

/-- Claim B′ (GL73): the `S₂`-endpoint `B.head` is blue to every `X`-side
vertex of `A` — the `a`-even–`b₁` junction used in claim C's bipath. -/
abbrev ClaimB' (c3 : Case3Data G X Y) : Prop :=
  ∀ l ∈ c3.SL, l ∈ c3.A → ¬ G.Adj l (c3.B.head c3.hB)

/-- Assembling `InternalFacts`: internal completeness (`ClaimE`, `ClaimE'`)
plus the cross completeness (`ClaimF`) give the two block facts. -/
theorem internalFacts_of_E_F (c3 : Case3Data G X Y)
    (hE : c3.ClaimE) (hE' : c3.ClaimE') (hF : c3.ClaimF) :
    c3.InternalFacts := by
  obtain ⟨hF1, hF2⟩ := hF
  have hmem : ∀ l ∈ c3.SL, l ∈ c3.A ∨ l = c3.z ∨ l ∈ c3.B := by
    intro l hl
    have h : l ∈ c3.A ++ c3.z :: c3.B :=
      List.mem_toFinset.mp (Finset.mem_filter.mp hl).1
    rw [List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine ⟨fun u hu l hl ↦ ?_, fun u hu l hl ↦ ?_⟩
  · rcases hmem l hl with h | h | h
    · exact hE u hu l hl (Or.inl h)
    · exact hE u hu l hl (Or.inr h)
    · exact hF1 u hu l hl h
  · rcases hmem l hl with h | h | h
    · exact fun hadj ↦ hF2 l hl h u hu hadj.symm
    · exact hE' u hu l hl (Or.inr h)
    · exact hE' u hu l hl (Or.inl h)

end Case3Data

end JSP415
