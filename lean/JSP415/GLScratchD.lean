import JSP415.BipLemmas

/-!
# GL finale: the two-block counting lemma (Gyárfás–Lehel Thm 3, case (iii))

In case (iii) of the GL73 argument the red graph on `X ∪ Y` decomposes into
exactly two complete-bipartite blocks `(U₁', L₁')` and `(U₂', L₂')` (with the
`U`'s on the `Y`-side and the `L`'s on the `X`-side), while every cross-block
pair `U₁' × L₂'`, `U₂' × L₁'` is blue.  This file formalizes the closing
counting argument: either one of the red blocks already contains a red
alternating path on `k + 1` vertices, or one of the blue cross pairs contains
a blue alternating path on `ℓ + 1` vertices.

* `two_block_count` — the pure arithmetic heart (a `min`-inequality case
  bash, discharged by `omega`).
* `two_block_ramsey` — the reusable finale: from the partition and the four
  completeness facts, produce the Ramsey disjunction.
* `red_path_covers` / `blue_path_covers` — layer-1 corollaries of
  `red_long_path` / `blue_long_path`: a balanced monochromatic-complete
  bipartite pair is covered by a single alternating path.
-/

open Finset

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Layer 1: block path covers -/

/-- If a red-complete bipartite pair `A ⊆ X`, `B ⊆ Y` is balanced
(`|A.card - B.card| ≤ 1`), `red_long_path` covers all `|A| + |B|` vertices. -/
theorem red_path_covers {G : SimpleGraph V} {X Y A B : Finset V}
    (hXY : Disjoint X Y) (hAX : A ⊆ X) (hBY : B ⊆ Y)
    (hb : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAbal : A.card ≤ B.card + 1) (hBbal : B.card ≤ A.card + 1) :
    ∃ p : VertPath V, p.toList.IsChain (Color.adjXY G X Y .red) ∧
      p.toList.length = A.card + B.card := by
  obtain ⟨p, hch, hlen⟩ := red_long_path hXY hAX hBY hb hA hB
  exact ⟨p, hch, by rw [hlen]; omega⟩

/-- Threshold form of `red_long_path`: any `n` below the guaranteed length is
achieved. -/
theorem red_long_path_ge {G : SimpleGraph V} {X Y A B : Finset V}
    (hXY : Disjoint X Y) (hAX : A ⊆ X) (hBY : B ⊆ Y)
    (hb : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hA : A.Nonempty) (hB : B.Nonempty) {n : ℕ}
    (hn : n ≤ min (A.card + B.card) (2 * min A.card B.card + 1)) :
    ∃ p : VertPath V, p.toList.IsChain (Color.adjXY G X Y .red) ∧
      n ≤ p.toList.length := by
  obtain ⟨p, hch, hlen⟩ := red_long_path hXY hAX hBY hb hA hB
  exact ⟨p, hch, by rw [hlen]; exact hn⟩

/-- Blue analogue of `red_path_covers`. -/
theorem blue_path_covers {G : SimpleGraph V} {X Y A B : Finset V}
    (hXY : Disjoint X Y) (hAX : A ⊆ X) (hBY : B ⊆ Y)
    (hb : ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAbal : A.card ≤ B.card + 1) (hBbal : B.card ≤ A.card + 1) :
    ∃ p : VertPath V, p.toList.IsChain (Color.adjXY G X Y .blue) ∧
      p.toList.length = A.card + B.card := by
  obtain ⟨p, hch, hlen⟩ := blue_long_path hXY hAX hBY hb hA hB
  exact ⟨p, hch, by rw [hlen]; omega⟩

/-- Threshold form of `blue_long_path`. -/
theorem blue_long_path_ge {G : SimpleGraph V} {X Y A B : Finset V}
    (hXY : Disjoint X Y) (hAX : A ⊆ X) (hBY : B ⊆ Y)
    (hb : ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b)
    (hA : A.Nonempty) (hB : B.Nonempty) {n : ℕ}
    (hn : n ≤ min (A.card + B.card) (2 * min A.card B.card + 1)) :
    ∃ p : VertPath V, p.toList.IsChain (Color.adjXY G X Y .blue) ∧
      n ≤ p.toList.length := by
  obtain ⟨p, hch, hlen⟩ := blue_long_path hXY hAX hBY hb hA hB
  exact ⟨p, hch, by rw [hlen]; exact hn⟩

/-! ### Layer 2: the two-block counting lemma -/

/-- `min (a+b) (2·min a b + 1)` is symmetric in `a b`. -/
private theorem pathlen_comm (a b : ℕ) :
    min (a + b) (2 * min a b + 1) = min (b + a) (2 * min b a + 1) := by
  rw [Nat.add_comm a b, Nat.min_comm a b]

/-- The arithmetic heart of the GL finale.  If the red graph on `X ∪ Y`
(`|X| = |Y| = m`, `k + ℓ ≤ 2m`, `k ≠ ℓ`) splits into two complete-bipartite
blocks `(u₁, l₁)`, `(u₂, l₂)` and every cross pair `(u₁, l₂)`, `(u₂, l₁)` is
blue, then it is impossible that both red blocks have longest alternating
path `< k + 1` vertices *and* both blue cross pairs have longest alternating
path `< ℓ + 1` vertices.  (The longest alternating path in `K_{a,b}` has
`min (a + b) (2 min a b + 1)` vertices.) -/
theorem two_block_count {u₁ u₂ l₁ l₂ m k ℓ : ℕ}
    (hu : u₁ + u₂ = m) (hl : l₁ + l₂ = m)
    (hm : k + ℓ ≤ 2 * m) (hkl : k ≠ ℓ)
    (h1 : min (u₁ + l₁) (2 * min u₁ l₁ + 1) ≤ k)
    (h2 : min (u₂ + l₂) (2 * min u₂ l₂ + 1) ≤ k)
    (h3 : min (u₁ + l₂) (2 * min u₁ l₂ + 1) ≤ ℓ)
    (h4 : min (u₂ + l₁) (2 * min u₂ l₁ + 1) ≤ ℓ) : False := by
  omega

/-- **The GL finale.**  Suppose the bipartition `X ⊔ Y` (with
`|X| = |Y| = (k+ℓ+1)/2`, `k ≠ ℓ`) splits as `Y = U₁ ⊔ U₂`, `X = L₁ ⊔ L₂`
such that `U₁ × L₁` and `U₂ × L₂` are entirely red while `U₁ × L₂` and
`U₂ × L₁` are entirely blue.  Then there is a red `adjXY`-path on `k + 1`
vertices or a blue one on `ℓ + 1` vertices.

This is exactly what the case-(iii) rotation analysis produces: take
`U₁' = S₁-upper ∪ 𝒮₁`, `L₁' =` lower vertices of `S`, `U₂' = S₂-upper ∪ 𝒮₂`,
`L₂' = X ∖ S`. -/
theorem two_block_ramsey {G : SimpleGraph V} {X Y : Finset V}
    (hXY : Disjoint X Y) {k ℓ : ℕ} (hkl : k ≠ ℓ)
    (hX : X.card = (k + ℓ + 1) / 2) (hY : Y.card = (k + ℓ + 1) / 2)
    {U₁ U₂ L₁ L₂ : Finset V}
    (hU : U₁ ∪ U₂ = Y) (hUd : Disjoint U₁ U₂)
    (hL : L₁ ∪ L₂ = X) (hLd : Disjoint L₁ L₂)
    (hred₁ : ∀ u ∈ U₁, ∀ l ∈ L₁, G.Adj u l)
    (hred₂ : ∀ u ∈ U₂, ∀ l ∈ L₂, G.Adj u l)
    (hblue₁ : ∀ u ∈ U₁, ∀ l ∈ L₂, ¬G.Adj u l)
    (hblue₂ : ∀ u ∈ U₂, ∀ l ∈ L₁, ¬G.Adj u l) :
    ∃ p : VertPath V,
      (p.toList.IsChain (Color.adjXY G X Y .red) ∧ k + 1 ≤ p.toList.length) ∨
      (p.toList.IsChain (Color.adjXY G X Y .blue) ∧ ℓ + 1 ≤ p.toList.length) := by
  have hm : k + ℓ ≤ 2 * ((k + ℓ + 1) / 2) := by omega
  have hUc : U₁.card + U₂.card = (k + ℓ + 1) / 2 := by
    rw [← hY, ← hU]
    exact (Finset.card_union_of_disjoint hUd).symm
  have hLc : L₁.card + L₂.card = (k + ℓ + 1) / 2 := by
    rw [← hX, ← hL]
    exact (Finset.card_union_of_disjoint hLd).symm
  have hU₁sub : U₁ ⊆ Y := by rw [← hU]; exact Finset.subset_union_left
  have hU₂sub : U₂ ⊆ Y := by rw [← hU]; exact Finset.subset_union_right
  have hL₁sub : L₁ ⊆ X := by rw [← hL]; exact Finset.subset_union_left
  have hL₂sub : L₂ ⊆ X := by rw [← hL]; exact Finset.subset_union_right
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: any single vertex is a (vacuously) red 1-vertex chain.
    subst hk0
    have hYpos : 0 < Y.card := by rw [hY]; omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hYpos
    exact ⟨VertPath.singleton v,
      Or.inl ⟨List.isChain_singleton v, by simp [VertPath.singleton]⟩⟩
  rcases Nat.eq_zero_or_pos ℓ with hl0 | hlpos
  · -- `ℓ = 0`: any single vertex is a blue 1-vertex chain.
    subst hl0
    have hXpos : 0 < X.card := by rw [hX]; omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hXpos
    exact ⟨VertPath.singleton v,
      Or.inr ⟨List.isChain_singleton v, by simp [VertPath.singleton]⟩⟩
  -- `k, ℓ ≥ 1`: the counting disjunction.
  have key :
      k + 1 ≤ min (U₁.card + L₁.card) (2 * min U₁.card L₁.card + 1) ∨
      k + 1 ≤ min (U₂.card + L₂.card) (2 * min U₂.card L₂.card + 1) ∨
      ℓ + 1 ≤ min (U₁.card + L₂.card) (2 * min U₁.card L₂.card + 1) ∨
      ℓ + 1 ≤ min (U₂.card + L₁.card) (2 * min U₂.card L₁.card + 1) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3, h4⟩ := hcon
    exact two_block_count hUc hLc hm hkl
      (Nat.le_of_lt_succ h1) (Nat.le_of_lt_succ h2)
      (Nat.le_of_lt_succ h3) (Nat.le_of_lt_succ h4)
  have ne_of_bound {a b n : ℕ} (hn : 2 ≤ n)
      (h : n ≤ min (a + b) (2 * min a b + 1)) : 0 < a ∧ 0 < b := by
    omega
  rcases key with hR1 | hR2 | hB1 | hB2
  · -- Red block 1 is large enough.
    obtain ⟨hU₁pos, hL₁pos⟩ := ne_of_bound (by omega) hR1
    obtain ⟨p, hch, hlen⟩ := red_long_path hXY hL₁sub hU₁sub
      (fun a ha b hb ↦ (hred₁ b hb a ha).symm)
      (Finset.card_pos.mp hL₁pos) (Finset.card_pos.mp hU₁pos)
    refine ⟨p, Or.inl ⟨hch, ?_⟩⟩
    rw [hlen, pathlen_comm]
    exact hR1
  · -- Red block 2 is large enough.
    obtain ⟨hU₂pos, hL₂pos⟩ := ne_of_bound (by omega) hR2
    obtain ⟨p, hch, hlen⟩ := red_long_path hXY hL₂sub hU₂sub
      (fun a ha b hb ↦ (hred₂ b hb a ha).symm)
      (Finset.card_pos.mp hL₂pos) (Finset.card_pos.mp hU₂pos)
    refine ⟨p, Or.inl ⟨hch, ?_⟩⟩
    rw [hlen, pathlen_comm]
    exact hR2
  · -- Blue cross pair `(U₁, L₂)` is large enough.
    obtain ⟨hU₁pos, hL₂pos⟩ := ne_of_bound (by omega) hB1
    obtain ⟨p, hch, hlen⟩ := blue_long_path hXY hL₂sub hU₁sub
      (fun a ha b hb ↦ fun hadj ↦ hblue₁ b hb a ha hadj.symm)
      (Finset.card_pos.mp hL₂pos) (Finset.card_pos.mp hU₁pos)
    refine ⟨p, Or.inr ⟨hch, ?_⟩⟩
    rw [hlen, pathlen_comm]
    exact hB1
  · -- Blue cross pair `(U₂, L₁)` is large enough.
    obtain ⟨hU₂pos, hL₁pos⟩ := ne_of_bound (by omega) hB2
    obtain ⟨p, hch, hlen⟩ := blue_long_path hXY hL₁sub hU₂sub
      (fun a ha b hb ↦ fun hadj ↦ hblue₂ b hb a ha hadj.symm)
      (Finset.card_pos.mp hL₁pos) (Finset.card_pos.mp hU₂pos)
    refine ⟨p, Or.inr ⟨hch, ?_⟩⟩
    rw [hlen, pathlen_comm]
    exact hB2

/-- The finale with the same conclusion as `bip_ramsey_path`: the hypotheses
are precisely the two-block decomposition that case (iii) of the GL argument
produces (`S₁ = A ++ [z]` red-complete, `S₂ = z :: B` blue-complete, plus
propositions F–H). -/
theorem bip_ramsey_path_D (G : SimpleGraph V) (X Y : Finset V)
    (hXY : Disjoint X Y) {k ℓ : ℕ} (hkl : k ≠ ℓ)
    (hX : X.card = (k + ℓ + 1) / 2) (hY : Y.card = (k + ℓ + 1) / 2)
    (U₁ U₂ L₁ L₂ : Finset V)
    (hU : U₁ ∪ U₂ = Y) (hUd : Disjoint U₁ U₂)
    (hL : L₁ ∪ L₂ = X) (hLd : Disjoint L₁ L₂)
    (hred₁ : ∀ u ∈ U₁, ∀ l ∈ L₁, G.Adj u l)
    (hred₂ : ∀ u ∈ U₂, ∀ l ∈ L₂, G.Adj u l)
    (hblue₁ : ∀ u ∈ U₁, ∀ l ∈ L₂, ¬G.Adj u l)
    (hblue₂ : ∀ u ∈ U₂, ∀ l ∈ L₁, ¬G.Adj u l) :
    ∃ p : VertPath V,
      (p.toList.IsChain (Color.adjXY G X Y .red) ∧ k + 1 ≤ p.toList.length) ∨
      (p.toList.IsChain (Color.adjXY G X Y .blue) ∧ ℓ + 1 ≤ p.toList.length) :=
  two_block_ramsey hXY hkl hX hY hU hUd hL hLd hred₁ hred₂ hblue₁ hblue₂

end JSP415
