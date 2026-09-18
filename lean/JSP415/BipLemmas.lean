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

namespace bip_ramsey_path

variable {G : SimpleGraph V} {X Y : Finset V}

theorem Disjoint.notMem_left {a : V} (hXY : Disjoint X Y) (ha : a ∈ X) : a ∉ Y :=
  Finset.disjoint_left.mp hXY ha

theorem Disjoint.notMem_right {a : V} (hXY : Disjoint X Y) (ha : a ∈ Y) : a ∉ X :=
  Finset.disjoint_left.mp hXY.symm ha

theorem acrossXY.symm {a b : V} (h : acrossXY X Y a b) : acrossXY X Y b a :=
  h.elim (fun h ↦ .inr ⟨h.2, h.1⟩) (fun h ↦ .inl ⟨h.2, h.1⟩)

theorem Color.adjXY.symm {c : Color} {a b : V} (h : Color.adjXY G X Y c a b) :
    Color.adjXY G X Y c b a := by
  cases c with
  | red => exact ⟨acrossXY.symm h.1, h.2.symm⟩
  | blue => exact ⟨acrossXY.symm h.1, fun hba ↦ h.2 hba.symm⟩

theorem Color.adjXY_cases {a b : V} (h : acrossXY X Y a b) :
    Color.adjXY G X Y .red a b ∨ Color.adjXY G X Y .blue a b := by
  by_cases hadj : G.Adj a b
  · exact Or.inl ⟨h, hadj⟩
  · exact Or.inr ⟨h, hadj⟩

theorem acrossXY.left_mem {a b : V} (h : acrossXY X Y a b) : a ∈ X ∨ a ∈ Y :=
  h.elim (fun h ↦ .inl h.1) (fun h ↦ .inr h.1)

theorem acrossXY.right_mem {a b : V} (h : acrossXY X Y a b) : b ∈ X ∨ b ∈ Y :=
  acrossXY.left_mem (acrossXY.symm h)

theorem acrossXY.left_mem_iff {a b : V} (hXY : Disjoint X Y) (h : acrossXY X Y a b) :
    a ∈ X ↔ b ∈ Y := by
  obtain h | h := h
  · exact ⟨fun _ ↦ h.2, fun _ ↦ h.1⟩
  · exact ⟨fun ha ↦ absurd h.1 (Disjoint.notMem_left hXY ha),
           fun hb ↦ absurd h.2 (Disjoint.notMem_right hXY hb)⟩

theorem Color.adjXY.across {c : Color} {a b : V} (h : Color.adjXY G X Y c a b) :
    acrossXY X Y a b := by
  cases c <;> exact h.1

theorem Color.adjXY.left_mem_iff {c : Color} {a b : V} (hXY : Disjoint X Y)
    (h : Color.adjXY G X Y c a b) : a ∈ X ↔ b ∈ Y :=
  acrossXY.left_mem_iff hXY (Color.adjXY.across h)

theorem Color.adjXY.right_mem_iff {c : Color} {a b : V} (hXY : Disjoint X Y)
    (h : Color.adjXY G X Y c a b) : a ∈ Y ↔ b ∈ X := by
  obtain h' | h' := Color.adjXY.across h
  · exact ⟨fun ha ↦ absurd h'.1 (Disjoint.notMem_right hXY ha),
           fun hb ↦ absurd h'.2 (Disjoint.notMem_left hXY hb)⟩
  · exact ⟨fun _ ↦ h'.2, fun _ ↦ h'.1⟩

/-- In a chain over `adjXY`, consecutive vertices lie on opposite sides:
`l[i] ∈ X ↔ l[i+1] ∈ Y` and `l[i] ∈ Y ↔ l[i+1] ∈ X`. -/
theorem Color.adjXY.next_mem_iff {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y) {i : ℕ}
    (hi : i + 1 < l.length) :
    (l[i] ∈ X ↔ l[i+1] ∈ Y) ∧ (l[i] ∈ Y ↔ l[i+1] ∈ X) := by
  have hedge : Color.adjXY G X Y c l[i] l[i+1] := by
    rw [List.isChain_iff_getElem] at h
    exact h i hi
  exact ⟨Color.adjXY.left_mem_iff hXY hedge, Color.adjXY.right_mem_iff hXY hedge⟩

/-- Vertices two steps apart in a chain lie on the same side. -/
theorem Color.adjXY.mem_of_two {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y) {i : ℕ}
    (hi : i + 2 < l.length) : (l[i] ∈ X ↔ l[i+2] ∈ X) ∧ (l[i] ∈ Y ↔ l[i+2] ∈ Y) := by
  have h1 := Color.adjXY.next_mem_iff h hXY (i := i) (by omega)
  have h2 := Color.adjXY.next_mem_iff h hXY (i := i + 1) (by omega)
  exact ⟨h1.1.trans h2.2, h1.2.trans h2.1⟩

/-- Vertices an even number of steps apart in a chain lie on the same side. -/
theorem Color.adjXY.mem_of_even_dist {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y) {i t : ℕ}
    (hi : i + 2 * t < l.length) :
    (l[i] ∈ X ↔ l[i + 2 * t] ∈ X) ∧ (l[i] ∈ Y ↔ l[i + 2 * t] ∈ Y) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hi' : i + 2 * t < l.length := by omega
    obtain ⟨hx, hy⟩ := ih hi'
    have h2 := Color.adjXY.mem_of_two h hXY (i := i + 2 * t) (by omega)
    show (l[i] ∈ X ↔ l[i + 2 * t + 2] ∈ X) ∧ (l[i] ∈ Y ↔ l[i + 2 * t + 2] ∈ Y)
    exact ⟨hx.trans h2.1, hy.trans h2.2⟩

/-- Two vertices of a chain at positions `i ≤ j` of the same parity lie on the
same side. -/
theorem Color.adjXY.same_side {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) (hpar : (j - i) % 2 = 0) :
    (l[i] ∈ X ↔ l[j] ∈ X) ∧ (l[i] ∈ Y ↔ l[j] ∈ Y) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, j = i + 2 * t := ⟨(j - i) / 2, by omega⟩
  subst ht
  have hlen : i + 2 * t < l.length := hj
  exact Color.adjXY.mem_of_even_dist h hXY hlen

/-- Two vertices of a chain at positions `i ≤ j` of opposite parity lie on
opposite sides. -/
theorem Color.adjXY.opp_side {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) (hpar : (j - i) % 2 = 1) :
    (l[i] ∈ X ↔ l[j] ∈ Y) ∧ (l[i] ∈ Y ↔ l[j] ∈ X) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, j = i + 2 * t + 1 := ⟨(j - i - 1) / 2, by omega⟩
  subst ht
  have h1 := Color.adjXY.mem_of_even_dist h hXY (i := i) (t := t) (by omega)
  have h2 := Color.adjXY.next_mem_iff h hXY (i := i + 2 * t) (by omega)
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem Color.adjXY.isChain_reverse {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) : l.reverse.IsChain (Color.adjXY G X Y c) := by
  rw [List.isChain_reverse]
  exact h.imp (fun _ _ ↦ Color.adjXY.symm)

/-- A *bipath* `(A, z, B)` is a list `A ++ z :: B` of distinct vertices such
that `A ++ [z]` is a red chain and `z :: B` is a blue chain.  `z` is the
*midpoint*.  (Gyárfás–Lehel's `S = (A₁,…,Aᵣ,X,B₁,…,Bₛ)`.) -/
def IsBipath (G : SimpleGraph V) (X Y : Finset V) (A : List V) (z : V) (B : List V) : Prop :=
  (A ++ [z]).IsChain (Color.adjXY G X Y .red) ∧
  (z :: B).IsChain (Color.adjXY G X Y .blue) ∧
  (A ++ z :: B).Nodup

/-- Number of vertices of the bipath. -/
def bipathLen (A : List V) (z : V) (B : List V) : ℕ := A.length + B.length + 1

/-- Existence of a bipath of maximum length. -/
theorem exists_max_bipath (G : SimpleGraph V) (X Y : Finset V) (v : V) :
    ∃ A z B, IsBipath G X Y A z B ∧
      ∀ A' z' B', IsBipath G X Y A' z' B' → bipathLen A' z' B' ≤ bipathLen A z B := by
  classical
  have : Nonempty V := ⟨v⟩
  have hPM := Nat.findGreatest_spec
    (P := fun m ↦ ∃ A z B, IsBipath G X Y A z B ∧ bipathLen A z B = m)
    (n := Fintype.card V) Fintype.card_pos
    (m := 1) ⟨[], v, [], ⟨List.isChain_singleton v, List.isChain_singleton v, by simp⟩,
              by simp [bipathLen]⟩
  obtain ⟨A, z, B, hb, hlen⟩ := hPM
  refine ⟨A, z, B, hb, fun A' z' B' hb' ↦ ?_⟩
  have hle : bipathLen A' z' B' ≤ Fintype.card V := by
    have hnd : (A' ++ z' :: B').Nodup := hb'.2.2
    have := hnd.length_le_card
    simp only [bipathLen, List.length_append, List.length_cons] at this ⊢
    omega
  have hle' : bipathLen A' z' B' ≤ Nat.findGreatest
      (fun m ↦ ∃ A z B, IsBipath G X Y A z B ∧ bipathLen A z B = m)
      (Fintype.card V) :=
    Nat.le_findGreatest hle ⟨A', z', B', hb', rfl⟩
  omega

end bip_ramsey_path

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
