import JSP415.GLIface
import JSP415.GLScratchA
import JSP415.GLScratchW
import JSP415.GLScratchLC
import JSP415.GLScratchLC2

/-!
# GLScratchInt2 — Gyárfás–Lehel Thm 3: internal claims D, E (hedge file)

Parallel implementation of the internal claims: claim D (skip-3 edges of the
`A ++ [z]` red cycle are red), claim E (the red branch is internally
red-complete), and the blue-side mirrors D′, E′.
-/

open Finset
open scoped List

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

/-! ### List segment helpers -/

/-- Half-open segment `l[i..j)`. -/
private abbrev seg {α : Type*} (l : List α) (i j : ℕ) : List α := (l.drop i).take (j - i)

private theorem seg_length {l : List V} (i j : ℕ) :
    (seg l i j).length = min j l.length - i := by
  simp only [seg, List.length_take, List.length_drop]
  omega

private theorem seg_eq_nil {l : List V} {i j : ℕ} (h : j ≤ i ∨ l.length ≤ i) :
    seg l i j = ([] : List V) := by
  have h0 : (seg l i j).length = 0 := by rw [seg_length]; omega
  exact List.length_eq_zero_iff.mp h0

private theorem seg_eq_take (l : List V) (j : ℕ) : seg l 0 j = l.take j := by
  simp [seg]

private theorem seg_eq_drop {l : List V} {i j : ℕ} (h : l.length ≤ j) :
    seg l i j = l.drop i := by
  simp only [seg]
  apply List.take_of_length_le
  simp only [List.length_drop]
  omega

private theorem seg_ne_nil {l : List V} {i j : ℕ} (hij : i < j)
    (hj : j ≤ l.length) : seg l i j ≠ ([] : List V) := by
  rw [List.ne_nil_iff_length_pos, seg_length]; omega

private theorem chain_seg {l : List V} {R : V → V → Prop} {i j : ℕ}
    (h : l.IsChain R) : (seg l i j).IsChain R :=
  (h.drop i).take _

private theorem chain_seg_rev {l : List V} {c : Color} {i j : ℕ}
    (h : l.IsChain (Color.adjXY G X Y c)) :
    (seg l i j).reverse.IsChain (Color.adjXY G X Y c) :=
  Color.adjXY.isChain_reverse (chain_seg h)

private theorem head?_seg {l : List V} {i j : ℕ} (hij : i < j) (hj : j ≤ l.length) :
    (seg l i j).head? = some l[i] := by
  have hilt : i < l.length := lt_of_lt_of_le hij hj
  simp only [seg, List.head?_take, List.head?_drop]
  rw [if_neg (by omega), List.getElem?_eq_getElem hilt]

private theorem getLast?_seg {l : List V} {i j : ℕ} (hij : i < j) (hj : j ≤ l.length) :
    (seg l i j).getLast? = some l[j - 1] := by
  have hj' : j - 1 < l.length := by omega
  simp only [seg, List.getLast?_take]
  rw [if_neg (by omega), List.getElem?_drop,
    show i + (j - i - 1) = j - 1 from by omega,
    List.getElem?_eq_getElem hj']
  rfl

private theorem head?_seg_rev {l : List V} {i j : ℕ} (hij : i < j) (hj : j ≤ l.length) :
    (seg l i j).reverse.head? = some l[j - 1] := by
  rw [List.head?_reverse, getLast?_seg hij hj]

private theorem getLast?_seg_rev {l : List V} {i j : ℕ} (hij : i < j) (hj : j ≤ l.length) :
    (seg l i j).reverse.getLast? = some l[i] := by
  rw [List.getLast?_reverse, head?_seg hij hj]

private theorem mem_seg {l : List V} {x : V} {i j : ℕ} :
    x ∈ seg l i j → ∃ k, i ≤ k ∧ k < j ∧ ∃ hk : k < l.length, l[k] = x := by
  simp only [seg, List.mem_take_iff_getElem, List.length_drop]
  rintro ⟨k, hk, he⟩
  have hk' : i + k < l.length := by omega
  refine ⟨i + k, by omega, by omega, hk', ?_⟩
  rw [List.getElem_drop] at he
  exact he

private theorem seg_cat {l : List V} {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    seg l i j ++ seg l j k = seg l i k := by
  simp only [seg]
  rw [show l.drop j = (l.drop i).drop (j - i) from by
        rw [List.drop_drop]; congr 1; omega]
  rw [← List.take_add]
  congr 1
  omega

private theorem seg_singleton {l : List V} {i : ℕ} (hi : i < l.length) :
    seg l i (i + 1) = [l[i]] := by
  simp only [seg]
  rw [show i + 1 - i = 1 from by omega, List.take_one]
  simp [List.getElem?_drop, List.getElem?_eq_getElem hi]

/-- Concatenate two chains with a junction edge. -/
private theorem chain_app {R : V → V → Prop} {l₁ l₂ : List V}
    (h1 : l₁.IsChain R) (h2 : l₂.IsChain R)
    (he : ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y) :
    (l₁ ++ l₂).IsChain R :=
  List.isChain_append.mpr ⟨h1, h2, he⟩

/-- Concatenate three chains (`++` is left-associative). -/
private theorem chain_app3 {R : V → V → Prop} {l₁ l₂ l₃ : List V}
    (h1 : l₁.IsChain R) (h2 : l₂.IsChain R) (h3 : l₃.IsChain R)
    (e12 : ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y)
    (e23 : ∀ x ∈ (l₁ ++ l₂).getLast?, ∀ y ∈ l₃.head?, R x y) :
    (l₁ ++ l₂ ++ l₃).IsChain R :=
  chain_app (chain_app h1 h2 e12) h3 e23

/-- Concatenate four chains. -/
private theorem chain_app4 {R : V → V → Prop} {l₁ l₂ l₃ l₄ : List V}
    (h1 : l₁.IsChain R) (h2 : l₂.IsChain R) (h3 : l₃.IsChain R)
    (h4 : l₄.IsChain R)
    (e12 : ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y)
    (e23 : ∀ x ∈ (l₁ ++ l₂).getLast?, ∀ y ∈ l₃.head?, R x y)
    (e34 : ∀ x ∈ (l₁ ++ l₂ ++ l₃).getLast?, ∀ y ∈ l₄.head?, R x y) :
    (l₁ ++ l₂ ++ l₃ ++ l₄).IsChain R :=
  chain_app (chain_app3 h1 h2 h3 e12 e23) h4 e34

/-- Concatenate five chains. -/
private theorem chain_app5 {R : V → V → Prop} {l₁ l₂ l₃ l₄ l₅ : List V}
    (h1 : l₁.IsChain R) (h2 : l₂.IsChain R) (h3 : l₃.IsChain R)
    (h4 : l₄.IsChain R) (h5 : l₅.IsChain R)
    (e12 : ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y)
    (e23 : ∀ x ∈ (l₁ ++ l₂).getLast?, ∀ y ∈ l₃.head?, R x y)
    (e34 : ∀ x ∈ (l₁ ++ l₂ ++ l₃).getLast?, ∀ y ∈ l₄.head?, R x y)
    (e45 : ∀ x ∈ (l₁ ++ l₂ ++ l₃ ++ l₄).getLast?, ∀ y ∈ l₅.head?, R x y) :
    (l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅).IsChain R :=
  chain_app (chain_app4 h1 h2 h3 h4 e12 e23 e34) h5 e45

/-- A cons chain with explicit head-edge. -/
private theorem chain_cons {R : V → V → Prop} {a : V} {l : List V}
    (h : ∀ y ∈ l.head?, R a y) (hl : l.IsChain R) :
    (a :: l).IsChain R :=
  List.isChain_cons.mpr ⟨h, hl⟩

/-- Solve a junction goal once endpoint values are known. -/
private theorem junc {R : V → V → Prop} {l₁ l₂ : List V} {v w : V}
    (hl : l₁.getLast? = some v) (hr : l₂.head? = some w) (e : R v w) :
    ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y := by
  intro x hx y hy
  rw [hl, Option.mem_some_iff] at hx
  rw [hr, Option.mem_some_iff] at hy
  subst hx hy
  exact e

/-- The `or`-form junction: `l₁.getLast?` may delegate when a right block is empty. -/
private theorem junc_or {R : V → V → Prop} {l₁ l₂ : List V} {v : V}
    (hl : l₁.getLast? = some v) (e : ∀ y ∈ l₂.head?, R v y) :
    ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y := by
  intro x hx y hy
  rw [hl, Option.mem_some_iff] at hx
  subst hx
  exact e y hy

/-! ### Edge constructors -/

private theorem redEdgeYX {a b : V} (ha : a ∈ Y) (hb : b ∈ X) (h : G.Adj a b) :
    Color.adjXY G X Y .red a b := ⟨Or.inr ⟨ha, hb⟩, h⟩

private theorem redEdgeXY {a b : V} (ha : a ∈ X) (hb : b ∈ Y) (h : G.Adj a b) :
    Color.adjXY G X Y .red a b := ⟨Or.inl ⟨ha, hb⟩, h⟩

private theorem blueEdgeYX {a b : V} (ha : a ∈ Y) (hb : b ∈ X) (h : ¬ G.Adj a b) :
    Color.adjXY G X Y .blue a b := ⟨Or.inr ⟨ha, hb⟩, h⟩

private theorem blueEdgeXY {a b : V} (ha : a ∈ X) (hb : b ∈ Y) (h : ¬ G.Adj a b) :
    Color.adjXY G X Y .blue a b := ⟨Or.inl ⟨ha, hb⟩, h⟩

/-! ### Case-3 setup facts -/

namespace Case3Data

variable (hXY : Disjoint X Y) (c3 : Case3Data G X Y)

private theorem redChain : (c3.A ++ [c3.z]).IsChain (Color.adjXY G X Y .red) :=
  c3.hb.1

private theorem blueChain : (c3.z :: c3.B).IsChain (Color.adjXY G X Y .blue) :=
  c3.hb.2.1

private theorem chainA : c3.A.IsChain (Color.adjXY G X Y .red) :=
  c3.hb.1.left_of_append

private theorem chainB : c3.B.IsChain (Color.adjXY G X Y .blue) :=
  c3.hb.2.1.tail

private theorem hnd : (c3.A ++ c3.z :: c3.B).Nodup := c3.hb.2.2

private theorem nodupA : c3.A.Nodup :=
  (List.nodup_append.mp (hnd c3)).1

private theorem nodupB : c3.B.Nodup :=
  (List.nodup_cons.mp (List.nodup_append.mp (hnd c3)).2.1).2

private theorem z_not_mem_B : c3.z ∉ c3.B :=
  (List.nodup_cons.mp (List.nodup_append.mp (hnd c3)).2.1).1

private theorem z_not_mem_A : c3.z ∉ c3.A :=
  (c3.hb.disjoint_pieces).1

private theorem a_not_mem_B_list : c3.A.Disjoint c3.B :=
  (c3.hb.disjoint_pieces).2.2

private theorem mem_S {x : V} :
    x ∈ c3.A ++ c3.z :: c3.B ↔ x ∈ c3.A ∨ x = c3.z ∨ x ∈ c3.B := by
  simp [List.mem_append, List.mem_cons, or_assoc]

private theorem lenAz : (c3.A ++ [c3.z]).length = c3.A.length + 1 := by simp

private theorem lenzB : (c3.z :: c3.B).length = c3.B.length + 1 := by simp

/-- Position parity determines the side: `A[i] ∈ Y ↔ i` even, `∈ X ↔ i` odd. -/
private theorem a_side (hXY : Disjoint X Y) (i : ℕ) (hi : i < c3.A.length) :
    (c3.A[i] ∈ Y ↔ i % 2 = 0) ∧ (c3.A[i] ∈ X ↔ i % 2 = 1) := by
  have hC : (c3.A ++ [c3.z]).IsChain (Color.adjXY G X Y .red) := c3.hb.1
  have h0 : (c3.A ++ [c3.z])[0]'(by rw [lenAz c3]; omega) ∈ Y := by
    rw [List.getElem_append_left (by omega : 0 < c3.A.length),
      ← List.head_eq_getElem_zero]
    exact c3.hhead
  have hmem : (c3.A ++ [c3.z])[i]'(by rw [lenAz c3]; omega) = c3.A[i] :=
    List.getElem_append_left hi
  have hcase : (i % 2 = 0 → c3.A[i] ∈ Y) ∧ (i % 2 = 1 → c3.A[i] ∈ X) := by
    constructor
    · intro hpar
      have hs := (Color.adjXY.same_side hC hXY (by rw [lenAz c3]; omega)
        (by rw [lenAz c3]; omega) (Nat.zero_le i) (by omega)).2
      rw [hmem] at hs
      exact hs.mp h0
    · intro hpar
      have hs := (Color.adjXY.opp_side hC hXY (by rw [lenAz c3]; omega)
        (by rw [lenAz c3]; omega) (Nat.zero_le i) (by omega)).2
      rw [hmem] at hs
      exact hs.mp h0
  constructor
  · constructor
    · intro hY
      rcases Nat.even_or_odd i with hpar | hpar
      · exact Nat.even_iff.mp hpar
      · exact absurd hY (Disjoint.notMem_left hXY (hcase.2 (Nat.odd_iff.mp hpar)))
    · exact fun hpar ↦ hcase.1 hpar
  · constructor
    · intro hX
      rcases Nat.even_or_odd i with hpar | hpar
      · exact absurd hX (Disjoint.notMem_right hXY (hcase.1 (Nat.even_iff.mp hpar)))
      · exact Nat.odd_iff.mp hpar
    · exact fun hpar ↦ hcase.2 hpar

/-- `B[i] ∈ Y ↔ i` even, `∈ X ↔ i` odd. -/
private theorem b_side (hXY : Disjoint X Y) (i : ℕ) (hi : i < c3.B.length) :
    (c3.B[i] ∈ Y ↔ i % 2 = 0) ∧ (c3.B[i] ∈ X ↔ i % 2 = 1) := by
  have hC : (c3.z :: c3.B).IsChain (Color.adjXY G X Y .blue) := c3.hb.2.1
  have h0 : (c3.z :: c3.B)[0]'(by rw [lenzB c3]; omega) ∈ X := by
    rw [List.getElem_cons_zero]
    exact c3.hz
  have hmem : (c3.z :: c3.B)[i + 1]'(by rw [lenzB c3]; omega) = c3.B[i] :=
    List.getElem_cons_succ _ _ _ _
  have hcase : (i % 2 = 0 → c3.B[i] ∈ Y) ∧ (i % 2 = 1 → c3.B[i] ∈ X) := by
    constructor
    · intro hpar
      have hs := (Color.adjXY.opp_side hC hXY (by rw [lenzB c3]; omega)
        (by rw [lenzB c3]; omega) (Nat.zero_le (i + 1)) (by omega)).1
      rw [hmem] at hs
      exact hs.mp h0
    · intro hpar
      have hs := (Color.adjXY.same_side hC hXY (by rw [lenzB c3]; omega)
        (by rw [lenzB c3]; omega) (Nat.zero_le (i + 1)) (by omega)).1
      rw [hmem] at hs
      exact hs.mp h0
  constructor
  · constructor
    · intro hY
      rcases Nat.even_or_odd i with hpar | hpar
      · exact Nat.even_iff.mp hpar
      · exact absurd hY (Disjoint.notMem_left hXY (hcase.2 (Nat.odd_iff.mp hpar)))
    · exact fun hpar ↦ hcase.1 hpar
  · constructor
    · intro hX
      rcases Nat.even_or_odd i with hpar | hpar
      · exact absurd hX (Disjoint.notMem_right hXY (hcase.1 (Nat.even_iff.mp hpar)))
      · exact Nat.odd_iff.mp hpar
    · exact fun hpar ↦ hcase.2 hpar

/-- The last red edge `aᵣ–z`. -/
private theorem edgeLastA : Color.adjXY G X Y .red (c3.A.getLast c3.hA) c3.z := by
  have h := (List.isChain_append.mp (redChain c3)).2.2
  have h1 : c3.A.getLast c3.hA ∈ c3.A.getLast? := by
    rw [List.getLast?_eq_getLast c3.hA]
    exact Option.mem_some_self _
  have h2 : c3.z ∈ [c3.z].head? := by simp
  exact h _ h1 _ h2

/-- The last red edge, in `getElem` form. -/
private theorem edgeLastAi : Color.adjXY G X Y .red
    (c3.A[c3.A.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil c3.hA) Nat.one_pos))
    c3.z := by
  rw [← List.getLast_eq_getElem]
  exact edgeLastA c3

/-- The first blue edge `z–b₁`. -/
private theorem edgeFirstB : Color.adjXY G X Y .blue c3.z (c3.B.head c3.hB) := by
  have h := (List.isChain_cons.mp (blueChain c3)).1
  have hmem : c3.B.head c3.hB ∈ c3.B.head? := by
    rw [List.head?_eq_some_head c3.hB]
    exact Option.mem_some_self _
  exact h _ hmem

/-- The first blue edge, in `getElem` form. -/
private theorem edgeFirstBi : Color.adjXY G X Y .blue c3.z
    (c3.B[0]'(List.length_pos_of_ne_nil c3.hB)) := by
  rw [← List.head_eq_getElem_zero]
  exact edgeFirstB c3

/-- Claim A (i): `z–A[0]` is red. -/
private theorem za1red (hXY : Disjoint X Y) :
    Color.adjXY G X Y .red c3.z (c3.A.head c3.hA) := by
  have hA1 := (claimA_of_case3 hXY c3).1
  exact Color.adjXY.symm hA1

/-- Claim A (i), in `getElem` form. -/
private theorem za1redi (hXY : Disjoint X Y) :
    Color.adjXY G X Y .red c3.z (c3.A[0]'(List.length_pos_of_ne_nil c3.hA)) := by
  rw [← List.head_eq_getElem_zero]
  exact za1red c3 hXY

/-- Claim A (ii): `z–B[s-1]` is blue. -/
private theorem zbsBlue (hXY : Disjoint X Y) :
    Color.adjXY G X Y .blue c3.z (c3.B.getLast c3.hB) :=
  (claimA_of_case3 hXY c3).2

/-- Claim A (ii), in `getElem` form. -/
private theorem zbsBluei (hXY : Disjoint X Y) :
    Color.adjXY G X Y .blue c3.z
      (c3.B[c3.B.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil c3.hB) Nat.one_pos)) := by
  rw [← List.getLast_eq_getElem]
  exact zbsBlue c3 hXY

/-- `r` is odd: `A[r-1]` (adjacent to `z ∈ X` via red) lies in `Y`. -/
private theorem r_odd (hXY : Disjoint X Y) : c3.A.length % 2 = 1 := by
  have hr : 0 < c3.A.length := List.length_pos_of_ne_nil c3.hA
  have hac : acrossXY X Y (c3.A[c3.A.length - 1]'(Nat.sub_lt hr Nat.one_pos)) c3.z :=
    (edgeLastAi c3).1
  rcases hac with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h2 (Disjoint.notMem_left hXY c3.hz)
  · have := (c3.a_side hXY (c3.A.length - 1) (Nat.sub_lt hr Nat.one_pos)).1.mp h1
    omega

/-- `s` is odd: `B[s-1] ∈ Y` by `hlast`. -/
private theorem s_odd (hXY : Disjoint X Y) : c3.B.length % 2 = 1 := by
  have hs : c3.B.length - 1 < c3.B.length :=
    Nat.sub_lt (List.length_pos_of_ne_nil c3.hB) Nat.one_pos
  have hl : c3.B[c3.B.length - 1] ∈ Y := by
    rw [← List.getLast_eq_getElem]
    exact c3.hlast
  have := (c3.b_side hXY (c3.B.length - 1) hs).1.mp hl
  omega

/-- Consecutive red edge inside `A`. -/
private theorem edgeA (i : ℕ) (hi : i + 1 < c3.A.length) :
    Color.adjXY G X Y .red c3.A[i] c3.A[i + 1] :=
  List.isChain_iff_getElem.mp (chainA c3) i hi

/-- Consecutive blue edge inside `B`. -/
private theorem edgeB (i : ℕ) (hi : i + 1 < c3.B.length) :
    Color.adjXY G X Y .blue c3.B[i] c3.B[i + 1] :=
  List.isChain_iff_getElem.mp (chainB c3) i hi

/-! ### Membership in the finsets -/

private theorem mem_S1U (hXY : Disjoint X Y) {u : V} :
    u ∈ c3.S1U ↔ u ∈ c3.A ∧ u ∈ Y := by
  simp only [Case3Data.S1U, Finset.mem_filter, List.mem_toFinset, Case3Data.S1,
    List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨h, hY⟩
    rcases h with h | h
    · exact ⟨h, hY⟩
    · subst h
      exact absurd hY (Disjoint.notMem_left hXY c3.hz)
  · rintro ⟨h, hY⟩
    exact ⟨Or.inl h, hY⟩

private theorem mem_S2U (hXY : Disjoint X Y) {u : V} :
    u ∈ c3.S2U ↔ u ∈ c3.B ∧ u ∈ Y := by
  simp only [Case3Data.S2U, Finset.mem_filter, List.mem_toFinset, Case3Data.S2,
    List.mem_cons]
  constructor
  · rintro ⟨h, hY⟩
    rcases h with h | h
    · subst h
      exact absurd hY (Disjoint.notMem_left hXY c3.hz)
    · exact ⟨h, hY⟩
  · rintro ⟨h, hY⟩
    exact ⟨Or.inr h, hY⟩

private theorem mem_SL {l : V} :
    l ∈ c3.SL ↔ (l ∈ c3.A ∨ l = c3.z ∨ l ∈ c3.B) ∧ l ∈ X := by
  simp only [Case3Data.SL, Finset.mem_filter, List.mem_toFinset, Case3Data.S,
    List.mem_append, List.mem_cons]

private theorem mem_L2 {w : V} : w ∈ c3.L2 ↔ w ∈ X ∧ w ∉ c3.A ++ c3.z :: c3.B := by
  simp only [Case3Data.L2, Finset.mem_sdiff, List.mem_toFinset]

/-- `A[i]` for even `i` lies in `S1U`. -/
private theorem a_mem_S1U (hXY : Disjoint X Y) {i : ℕ} (hi : i < c3.A.length)
    (hpar : i % 2 = 0) : c3.A[i] ∈ c3.S1U :=
  (mem_S1U c3 hXY).mpr ⟨List.getElem_mem hi, (c3.a_side hXY i hi).1.mpr hpar⟩

/-- `B[i]` for even `i` lies in `S2U`. -/
private theorem b_mem_S2U (hXY : Disjoint X Y) {i : ℕ} (hi : i < c3.B.length)
    (hpar : i % 2 = 0) : c3.B[i] ∈ c3.S2U :=
  (mem_S2U c3 hXY).mpr ⟨List.getElem_mem hi, (c3.b_side hXY i hi).1.mpr hpar⟩

/-- `A[i]` for odd `i` lies in `SL`. -/
private theorem a_mem_SL (hXY : Disjoint X Y) {i : ℕ} (hi : i < c3.A.length)
    (hpar : i % 2 = 1) : c3.A[i] ∈ c3.SL :=
  (mem_SL c3).mpr ⟨Or.inl (List.getElem_mem hi), (c3.a_side hXY i hi).2.mpr hpar⟩

/-- `B[i]` for odd `i` lies in `SL`. -/
private theorem b_mem_SL (hXY : Disjoint X Y) {i : ℕ} (hi : i < c3.B.length)
    (hpar : i % 2 = 1) : c3.B[i] ∈ c3.SL :=
  (mem_SL c3).mpr ⟨Or.inr (Or.inr (List.getElem_mem hi)),
    (c3.b_side hXY i hi).2.mpr hpar⟩

private theorem z_mem_SL : c3.z ∈ c3.SL :=
  (mem_SL c3).mpr ⟨Or.inr (Or.inl rfl), c3.hz⟩

/-- Elements of `A` are distinct. -/
private theorem a_inj {i j : ℕ} (hi : i < c3.A.length) (hj : j < c3.A.length)
    (h : c3.A[i] = c3.A[j]) : i = j :=
  (nodupA c3).getElem_inj.mp h

/-- Elements of `B` are distinct. -/
private theorem b_inj {i j : ℕ} (hi : i < c3.B.length) (hj : j < c3.B.length)
    (h : c3.B[i] = c3.B[j]) : i = j :=
  (nodupB c3).getElem_inj.mp h

/-- Elements of `A` are not in `B` and differ from `z`. -/
private theorem a_not_mem_B {i : ℕ} (hi : i < c3.A.length) : c3.A[i] ∉ c3.B := by
  intro hmem
  have hd := (List.nodup_append.mp (hnd c3)).2.2
  exact hd _ (List.getElem_mem hi) _ (List.mem_cons_of_mem _ hmem) rfl

private theorem a_ne_z {i : ℕ} (hi : i < c3.A.length) : c3.A[i] ≠ c3.z := by
  intro e
  have hd := (List.nodup_append.mp (hnd c3)).2.2
  exact hd _ (List.getElem_mem hi) _ List.mem_cons_self e

private theorem a_ne_b {i j : ℕ} (hi : i < c3.A.length) (hj : j < c3.B.length) :
    c3.A[i] ≠ c3.B[j] := by
  intro e
  have hd := (List.nodup_append.mp (hnd c3)).2.2
  exact hd _ (List.getElem_mem hi) _ (List.mem_cons_of_mem _ (List.getElem_mem hj)) e

private theorem b_ne_z {i : ℕ} (hi : i < c3.B.length) : c3.B[i] ≠ c3.z := by
  intro e
  exact (z_not_mem_B c3) (e ▸ List.getElem_mem hi)

private theorem b_not_mem_A {i : ℕ} (hi : i < c3.B.length) : c3.B[i] ∉ c3.A := by
  intro hmem
  have hd := (List.nodup_append.mp (hnd c3)).2.2
  exact hd _ hmem _ (List.mem_cons_of_mem _ (List.getElem_mem hi)) rfl

private theorem ux_not_mem : c3.ux ∉ c3.A ++ c3.z :: c3.B := c3.hux.2

private theorem ux_X : c3.ux ∈ X := c3.hux.1

/-- `A` decomposed as `seg 0 m` + 1 element + `seg (m+1) r`. -/
private theorem A_split1' {m : ℕ} (hmr : m < c3.A.length) :
    c3.A = seg c3.A 0 m ++ [c3.A[m]] ++ seg c3.A (m + 1) c3.A.length := by
  rw [seg_eq_take, seg_eq_drop (Nat.le_refl _)]
  calc c3.A = c3.A.take m ++ c3.A.drop m := (List.take_append_drop _ _).symm
    _ = c3.A.take m ++ (c3.A[m] :: c3.A.drop (m + 1)) := by
        rw [List.drop_eq_getElem_cons hmr]
    _ = c3.A.take m ++ [c3.A[m]] ++ c3.A.drop (m + 1) := by
        rw [List.append_assoc, List.cons_append, List.nil_append]

/-- `B` decomposed as `seg 0 n` + 1 element + `seg (n+1) s`. -/
private theorem B_split1' {n : ℕ} (hnr : n < c3.B.length) :
    c3.B = seg c3.B 0 n ++ [c3.B[n]] ++ seg c3.B (n + 1) c3.B.length := by
  rw [seg_eq_take, seg_eq_drop (Nat.le_refl _)]
  calc c3.B = c3.B.take n ++ c3.B.drop n := (List.take_append_drop _ _).symm
    _ = c3.B.take n ++ (c3.B[n] :: c3.B.drop (n + 1)) := by
        rw [List.drop_eq_getElem_cons hnr]
    _ = c3.B.take n ++ [c3.B[n]] ++ c3.B.drop (n + 1) := by
        rw [List.append_assoc, List.cons_append, List.nil_append]

/-! ### Nodup normal forms -/

/-- `take p ++ drop q` of `A` is nodup when `p ≤ q`. -/
private theorem nodupA_td {p q : ℕ} (hpq : p ≤ q) :
    (c3.A.take p ++ c3.A.drop q).Nodup := by
  rw [List.nodup_append]
  refine ⟨(List.take_sublist _ _).nodup (nodupA c3),
    (List.drop_sublist _ _).nodup (nodupA c3), ?_⟩
  intro x hx y hy hxy
  obtain ⟨i, hi, hie⟩ := List.mem_take_iff_getElem.mp hx
  obtain ⟨j, hj, hje⟩ := List.mem_drop_iff_getElem.mp hy
  have hi' : i < c3.A.length := by omega
  have hj' : q + j < c3.A.length := by omega
  have : i = q + j := c3.a_inj hi' hj' (hie.trans (hxy.trans hje.symm))
  omega

/-- `take p ++ drop q` of `B` is nodup when `p ≤ q`. -/
private theorem nodupB_td {p q : ℕ} (hpq : p ≤ q) :
    (c3.B.take p ++ c3.B.drop q).Nodup := by
  rw [List.nodup_append]
  refine ⟨(List.take_sublist _ _).nodup (nodupB c3),
    (List.drop_sublist _ _).nodup (nodupB c3), ?_⟩
  intro x hx y hy hxy
  obtain ⟨i, hi, hie⟩ := List.mem_take_iff_getElem.mp hx
  obtain ⟨j, hj, hje⟩ := List.mem_drop_iff_getElem.mp hy
  have hi' : i < c3.B.length := by omega
  have hj' : q + j < c3.B.length := by omega
  have : i = q + j := c3.b_inj hi' hj' (hie.trans (hxy.trans hje.symm))
  omega

/-- A `take p ++ drop q` element of `A` lies in `A` (so misses `z`, `B`,
leftovers). -/
private theorem mem_td_of_A {x : V} {p q : ℕ}
    (h : x ∈ c3.A.take p ++ c3.A.drop q) : x ∈ c3.A := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_of_mem_take h
  · exact List.mem_of_mem_drop h

private theorem mem_td_of_B {x : V} {p q : ℕ}
    (h : x ∈ c3.B.take p ++ c3.B.drop q) : x ∈ c3.B := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_of_mem_take h
  · exact List.mem_of_mem_drop h

/-- The standard normal form `extras ++ (A.take p ++ A.drop q ++ z :: B)`
is nodup when the extras are distinct leftovers. -/
private theorem nodup_NF_A (p q : ℕ) (hpq : p ≤ q) :
    (c3.A.take p ++ c3.A.drop q ++ c3.z :: c3.B).Nodup := by
  have hzB : (c3.z :: c3.B).Nodup :=
    (List.nodup_append.mp (hnd c3)).2.1
  rw [List.nodup_append]
  refine ⟨nodupA_td c3 hpq, hzB, ?_⟩
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_td_of_A c3 hx)
  rcases List.mem_cons.mp hy with hyz | hyB
  · exact c3.a_ne_z hi (hxy.trans hyz)
  · exact c3.a_not_mem_B hi (hxy ▸ hyB)

/-- Blue-first normal form: `B.take p ++ B.drop q ++ z :: A` is nodup. -/
private theorem nodup_NF_B (p q : ℕ) (hpq : p ≤ q) :
    (c3.B.take p ++ c3.B.drop q ++ c3.z :: c3.A).Nodup := by
  have hzA : (c3.z :: c3.A).Nodup := by
    refine List.nodup_cons.mpr ⟨z_not_mem_A c3, nodupA c3⟩
  rw [List.nodup_append]
  refine ⟨nodupB_td c3 hpq, hzA, ?_⟩
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_td_of_B c3 hx)
  rcases List.mem_cons.mp hy with hyz | hyA
  · exact c3.b_ne_z hi (hxy.trans hyz)
  · exact c3.b_not_mem_A hi (hxy ▸ hyA)

/-- A vertex of `A.take p ++ A.drop q` lies in `S`. -/
private theorem mem_S_of_td_A {x : V} {p q : ℕ}
    (h : x ∈ c3.A.take p ++ c3.A.drop q ++ c3.z :: c3.B) :
    x ∈ c3.A ++ c3.z :: c3.B := by
  rw [mem_S c3]
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (mem_td_of_A c3 h)
  · rcases List.mem_cons.mp h with e | hB
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr hB)

private theorem mem_S_of_td_B {x : V} {p q : ℕ}
    (h : x ∈ c3.B.take p ++ c3.B.drop q ++ c3.z :: c3.A) :
    x ∈ c3.A ++ c3.z :: c3.B := by
  rw [mem_S c3]
  rcases List.mem_append.mp h with h | h
  · exact Or.inr (Or.inr (mem_td_of_B c3 h))
  · rcases List.mem_cons.mp h with e | hA
    · exact Or.inr (Or.inl e)
    · exact Or.inl hA

/-! ### Permutation gadgets -/

/-- Rotation vertex-list identity without a leading vertex. -/
private theorem rot_vertex_eq' {z : V} {P Q R : List V} (hQ : Q ≠ []) :
    (P.reverse ++ z :: Q.tail.reverse) ++ Q.head hQ :: R
      = P.reverse ++ z :: (Q.reverse ++ R) := by
  have h := rot_vertex_eq (w := z) (z := z) (P := P) (Q := Q) (R := R) hQ
  -- (z :: P.rev ++ z :: Q.tail.rev) ++ Q.head :: R = z :: P.rev ++ z :: (Q.rev ++ R)
  -- not directly applicable; do it by hand
  rw [show (P.reverse ++ z :: Q.tail.reverse) ++ Q.head hQ :: R
        = P.reverse ++ z :: (Q.tail.reverse ++ (Q.head hQ :: R)) from by
        simp only [List.append_assoc, List.cons_append]]
  rw [tail_rev_cons_head_app hQ]

/-- Rotation vertex-list permutation without a leading vertex:
`(P.reverse ++ z :: Q.tail.reverse) ++ Q.head :: R ~ (P ++ Q) ++ z :: R`. -/
private theorem perm_rot' {z : V} {P Q R : List V} (hQ : Q ≠ []) :
    List.Perm ((P.reverse ++ z :: Q.tail.reverse) ++ Q.head hQ :: R)
      ((P ++ Q) ++ z :: R) := by
  rw [rot_vertex_eq' hQ]
  calc P.reverse ++ z :: (Q.reverse ++ R)
      ~ z :: (P.reverse ++ (Q.reverse ++ R)) := List.perm_middle
    _ ~ z :: (P ++ (Q ++ R)) := by
        apply List.Perm.cons
        exact ((List.reverse_perm _).append_right _).trans
          (((List.reverse_perm _).append_right _).append_left _)
    _ ~ z :: ((P ++ Q) ++ R) :=
        List.Perm.of_eq (congrArg (z :: ·) (List.append_assoc P Q R).symm)
    _ ~ (P ++ Q) ++ z :: R := List.perm_middle.symm

/-- `l ++ [a]` rotated to `a :: l`. -/
private theorem perm_snoc {a : V} {l : List V} : (l ++ [a]).Perm (a :: l) := by
  have h := List.perm_append_comm (l₁ := l) (l₂ := [a])
  exact h

/-- `a :: l` rotated to `l ++ [a]`. -/
private theorem perm_cons_end {a : V} {l : List V} : (a :: l).Perm (l ++ [a]) := by
  have h := List.perm_append_comm (l₁ := [a]) (l₂ := l)
  exact h

/-- Move the head element three positions right. -/
private theorem perm_rot3 {a b c d : V} {l : List V} :
    (a :: b :: c :: d :: l).Perm (b :: c :: d :: a :: l) := by
  calc a :: b :: c :: d :: l ~ b :: a :: c :: d :: l := List.Perm.swap _ _ _
    _ ~ b :: c :: a :: d :: l := (List.Perm.swap _ _ _).cons _
    _ ~ b :: c :: d :: a :: l := ((List.Perm.swap _ _ _).cons _).cons _

/-- Move the head element two positions right. -/
private theorem perm_rot2 {a b c : V} {l : List V} :
    (a :: b :: c :: l).Perm (b :: c :: a :: l) := by
  calc a :: b :: c :: l ~ b :: a :: c :: l := List.Perm.swap _ _ _
    _ ~ b :: c :: a :: l := (List.Perm.swap _ _ _).cons _

/-- `z :: (B ++ T) ~ T ++ z :: B` — move a singleton across two blocks. -/
private theorem perm_z_to_mid {z : V} {B_ T : List V} :
    (z :: (B_ ++ T)).Perm (T ++ z :: B_) := by
  calc z :: (B_ ++ T) ~ (B_ ++ T) ++ [z] := perm_cons_end
    _ ~ (T ++ B_) ++ [z] := (List.perm_append_comm).append_right _
    _ ~ T ++ (B_ ++ [z]) := List.Perm.of_eq (List.append_assoc _ _ _)
    _ ~ T ++ (z :: B_) := (List.perm_append_comm).append_left _

/-- `take (i+1) ++ drop (i+1)` expansions. -/
private theorem take_succ_eq {l : List V} {i : ℕ} (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]] := by
  rw [List.take_add, List.take_one, List.head?_drop,
    List.getElem?_eq_getElem hi]
  rfl

private theorem drop_cons_eq {l : List V} {i : ℕ} (hi : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) :=
  List.drop_eq_getElem_cons hi

private theorem take_drop_eq {l : List V} {i : ℕ} (hi : i + 1 < l.length) :
    l.take i ++ l[i] :: l.drop (i + 1) = l.take (i + 1) ++ l.drop (i + 1) := by
  rw [take_succ_eq (Nat.lt_of_succ_lt hi), List.append_assoc,
    List.cons_append, List.nil_append]

/-- Single head-edge in `∀ y ∈ head?` form. -/
private theorem head_edge {R : V → V → Prop} {a b : V} {l : List V}
    (h : R a b) : ∀ y ∈ (b :: l).head?, R a y := by
  intro y hy
  rw [List.head?_cons, Option.mem_some_iff] at hy
  subst hy
  exact h

/-- Claim D, even first index.  If `a_t–a_{t+3}` were blue, the bipath
`(a_{t-1},…,a_0, z, a_{r-1},…,a_{t+5} ; a_{t+4} ; u₂, a_{t+2}, ux, a_t,
a_{t+3}, b_0,…)` would be a strictly longer bipath. -/
private theorem claimD_even (hXY : Disjoint X Y) (hB' : c3.ClaimB')
    (hC : ∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u)
    (hux2 : c3.HasUx2) {t : ℕ} (ht : t + 3 < c3.A.length) (hpar : t % 2 = 0) :
    G.Adj c3.A[t] c3.A[t + 3] := by
  obtain ⟨u₂, hu₂X, hu₂S, hu₂ne⟩ := hux2
  have hro : c3.A.length % 2 = 1 := c3.r_odd hXY
  by_contra hbad
  have ht4 : t + 4 < c3.A.length := by omega
  have huL : c3.ux ∈ c3.L2 := (mem_L2 c3).mpr ⟨c3.ux_X, c3.ux_not_mem⟩
  have hu₂L : u₂ ∈ c3.L2 := (mem_L2 c3).mpr ⟨hu₂X, hu₂S⟩
  -- abbreviations for the non-list vertices
  set m := c3.A[t + 4]'ht4 with hm_def
  set x2 := c3.A[t + 2]'(by omega) with hx2_def
  set x0 := c3.A[t]'(by omega) with hx0_def
  set x3 := c3.A[t + 3]'ht with hx3_def
  have hmY : m ∈ Y := (c3.a_side hXY _ ht4).1.mpr (by omega)
  have hx2Y : x2 ∈ Y := (c3.a_side hXY _ (by omega)).1.mpr (by omega)
  have hx0Y : x0 ∈ Y := (c3.a_side hXY _ (by omega)).1.mpr (by omega)
  have hx3X : x3 ∈ X := (c3.a_side hXY _ ht).2.mpr (by omega)
  have hmU : m ∈ c3.S1U := c3.a_mem_S1U hXY ht4 (by omega)
  have hx2U : x2 ∈ c3.S1U := c3.a_mem_S1U hXY (by omega) (by omega)
  have hx0U : x0 ∈ c3.S1U := c3.a_mem_S1U hXY (by omega) (by omega)
  have hx3L : x3 ∈ c3.SL := c3.a_mem_SL hXY ht (by omega)
  -- the blue chain edges
  have emu : Color.adjXY G X Y .blue m u₂ :=
    ⟨Or.inr ⟨hmY, hu₂X⟩, fun h ↦ hC u₂ hu₂L m hmU h.symm⟩
  have eu2 : Color.adjXY G X Y .blue u₂ x2 :=
    ⟨Or.inl ⟨hu₂X, hx2Y⟩, hC u₂ hu₂L x2 hx2U⟩
  have e2u : Color.adjXY G X Y .blue x2 c3.ux :=
    ⟨Or.inr ⟨hx2Y, c3.ux_X⟩, fun h ↦ hC c3.ux huL x2 hx2U h.symm⟩
  have eux : Color.adjXY G X Y .blue c3.ux x0 :=
    ⟨Or.inl ⟨c3.ux_X, hx0Y⟩, hC c3.ux huL x0 hx0U⟩
  have e03 : Color.adjXY G X Y .blue x0 x3 := ⟨Or.inr ⟨hx0Y, hx3X⟩, hbad⟩
  have e3b : ∀ y ∈ c3.B.head?, Color.adjXY G X Y .blue x3 y := by
    intro y hy
    rw [List.head?_eq_some_head c3.hB, Option.mem_some_iff] at hy
    subst hy
    exact ⟨Or.inl ⟨hx3X, B_head_mem_Y hXY c3⟩,
      hB' x3 hx3L (List.getElem_mem _)⟩
  -- red chain: `(take t).reverse ++ z :: (drop (t+4)).reverse`
  have hT1 : (c3.A.take t).reverse.IsChain (Color.adjXY G X Y .red) :=
    Color.adjXY.isChain_reverse (isChain_take_of _ (chainA c3))
  have hT2 : (c3.A.drop (t + 4)).reverse.IsChain (Color.adjXY G X Y .red) :=
    Color.adjXY.isChain_reverse (isChain_drop_of _ (chainA c3))
  have hQne : c3.A.drop (t + 4) ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_drop]; omega
  have hR : ((c3.A.take t).reverse ++ c3.z ::
      (c3.A.drop (t + 4)).reverse).IsChain (Color.adjXY G X Y .red) := by
    refine chain_app hT1 (chain_cons ?_ hT2) ?_
    · intro y hy
      rw [List.head?_reverse, getLast?_drop ht4, Option.mem_some_iff] at hy
      subst hy
      exact Color.adjXY.symm (edgeLastAi c3)
    · intro x hx y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy; subst hy
      rw [List.getLast?_reverse] at hx
      rcases Nat.eq_zero_or_pos t with ht0 | ht0
      · subst ht0; simp at hx
      · rw [head?_take ht0 (by omega), List.head?_eq_some_head c3.hA,
          Option.mem_some_iff] at hx
        subst hx
        exact (claimA_of_case3 hXY c3).1
  -- the red part in bipath form `A' ++ [z']`
  have hR' : (((c3.A.take t).reverse ++ c3.z ::
        (c3.A.drop (t + 4)).tail.reverse) ++
      [(c3.A.drop (t + 4)).head hQne]).IsChain (Color.adjXY G X Y .red) := by
    have e : (c3.A.drop (t + 4)).tail.reverse ++ [(c3.A.drop (t + 4)).head hQne]
        = (c3.A.drop (t + 4)).reverse := tail_reverse_cons_head hQne
    have e' : ((c3.A.take t).reverse ++ c3.z ::
          (c3.A.drop (t + 4)).tail.reverse) ++ [(c3.A.drop (t + 4)).head hQne]
        = (c3.A.take t).reverse ++ c3.z :: (c3.A.drop (t + 4)).reverse := by
      rw [show ((c3.A.take t).reverse ++ c3.z ::
              (c3.A.drop (t + 4)).tail.reverse) ++ [(c3.A.drop (t + 4)).head hQne]
            = (c3.A.take t).reverse ++ c3.z ::
              ((c3.A.drop (t + 4)).tail.reverse ++ [(c3.A.drop (t + 4)).head hQne])
          from by simp only [List.append_assoc, List.cons_append]]
      rw [e]
    rw [e']; exact hR
  -- blue chain: `m :: u₂ :: x2 :: ux :: x0 :: x3 :: B`
  have hBl : (m :: u₂ :: x2 :: c3.ux :: x0 :: x3 :: c3.B).IsChain
      (Color.adjXY G X Y .blue) :=
    chain_cons (head_edge emu) (chain_cons (head_edge eu2)
      (chain_cons (head_edge e2u) (chain_cons (head_edge eux)
        (chain_cons (head_edge e03) (chain_cons e3b (chainB c3))))))
  have hBl' : ((c3.A.drop (t + 4)).head hQne ::
      ([u₂, c3.A[t + 2], c3.ux, c3.A[t], c3.A[t + 3]] ++ c3.B)).IsChain
      (Color.adjXY G X Y .blue) := by
    have e : (c3.A.drop (t + 4)).head hQne = m := by
      rw [hm_def, List.head_drop hQne]
    rw [e]
    exact hBl
  -- nodup via permutation to normal form
  have hperm : List.Perm
      (((c3.A.take t).reverse ++ c3.z :: (c3.A.drop (t + 4)).tail.reverse) ++
        (c3.A.drop (t + 4)).head hQne ::
          ([u₂, c3.A[t + 2], c3.ux, c3.A[t], c3.A[t + 3]] ++ c3.B))
      (u₂ :: c3.ux :: (c3.A.take (t + 1) ++ c3.A.drop (t + 2) ++ c3.z :: c3.B)) := by
    have h1 := perm_rot' (z := c3.z) (P := c3.A.take t)
      (Q := c3.A.drop (t + 4)) (R := u₂ :: x2 :: c3.ux :: x0 :: x3 :: c3.B) hQne
    -- h1 : L' ~ (take t ++ drop (t+4)) ++ z :: (u₂::x2::ux::x0::x3::B)
    refine h1.trans ?_
    calc (c3.A.take t ++ c3.A.drop (t + 4)) ++
            c3.z :: (u₂ :: x2 :: c3.ux :: x0 :: x3 :: c3.B)
        ~ c3.z :: ((c3.A.take t ++ c3.A.drop (t + 4)) ++
            (u₂ :: x2 :: c3.ux :: x0 :: x3 :: c3.B)) := List.perm_middle
      _ ~ c3.z :: ((u₂ :: x2 :: c3.ux :: x0 :: x3 :: c3.B) ++
            (c3.A.take t ++ c3.A.drop (t + 4))) :=
          (List.perm_append_comm).cons _
      _ ~ c3.z :: (u₂ :: x2 :: c3.ux :: x0 :: x3 ::
            (c3.A.take t ++ c3.A.drop (t + 4) ++ c3.B)) := by
          apply List.Perm.cons
          apply List.Perm.cons; apply List.Perm.cons; apply List.Perm.cons
          apply List.Perm.cons; apply List.Perm.cons
          exact List.perm_append_comm
      _ ~ (u₂ :: x2 :: c3.ux :: x0 :: x3 ::
            (c3.A.take t ++ c3.A.drop (t + 4) ++ c3.B)) ++ [c3.z] :=
          perm_cons_end
      _ ~ u₂ :: x2 :: c3.ux :: x0 :: x3 ::
            (c3.A.take t ++ c3.A.drop (t + 4) ++ c3.z :: c3.B) := by
          apply List.Perm.cons; apply List.Perm.cons; apply List.Perm.cons
          apply List.Perm.cons; apply List.Perm.cons
          calc (c3.A.take t ++ c3.A.drop (t + 4) ++ c3.B) ++ [c3.z]
              ~ c3.A.take t ++ c3.A.drop (t + 4) ++ (c3.B ++ [c3.z]) :=
                List.Perm.of_eq (List.append_assoc _ _ _)
            _ ~ c3.A.take t ++ c3.A.drop (t + 4) ++ (c3.z :: c3.B) :=
                (List.perm_append_comm).append_left _
      _ ~ u₂ :: c3.ux :: x0 :: x2 :: x3 ::
            (c3.A.take t ++ c3.A.drop (t + 4) ++ c3.z :: c3.B) := by
          calc u₂ :: x2 :: c3.ux :: x0 :: x3 ::
                (c3.A.take t ++ c3.A.drop (t + 4) ++ c3.z :: c3.B)
              ~ u₂ :: c3.ux :: x2 :: x0 :: x3 ::
                (c3.A.take t ++ c3.A.drop (t + 4) ++ c3.z :: c3.B) :=
                (List.Perm.swap _ _ _).cons _
            _ ~ u₂ :: c3.ux :: x0 :: x2 :: x3 ::
                (c3.A.take t ++ c3.A.drop (t + 4) ++ c3.z :: c3.B) :=
                ((List.Perm.swap _ _ _).cons _).cons _
      _ ~ u₂ :: c3.ux ::
            (c3.A.take t ++ [x0, x2, x3] ++ c3.A.drop (t + 4) ++
              c3.z :: c3.B) := by
          apply List.Perm.cons; apply List.Perm.cons
          calc x0 :: x2 :: x3 ::
                (c3.A.take t ++ c3.A.drop (t + 4) ++ c3.z :: c3.B)
              ~ (c3.A.take t ++ [x0, x2, x3]) ++
                (c3.A.drop (t + 4) ++ c3.z :: c3.B) := by
                have : ([x0, x2, x3] ++ c3.A.take t).Perm
                    (c3.A.take t ++ [x0, x2, x3]) := List.perm_append_comm
                exact List.Perm.of_eq (by
                  simp only [List.append_assoc, List.cons_append,
                    List.nil_append]) |>.trans (this.append_right _)
            _ ~ c3.A.take t ++ [x0, x2, x3] ++ c3.A.drop (t + 4) ++
                c3.z :: c3.B := List.Perm.of_eq (by
                  simp only [List.append_assoc])
      _ ~ u₂ :: c3.ux ::
            (c3.A.take (t + 1) ++ c3.A.drop (t + 2) ++ c3.z :: c3.B) := by
          apply List.Perm.cons; apply List.Perm.cons
          apply List.Perm.append_right
          exact List.Perm.of_eq (by
            have htake : c3.A.take (t + 1) = c3.A.take t ++ [x0] := by
              rw [hx0_def, take_succ_eq (by omega : t < c3.A.length)]
            have hdrop : c3.A.drop (t + 2) = [x2, x3] ++ c3.A.drop (t + 4) := by
              rw [hx2_def, hx3_def,
                drop_cons_eq (show t + 2 < c3.A.length by omega),
                drop_cons_eq (show t + 3 < c3.A.length by omega)]
              rfl
            rw [htake, hdrop]
            simp only [List.append_assoc, List.cons_append, List.nil_append])
  have hndNF : (u₂ :: c3.ux ::
      (c3.A.take (t + 1) ++ c3.A.drop (t + 2) ++ c3.z :: c3.B)).Nodup := by
    have hM := nodup_NF_A c3 (t + 1) (t + 2) (by omega)
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hM⟩⟩
    · intro h
      rcases List.mem_cons.mp h with e | hM'
      · exact hu₂ne e
      · exact hu₂S (mem_S_of_td_A c3 hM')
    · intro h
      exact c3.ux_not_mem (mem_S_of_td_A c3 h)
  -- assemble the bipath
  have hbip : IsBipath G X Y
      ((c3.A.take t).reverse ++ c3.z :: (c3.A.drop (t + 4)).tail.reverse)
      ((c3.A.drop (t + 4)).head hQne)
      ([u₂, c3.A[t + 2], c3.ux, c3.A[t], c3.A[t + 3]] ++ c3.B) :=
    ⟨hR', hBl', hperm.nodup_iff.2 hndNF⟩
  have hlen := c3.hmax _ _ _ (Or.inl hbip)
  simp only [bipathLen, List.length_append, List.length_reverse,
    List.length_cons, List.length_singleton, List.length_tail,
    List.length_drop, List.length_take] at hlen
  omega

end Case3Data

end JSP415
