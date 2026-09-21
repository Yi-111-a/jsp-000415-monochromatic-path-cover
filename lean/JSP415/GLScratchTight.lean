import JSP415.GLIface
import JSP415.GLScratchA
import JSP415.GLScratchW
import JSP415.GLScratchZ
import JSP415.GLScratchD
import JSP415.GLScratchT5

/-!
# The tight subcase of Gyárfás–Lehel Theorem 3, case (iii)

For a maximal red-first bipath `S = A ++ z :: B` (endpoints in `Y`, midpoint
`z ∈ X`) with exactly one `X`-leftover `ux` (`¬ HasUx2`), the equal sizes
`|X| = |Y|` force `Y ⊆ S`, so `sc1 = sc2 = ∅`.  Unless `A ++ [z]` already
furnishes the red goal or `z :: B` the blue goal, counting forces
`|A| = k - 1`, `|B| = ℓ - 1` (hence `k, ℓ` even, `k ≠ ℓ`).  In that arithmetic
setting every edge between `ux`, the `Y`-side vertices `S1U ∪ S2U` of `S` and
the `X`-side vertices `SL` is classifiable: any contrary edge yields a bipath
strictly longer than the maximal one — the paths are built explicitly as
`ux :: arc`, cycle arcs `B.drop t ++ z :: B.take t`, short extensions and
endpoint rotations.  The resulting block facts are exactly `InternalFacts`
and `LeftoverFacts`, and `case3_finale` (`two_block_ramsey`) closes the goal.
-/

open Finset
open Classical

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

/-! ### Generic chain/list helpers -/

/-- In an `adjXY`-chain whose head lies in `Y`, the last vertex lies in `Y`
whenever `l.length - 1` is even. -/
private theorem adjXY_getLast_mem_Y {c : Color} {l : List V}
    (hXY : Disjoint X Y) (h : l.IsChain (Color.adjXY G X Y c)) (hl : l ≠ [])
    (hpar : (l.length - 1) % 2 = 0) (hhead : l.head hl ∈ Y) :
    l.getLast hl ∈ Y := by
  have hp : 0 < l.length := List.length_pos_of_ne_nil hl
  have hs := (Color.adjXY.same_side h hXY (i := 0) (j := l.length - 1)
      hp (by omega) (Nat.zero_le _) (by omega)).2
  rw [List.getElem_zero hp,
    List.getElem_length_sub_one_eq_getLast (by omega)] at hs
  exact hs.mp hhead

private theorem adjXY_getLast_mem_X {c : Color} {l : List V}
    (hXY : Disjoint X Y) (h : l.IsChain (Color.adjXY G X Y c)) (hl : l ≠ [])
    (hpar : (l.length - 1) % 2 = 0) (hhead : l.head hl ∈ X) :
    l.getLast hl ∈ X := by
  have hp : 0 < l.length := List.length_pos_of_ne_nil hl
  have hs := (Color.adjXY.same_side h hXY (i := 0) (j := l.length - 1)
      hp (by omega) (Nat.zero_le _) (by omega)).1
  rw [List.getElem_zero hp,
    List.getElem_length_sub_one_eq_getLast (by omega)] at hs
  exact hs.mp hhead

/-- `take i` and `drop i` of a `Nodup` list share no vertex. -/
private theorem take_drop_ne {l : List V} (hnd : l.Nodup) {i : ℕ} {a b : V}
    (ha : a ∈ l.drop i) (hb : b ∈ l.take i) : a ≠ b := by
  rintro rfl
  obtain ⟨p, hp, hpeq⟩ := List.mem_drop_iff_getElem.mp ha
  obtain ⟨q, hq, hqeq⟩ := List.mem_take_iff_getElem.mp hb
  have hq' : q < i := lt_of_lt_of_le hq (Nat.min_le_left _ _)
  have e : q = i + p := hnd.getElem_inj.mp (hqeq.trans hpeq.symm)
  omega

/-- A singleton list is a chain for any relation. -/
private theorem chain_singleton {R : V → V → Prop} {a : V} : [a].IsChain R :=
  List.isChain_cons.mpr ⟨fun y hy ↦ absurd hy (Option.not_mem_none _),
    List.isChain_nil⟩

namespace Case3Data

variable (c3 : Case3Data G X Y)

/-! ### Membership in `S` and side parity -/

theorem mem_S_of_eq_z {x : V} (hx : x = c3.z) : x ∈ c3.A ++ c3.z :: c3.B := by
  rw [List.mem_append, List.mem_cons]
  exact Or.inr (Or.inl hx)

theorem mem_S_of_mem_A {x : V} (hx : x ∈ c3.A) : x ∈ c3.A ++ c3.z :: c3.B :=
  List.mem_append_left _ hx

theorem mem_S_of_mem_B {x : V} (hx : x ∈ c3.B) : x ∈ c3.A ++ c3.z :: c3.B :=
  List.mem_append_right _ (List.mem_cons_of_mem _ hx)

theorem ux_notMem_A : c3.ux ∉ c3.A := (c3.hb.notMem_pieces c3.hux.2).1
theorem ux_notMem_B : c3.ux ∉ c3.B := (c3.hb.notMem_pieces c3.hux.2).2.2
theorem ux_ne_z : c3.ux ≠ c3.z := (c3.hb.notMem_pieces c3.hux.2).2.1
theorem z_notMem_A : c3.z ∉ c3.A := c3.hb.disjoint_pieces.1
theorem z_notMem_B : c3.z ∉ c3.B := c3.hb.disjoint_pieces.2.1
theorem disjoint_AB : c3.A.Disjoint c3.B := c3.hb.disjoint_pieces.2.2
theorem A_nodup : c3.A.Nodup := c3.hb.2.2.of_append_left
theorem B_nodup : c3.B.Nodup := (List.nodup_cons.mp c3.hb.2.2.of_append_right).2

theorem S1_nodup : (c3.A ++ [c3.z]).Nodup := by
  rw [List.nodup_append]
  refine ⟨c3.A_nodup, by simp, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton] at hb
  exact fun h ↦ c3.z_notMem_A (hb ▸ h ▸ ha)

theorem S2_nodup : (c3.z :: c3.B).Nodup :=
  List.nodup_cons.mpr ⟨c3.z_notMem_B, c3.B_nodup⟩

/-- `A[i] ∈ Y` for even `i`: the red chain `A ++ [z]` alternates and
`A.head ∈ Y`. -/
theorem A_memY (hXY : Disjoint X Y) {i : ℕ} (hi : i < c3.A.length)
    (hpar : i % 2 = 0) : c3.A[i] ∈ Y := by
  have hs := (Color.adjXY.same_side c3.hb.1 hXY
    (List.length_pos_of_ne_nil (by simp : c3.A ++ [c3.z] ≠ []))
    (by simp; omega) (Nat.zero_le i) (by omega)).2
  rw [List.getElem_append_left (List.length_pos_of_ne_nil c3.hA),
    List.getElem_append_left hi,
    List.getElem_zero (List.length_pos_of_ne_nil c3.hA)] at hs
  exact hs.mp c3.hhead

/-- `A[i] ∈ X` for odd `i`. -/
theorem A_memX (hXY : Disjoint X Y) {i : ℕ} (hi : i < c3.A.length)
    (hpar : i % 2 = 1) : c3.A[i] ∈ X := by
  have hs := (Color.adjXY.opp_side c3.hb.1 hXY
    (List.length_pos_of_ne_nil (by simp : c3.A ++ [c3.z] ≠ []))
    (by simp; omega) (Nat.zero_le i) (by omega)).2
  rw [List.getElem_append_left (List.length_pos_of_ne_nil c3.hA),
    List.getElem_append_left hi,
    List.getElem_zero (List.length_pos_of_ne_nil c3.hA)] at hs
  exact hs.mp c3.hhead

/-- `B[j] ∈ Y` for even `j` (index `j+1` in `z :: B` is odd, opposite of
`z ∈ X`). -/
theorem B_memY (hXY : Disjoint X Y) {j : ℕ} (hj : j < c3.B.length)
    (hpar : j % 2 = 0) : c3.B[j] ∈ Y := by
  have hs := (Color.adjXY.opp_side c3.hb.2.1 hXY
    (by simp) (by simp; omega) (Nat.zero_le (j + 1)) (by omega)).1
  rw [List.getElem_cons_zero, List.getElem_cons_succ] at hs
  exact hs.mp c3.hz

/-- `B[j] ∈ X` for odd `j`. -/
theorem B_memX (hXY : Disjoint X Y) {j : ℕ} (hj : j < c3.B.length)
    (hpar : j % 2 = 1) : c3.B[j] ∈ X := by
  have hs := (Color.adjXY.same_side c3.hb.2.1 hXY
    (by simp) (by simp; omega) (Nat.zero_le (j + 1)) (by omega)).1
  rw [List.getElem_cons_zero, List.getElem_cons_succ] at hs
  exact hs.mp c3.hz

/-- `A.length` is odd: if it were even, `z` would lie in `Y`. -/
theorem A_length_odd (hXY : Disjoint X Y) : c3.A.length % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one c3.A.length with h | h
  · exfalso
    have hrlen : (c3.A ++ [c3.z]).length = c3.A.length + 1 := by simp
    have hs := (Color.adjXY.same_side c3.hb.1 hXY (i := 0)
        (j := (c3.A ++ [c3.z]).length - 1) (by rw [hrlen]; omega)
        (by rw [hrlen]; omega) (Nat.zero_le _)
        (by rw [hrlen]; omega)).2
    rw [List.getElem_append_left (List.length_pos_of_ne_nil c3.hA),
      List.getElem_zero (List.length_pos_of_ne_nil c3.hA),
      List.getElem_length_sub_one_eq_getLast,
      List.getLast_append_of_ne_nil _ (by simp : [c3.z] ≠ []),
      List.getLast_singleton] at hs
    exact (Disjoint.notMem_left hXY c3.hz) (hs.mp c3.hhead)
  · exact h

/-- `B.length` is odd: if it were even, the head-side count would force
`B.getLast ∈ X`, contradicting `hlast`. -/
theorem B_length_odd (hXY : Disjoint X Y) : c3.B.length % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one c3.B.length with h | h
  · exfalso
    have hrlen : (c3.z :: c3.B).length = c3.B.length + 1 := by simp
    have hs := (Color.adjXY.same_side c3.hb.2.1 hXY (i := 0)
        (j := (c3.z :: c3.B).length - 1) (by rw [hrlen]; omega)
        (by rw [hrlen]; omega) (Nat.zero_le _)
        (by rw [hrlen]; omega)).2
    rw [List.getElem_zero (by rw [hrlen]; omega : 0 < (c3.z :: c3.B).length),
      List.head_cons, List.getElem_length_sub_one_eq_getLast,
      List.getLast_cons c3.hB] at hs
    exact (Disjoint.notMem_left hXY c3.hz) (hs.mpr c3.hlast)
  · exact h

/-! ### Membership characterizations of `S1U`, `S2U`, `SL` -/

theorem mem_S1U (hXY : Disjoint X Y) {u : V} (hu : u ∈ c3.S1U) :
    ∃ i : ℕ, ∃ hi : i < c3.A.length, c3.A[i] = u ∧ i % 2 = 0 := by
  obtain ⟨humem, huY⟩ := Finset.mem_filter.mp hu
  rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at humem
  rcases humem with humem | humem
  · obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.mp humem
    subst hiu
    refine ⟨i, hi, rfl, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · exact h
    · exact absurd (c3.A_memX hXY hi h) (Disjoint.notMem_right hXY huY)
  · subst humem
    exact absurd huY (Disjoint.notMem_left hXY c3.hz)

theorem mem_S2U (hXY : Disjoint X Y) {u : V} (hu : u ∈ c3.S2U) :
    ∃ j : ℕ, ∃ hj : j < c3.B.length, c3.B[j] = u ∧ j % 2 = 0 := by
  obtain ⟨humem, huY⟩ := Finset.mem_filter.mp hu
  rw [List.mem_toFinset, List.mem_cons] at humem
  rcases humem with humem | humem
  · subst humem
    exact absurd huY (Disjoint.notMem_left hXY c3.hz)
  · obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp humem
    subst hju
    refine ⟨j, hj, rfl, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · exact h
    · exact absurd (c3.B_memX hXY hj h) (Disjoint.notMem_right hXY huY)

theorem mem_SL (hXY : Disjoint X Y) {l : V} (hl : l ∈ c3.SL) :
    (∃ i : ℕ, ∃ hi : i < c3.A.length, c3.A[i] = l ∧ i % 2 = 1) ∨ l = c3.z ∨
      ∃ j : ℕ, ∃ hj : j < c3.B.length, c3.B[j] = l ∧ j % 2 = 1 := by
  obtain ⟨hlmem, hlX⟩ := Finset.mem_filter.mp hl
  rw [List.mem_toFinset, List.mem_append, List.mem_cons] at hlmem
  rcases hlmem with hlmem | hlmem | hlmem
  · obtain ⟨i, hi, hil⟩ := List.mem_iff_getElem.mp hlmem
    subst hil
    refine Or.inl ⟨i, hi, rfl, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · exact absurd (c3.A_memY hXY hi h) (Disjoint.notMem_left hXY hlX)
    · exact h
  · exact Or.inr (Or.inl hlmem)
  · obtain ⟨j, hj, hjl⟩ := List.mem_iff_getElem.mp hlmem
    subst hjl
    refine Or.inr (Or.inr ⟨j, hj, rfl, ?_⟩)
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · exact absurd (c3.B_memY hXY hj h) (Disjoint.notMem_left hXY hlX)
    · exact h

/-- `¬ HasUx2` iff `X ∖ S = {ux}`. -/
theorem L2_eq_singleton (hn : ¬ c3.HasUx2) : c3.L2 = {c3.ux} := by
  ext u
  constructor
  · intro hu
    rw [Finset.mem_singleton]
    obtain ⟨huX, huS⟩ := Finset.mem_sdiff.mp hu
    by_contra hne
    exact hn ⟨u, huX, fun h ↦ huS (List.mem_toFinset.mpr h), hne⟩
  · intro hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact Finset.mem_sdiff.mpr
      ⟨c3.hux.1, fun h ↦ c3.hux.2 (List.mem_toFinset.mp h)⟩

/-! ### Cycle-arc chains -/

/-- The red "cycle arc" `A.drop t ++ z :: A.take t` is a red chain for
`t ≤ A.length` (given claim A's `A.head–z` edge). -/
theorem arcA_chain (hA1 : Color.adjXY G X Y .red (c3.A.head c3.hA) c3.z)
    {t : ℕ} (ht : t ≤ c3.A.length) :
    (c3.A.drop t ++ c3.z :: c3.A.take t).IsChain (Color.adjXY G X Y .red) := by
  obtain ⟨hred, -, -⟩ := c3.hb
  have hchA : c3.A.IsChain (Color.adjXY G X Y .red) := hred.left_of_append
  rw [List.isChain_append]
  refine ⟨hchA.drop t, ?_, ?_⟩
  · rw [List.isChain_cons]
    refine ⟨?_, hchA.take t⟩
    intro y hy
    rw [List.head?_take] at hy
    by_cases ht0 : t = 0
    · subst ht0; simp at hy
    · simp only [ht0, ↓reduceIte, List.head?_eq_head c3.hA,
        Option.mem_some] at hy
      subst hy
      exact Color.adjXY.symm hA1
  · intro x hx y hy
    rw [List.getLast?_drop] at hx
    by_cases hlen : c3.A.length ≤ t
    · rw [if_pos hlen] at hx
      exact absurd hx (Option.not_mem_none _)
    · rw [if_neg hlen, List.getLast?_eq_getLast c3.hA, Option.mem_some] at hx
      subst hx
      rw [List.head?_cons, Option.mem_some] at hy
      subst hy
      exact c3.hb.red_last_edge c3.hA

/-- The blue "cycle arc" `B.drop t ++ z :: B.take t` is a blue chain for
`t ≤ B.length` (given claim A's `z–B.getLast` edge). -/
theorem arcB_chain (hA2 : Color.adjXY G X Y .blue c3.z (c3.B.getLast c3.hB))
    {t : ℕ} (ht : t ≤ c3.B.length) :
    (c3.B.drop t ++ c3.z :: c3.B.take t).IsChain (Color.adjXY G X Y .blue) := by
  obtain ⟨-, hblue, -⟩ := c3.hb
  have hchB : c3.B.IsChain (Color.adjXY G X Y .blue) := hblue.tail
  rw [List.isChain_append]
  refine ⟨hchB.drop t, ?_, ?_⟩
  · rw [List.isChain_cons]
    refine ⟨?_, hchB.take t⟩
    intro y hy
    rw [List.head?_take] at hy
    by_cases ht0 : t = 0
    · subst ht0; simp at hy
    · simp only [ht0, ↓reduceIte, List.head?_eq_head c3.hB,
        Option.mem_some] at hy
      subst hy
      exact c3.hb.blue_first_edge c3.hB
  · intro x hx y hy
    rw [List.getLast?_drop] at hx
    by_cases hlen : c3.B.length ≤ t
    · rw [if_pos hlen] at hx
      exact absurd hx (Option.not_mem_none _)
    · rw [if_neg hlen, List.getLast?_eq_getLast c3.hB, Option.mem_some] at hx
      subst hx
      rw [List.head?_cons, Option.mem_some] at hy
      subst hy
      exact Color.adjXY.symm hA2

/-! ### The eight rotation constructions

Each lemma shows: if the indicated "wrong-coloured" edge exists, an explicit
path already solves the goal (it is strictly longer than `S`, hence would
contradict maximality — but for `BipGoal` only the path matters).
`hk : k + 1 ≤ A.length + 2` and `hℓ : ℓ + 1 ≤ B.length + 2` hold exactly in
the tight arithmetic subcase `|A| = k - 1`, `|B| = ℓ - 1`. -/

/-- Claim C red branch: `ux–aᵢ` red (`i` even) gives the red path
`ux :: A.drop i ++ z :: A.take i` on `|A| + 2` vertices. -/
theorem goal_uxA_red (hXY : Disjoint X Y)
    (hA1 : Color.adjXY G X Y .red (c3.A.head c3.hA) c3.z)
    {i : ℕ} (hi : i < c3.A.length) (hpar : i % 2 = 0)
    (he : G.Adj c3.ux c3.A[i]) {k ℓ : ℕ} (hk : k + 1 ≤ c3.A.length + 2) :
    BipGoal G X Y k ℓ := by
  have hhead : (c3.A.drop i ++ c3.z :: c3.A.take i).head? = some c3.A[i] := by
    rw [List.head?_append, List.head?_drop,
      List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩]
    rfl
  have hch : (c3.ux :: (c3.A.drop i ++ c3.z :: c3.A.take i)).IsChain
      (Color.adjXY G X Y .red) := by
    rw [List.isChain_cons]
    refine ⟨?_, c3.arcA_chain hA1 hi.le⟩
    intro y hy
    rw [hhead, Option.mem_some] at hy
    subst hy
    exact ⟨Or.inl ⟨c3.hux.1, c3.A_memY hXY hi hpar⟩, he⟩
  have hnd : (c3.ux :: (c3.A.drop i ++ c3.z :: c3.A.take i)).Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro hu
      rw [List.mem_append, List.mem_cons] at hu
      rcases hu with hu | hu | hu
      · exact c3.hux.2 (c3.mem_S_of_mem_A (List.mem_of_mem_drop hu))
      · exact c3.hux.2 (c3.mem_S_of_eq_z hu)
      · exact c3.hux.2 (c3.mem_S_of_mem_A (List.mem_of_mem_take hu))
    · rw [List.nodup_append]
      refine ⟨c3.A_nodup.sublist (List.drop_sublist _ _), ?_, ?_⟩
      · rw [List.nodup_cons]
        exact ⟨fun h ↦ c3.z_notMem_A (List.mem_of_mem_take h),
          c3.A_nodup.sublist (List.take_sublist _ _)⟩
      · intro a ha b hb
        rw [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact fun h ↦ c3.z_notMem_A (h ▸ List.mem_of_mem_drop ha)
        · exact take_drop_ne c3.A_nodup ha hb
  obtain ⟨p, hchp, hpl⟩ := vertPath_of_chain (List.cons_ne_nil _ _) hnd hch
  refine ⟨p, Or.inl ⟨hchp, ?_⟩⟩
  rw [hpl]
  simp only [List.length_cons, List.length_append, List.length_drop,
    List.length_take]
  rw [Nat.min_eq_left hi.le]
  omega

/-- Claim C blue branch: `ux–bⱼ` blue (`j` even) gives the blue path
`ux :: B.drop j ++ z :: B.take j` on `|B| + 2` vertices. -/
theorem goal_uxB_blue (hXY : Disjoint X Y)
    (hA2 : Color.adjXY G X Y .blue c3.z (c3.B.getLast c3.hB))
    {j : ℕ} (hj : j < c3.B.length) (hpar : j % 2 = 0)
    (he : ¬ G.Adj c3.ux c3.B[j]) {k ℓ : ℕ} (hℓ : ℓ + 1 ≤ c3.B.length + 2) :
    BipGoal G X Y k ℓ := by
  have hhead : (c3.B.drop j ++ c3.z :: c3.B.take j).head? = some c3.B[j] := by
    rw [List.head?_append, List.head?_drop,
      List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩]
    rfl
  have hch : (c3.ux :: (c3.B.drop j ++ c3.z :: c3.B.take j)).IsChain
      (Color.adjXY G X Y .blue) := by
    rw [List.isChain_cons]
    refine ⟨?_, c3.arcB_chain hA2 hj.le⟩
    intro y hy
    rw [hhead, Option.mem_some] at hy
    subst hy
    exact ⟨Or.inl ⟨c3.hux.1, c3.B_memY hXY hj hpar⟩, he⟩
  have hnd : (c3.ux :: (c3.B.drop j ++ c3.z :: c3.B.take j)).Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro hu
      rw [List.mem_append, List.mem_cons] at hu
      rcases hu with hu | hu | hu
      · exact c3.hux.2 (c3.mem_S_of_mem_B (List.mem_of_mem_drop hu))
      · exact c3.hux.2 (c3.mem_S_of_eq_z hu)
      · exact c3.hux.2 (c3.mem_S_of_mem_B (List.mem_of_mem_take hu))
    · rw [List.nodup_append]
      refine ⟨c3.B_nodup.sublist (List.drop_sublist _ _), ?_, ?_⟩
      · rw [List.nodup_cons]
        exact ⟨fun h ↦ c3.z_notMem_B (List.mem_of_mem_take h),
          c3.B_nodup.sublist (List.take_sublist _ _)⟩
      · intro a ha b hb
        rw [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact fun h ↦ c3.z_notMem_B (h ▸ List.mem_of_mem_drop ha)
        · exact take_drop_ne c3.B_nodup ha hb
  obtain ⟨p, hchp, hpl⟩ := vertPath_of_chain (List.cons_ne_nil _ _) hnd hch
  refine ⟨p, Or.inr ⟨hchp, ?_⟩⟩
  rw [hpl]
  simp only [List.length_cons, List.length_append, List.length_drop,
    List.length_take]
  rw [Nat.min_eq_left hj.le]
  omega

/-- Claim F1: `aᵢ–bⱼ` blue (`i` even, `j` odd) gives the blue path
`B.drop (j+1) ++ z :: (B.take (j+1) ++ [aᵢ, ux])` on `|B| + 3` vertices. -/
theorem goal_crossAB_blue (hXY : Disjoint X Y)
    (hA2 : Color.adjXY G X Y .blue c3.z (c3.B.getLast c3.hB))
    (hC1 : ∀ i (hi : i < c3.A.length), i % 2 = 0 → ¬ G.Adj c3.ux c3.A[i])
    {i j : ℕ} (hi : i < c3.A.length) (hpi : i % 2 = 0)
    (hj : j < c3.B.length) (hpj : j % 2 = 1) (hjs : j + 1 < c3.B.length)
    (he : ¬ G.Adj c3.A[i] c3.B[j]) {k ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ c3.B.length + 2) : BipGoal G X Y k ℓ := by
  have hchB : c3.B.IsChain (Color.adjXY G X Y .blue) := c3.hb.2.1.tail
  have hAiY : c3.A[i] ∈ Y := c3.A_memY hXY hi hpi
  have hBjX : c3.B[j] ∈ X := c3.B_memX hXY hj hpj
  have hnd : (c3.B.drop (j + 1) ++
      c3.z :: (c3.B.take (j + 1) ++ [c3.A[i], c3.ux])).Nodup := by
    rw [List.nodup_append]
    refine ⟨c3.B_nodup.sublist (List.drop_sublist _ _), ?_, ?_⟩
    · rw [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro h
        rw [List.mem_append, List.mem_cons, List.mem_singleton] at h
        rcases h with h | h | h
        · exact c3.z_notMem_B (List.mem_of_mem_take h)
        · exact Disjoint.notMem_left hXY c3.hz (h ▸ hAiY)
        · exact c3.hux.2 (c3.mem_S_of_eq_z h.symm)
      · rw [List.nodup_append]
        refine ⟨c3.B_nodup.sublist (List.take_sublist _ _), ?_, ?_⟩
        · rw [List.nodup_cons]
          refine ⟨?_, by simp⟩
          intro h
          rw [List.mem_singleton] at h
          exact Disjoint.notMem_right hXY hAiY (h ▸ c3.hux.1)
        · intro a ha b hb
          rw [List.mem_cons, List.mem_singleton] at hb
          rcases hb with rfl | rfl
          · exact fun h ↦ c3.disjoint_AB (List.getElem_mem hi)
              (h ▸ List.mem_of_mem_take ha)
          · exact fun h ↦ c3.ux_notMem_B (h ▸ List.mem_of_mem_take ha)
    · intro a ha b hb
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact fun h ↦ c3.z_notMem_B (h ▸ List.mem_of_mem_drop ha)
      · rw [List.mem_append, List.mem_cons, List.mem_singleton] at hb
        rcases hb with hb | rfl | rfl
        · exact take_drop_ne c3.B_nodup ha hb
        · exact fun h ↦ c3.disjoint_AB (List.getElem_mem hi)
            (h ▸ List.mem_of_mem_drop ha)
        · exact fun h ↦ c3.ux_notMem_B (h ▸ List.mem_of_mem_drop ha)
  have hch : (c3.B.drop (j + 1) ++
      c3.z :: (c3.B.take (j + 1) ++ [c3.A[i], c3.ux])).IsChain
      (Color.adjXY G X Y .blue) := by
    rw [List.isChain_append]
    refine ⟨hchB.drop _, ?_, ?_⟩
    · rw [List.isChain_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [List.head?_append, List.head?_take,
          if_neg (by omega : j + 1 ≠ 0), List.head?_eq_head c3.hB] at hy
        rw [Option.some_or, Option.mem_some] at hy
        subst hy
        exact c3.hb.blue_first_edge c3.hB
      · rw [List.isChain_append]
        refine ⟨hchB.take _, ?_, ?_⟩
        · rw [List.isChain_cons]
          refine ⟨?_, chain_singleton⟩
          intro y hy
          rw [List.head?_cons, Option.mem_some] at hy
          subst hy
          exact ⟨Or.inr ⟨hAiY, c3.hux.1⟩, fun h ↦ hC1 i hi hpi h.symm⟩
        · intro x hx y hy
          rw [List.getLast?_take, if_neg (by omega : j + 1 ≠ 0),
            List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩,
            Option.some_or, Option.mem_some] at hx
          subst hx
          rw [List.head?_cons, Option.mem_some] at hy
          subst hy
          exact ⟨Or.inl ⟨hBjX, hAiY⟩, fun h ↦ he h.symm⟩
    · intro x hx y hy
      rw [List.getLast?_drop, if_neg (by omega : ¬ c3.B.length ≤ j + 1),
        List.getLast?_eq_getLast c3.hB, Option.mem_some] at hx
      subst hx
      rw [List.head?_cons, Option.mem_some] at hy
      subst hy
      exact Color.adjXY.symm hA2
  obtain ⟨p, hchp, hpl⟩ := vertPath_of_chain
    (by simp : (c3.B.drop (j + 1) ++
      c3.z :: (c3.B.take (j + 1) ++ [c3.A[i], c3.ux])) ≠ []) hnd hch
  refine ⟨p, Or.inr ⟨hchp, ?_⟩⟩
  rw [hpl]
  simp only [List.length_cons, List.length_append, List.length_drop,
    List.length_take]
  rw [Nat.min_eq_left (by omega : j + 1 ≤ c3.B.length)]
  omega

/-- Claim F2: `aᵢ–bⱼ` red (`i` odd, `j` even) gives the red path
`A.drop (i+1) ++ z :: (A.take (i+1) ++ [bⱼ, ux])` on `|A| + 3` vertices. -/
theorem goal_crossAB_red (hXY : Disjoint X Y)
    (hA1 : Color.adjXY G X Y .red (c3.A.head c3.hA) c3.z)
    (hC2 : ∀ j (hj : j < c3.B.length), j % 2 = 0 → G.Adj c3.ux c3.B[j])
    {i j : ℕ} (hi : i < c3.A.length) (hpi : i % 2 = 1)
    (hj : j < c3.B.length) (hpj : j % 2 = 0) (his : i + 1 < c3.A.length)
    (he : G.Adj c3.A[i] c3.B[j]) {k ℓ : ℕ}
    (hk : k + 1 ≤ c3.A.length + 2) : BipGoal G X Y k ℓ := by
  have hchA : c3.A.IsChain (Color.adjXY G X Y .red) := c3.hb.1.left_of_append
  have hAiX : c3.A[i] ∈ X := c3.A_memX hXY hi hpi
  have hBjY : c3.B[j] ∈ Y := c3.B_memY hXY hj hpj
  have hnd : (c3.A.drop (i + 1) ++
      c3.z :: (c3.A.take (i + 1) ++ [c3.B[j], c3.ux])).Nodup := by
    rw [List.nodup_append]
    refine ⟨c3.A_nodup.sublist (List.drop_sublist _ _), ?_, ?_⟩
    · rw [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro h
        rw [List.mem_append, List.mem_cons, List.mem_singleton] at h
        rcases h with h | h | h
        · exact c3.z_notMem_A (List.mem_of_mem_take h)
        · exact Disjoint.notMem_left hXY c3.hz (h ▸ hBjY)
        · exact c3.hux.2 (c3.mem_S_of_eq_z h.symm)
      · rw [List.nodup_append]
        refine ⟨c3.A_nodup.sublist (List.take_sublist _ _), ?_, ?_⟩
        · rw [List.nodup_cons]
          refine ⟨?_, by simp⟩
          intro h
          rw [List.mem_singleton] at h
          exact Disjoint.notMem_right hXY hBjY (h ▸ c3.hux.1)
        · intro a ha b hb
          rw [List.mem_cons, List.mem_singleton] at hb
          rcases hb with rfl | rfl
          · exact fun h ↦ c3.disjoint_AB (List.mem_of_mem_take ha)
              (h ▸ List.getElem_mem hj)
          · exact fun h ↦ c3.ux_notMem_A (h ▸ List.mem_of_mem_take ha)
    · intro a ha b hb
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact fun h ↦ c3.z_notMem_A (h ▸ List.mem_of_mem_drop ha)
      · rw [List.mem_append, List.mem_cons, List.mem_singleton] at hb
        rcases hb with hb | rfl | rfl
        · exact take_drop_ne c3.A_nodup ha hb
        · exact fun h ↦ c3.disjoint_AB (List.mem_of_mem_drop ha)
            (h ▸ List.getElem_mem hj)
        · exact fun h ↦ c3.ux_notMem_A (h ▸ List.mem_of_mem_drop ha)
  have hch : (c3.A.drop (i + 1) ++
      c3.z :: (c3.A.take (i + 1) ++ [c3.B[j], c3.ux])).IsChain
      (Color.adjXY G X Y .red) := by
    rw [List.isChain_append]
    refine ⟨hchA.drop _, ?_, ?_⟩
    · rw [List.isChain_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [List.head?_append, List.head?_take,
          if_neg (by omega : i + 1 ≠ 0), List.head?_eq_head c3.hA] at hy
        rw [Option.some_or, Option.mem_some] at hy
        subst hy
        exact Color.adjXY.symm hA1
      · rw [List.isChain_append]
        refine ⟨hchA.take _, ?_, ?_⟩
        · rw [List.isChain_cons]
          refine ⟨?_, chain_singleton⟩
          intro y hy
          rw [List.head?_cons, Option.mem_some] at hy
          subst hy
          exact ⟨Or.inr ⟨hBjY, c3.hux.1⟩, (hC2 j hj hpj).symm⟩
        · intro x hx y hy
          rw [List.getLast?_take, if_neg (by omega : i + 1 ≠ 0),
            List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩,
            Option.some_or, Option.mem_some] at hx
          subst hx
          rw [List.head?_cons, Option.mem_some] at hy
          subst hy
          exact ⟨Or.inl ⟨hAiX, hBjY⟩, he⟩
    · intro x hx y hy
      rw [List.getLast?_drop, if_neg (by omega : ¬ c3.A.length ≤ i + 1),
        List.getLast?_eq_getLast c3.hA, Option.mem_some] at hx
      subst hx
      rw [List.head?_cons, Option.mem_some] at hy
      subst hy
      exact c3.hb.red_last_edge c3.hA
  obtain ⟨p, hchp, hpl⟩ := vertPath_of_chain
    (by simp : (c3.A.drop (i + 1) ++
      c3.z :: (c3.A.take (i + 1) ++ [c3.B[j], c3.ux])) ≠ []) hnd hch
  refine ⟨p, Or.inl ⟨hchp, ?_⟩⟩
  rw [hpl]
  simp only [List.length_cons, List.length_append, List.length_drop,
    List.length_take]
  rw [Nat.min_eq_left (by omega : i + 1 ≤ c3.A.length)]
  omega

/-- Claim B' red case: `z–bⱼ` red (`j` even) gives the red path
`(A ++ [z]) ++ [bⱼ, ux]` on `|A| + 3` vertices. -/
theorem goal_zB_red (hXY : Disjoint X Y)
    (hC2 : ∀ j (hj : j < c3.B.length), j % 2 = 0 → G.Adj c3.ux c3.B[j])
    {j : ℕ} (hj : j < c3.B.length) (hpj : j % 2 = 0)
    (he : G.Adj c3.z c3.B[j]) {k ℓ : ℕ} (hk : k + 1 ≤ c3.A.length + 2) :
    BipGoal G X Y k ℓ := by
  have hBjY : c3.B[j] ∈ Y := c3.B_memY hXY hj hpj
  have hch : ((c3.A ++ [c3.z]) ++ [c3.B[j], c3.ux]).IsChain
      (Color.adjXY G X Y .red) := by
    rw [List.isChain_append]
    refine ⟨c3.hb.1, ?_, ?_⟩
    · rw [List.isChain_cons]
      refine ⟨?_, chain_singleton⟩
      intro y hy
      rw [List.head?_cons, Option.mem_some] at hy
      subst hy
      exact ⟨Or.inr ⟨hBjY, c3.hux.1⟩, (hC2 j hj hpj).symm⟩
    · intro x hx y hy
      rw [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.mem_some] at hx
      subst hx
      rw [List.head?_cons, Option.mem_some] at hy
      subst hy
      exact ⟨Or.inl ⟨c3.hz, hBjY⟩, he⟩
  have hnd : ((c3.A ++ [c3.z]) ++ [c3.B[j], c3.ux]).Nodup := by
    rw [List.nodup_append]
    refine ⟨c3.S1_nodup, ?_, ?_⟩
    · rw [List.nodup_cons]
      refine ⟨?_, by simp⟩
      intro h
      rw [List.mem_singleton] at h
      exact Disjoint.notMem_right hXY hBjY (h ▸ c3.hux.1)
    · intro a ha b hb
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · rw [List.mem_cons, List.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact fun h ↦ c3.disjoint_AB ha (h ▸ List.getElem_mem hj)
        · exact fun h ↦ c3.ux_notMem_A (h ▸ ha)
      · subst ha
        rw [List.mem_cons, List.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact fun h ↦ c3.z_notMem_B (h ▸ List.getElem_mem hj)
        · exact fun h ↦ c3.hux.2 (c3.mem_S_of_eq_z h.symm)
  obtain ⟨p, hchp, hpl⟩ := vertPath_of_chain
    (by simp : (c3.A ++ [c3.z]) ++ [c3.B[j], c3.ux] ≠ []) hnd hch
  refine ⟨p, Or.inl ⟨hchp, ?_⟩⟩
  rw [hpl]
  simp only [List.length_append, List.length_cons, List.length_singleton]
  omega

/-- Claim E inside `B`: `bᵢ–bⱼ` red (`i` even, `j` odd) gives the red path
`ux :: bᵢ :: bⱼ :: (A ++ [z])` on `|A| + 4` vertices. -/
theorem goal_BB_red (hXY : Disjoint X Y)
    (hC2 : ∀ j (hj : j < c3.B.length), j % 2 = 0 → G.Adj c3.ux c3.B[j])
    (hF1 : ∀ i (hi : i < c3.A.length) j (hj : j < c3.B.length),
      i % 2 = 0 → j % 2 = 1 → G.Adj c3.A[i] c3.B[j])
    {i j : ℕ} (hi : i < c3.B.length) (hpi : i % 2 = 0)
    (hj : j < c3.B.length) (hpj : j % 2 = 1)
    (he : G.Adj c3.B[i] c3.B[j]) {k ℓ : ℕ} (hk : k + 1 ≤ c3.A.length + 2) :
    BipGoal G X Y k ℓ := by
  have hBiY : c3.B[i] ∈ Y := c3.B_memY hXY hi hpi
  have hBjX : c3.B[j] ∈ X := c3.B_memX hXY hj hpj
  have hpA : 0 < c3.A.length := List.length_pos_of_ne_nil c3.hA
  have hA0Y : c3.A[0]'hpA ∈ Y := c3.A_memY hXY hpA rfl
  have hch : (c3.ux :: c3.B[i] :: c3.B[j] :: (c3.A ++ [c3.z])).IsChain
      (Color.adjXY G X Y .red) := by
    rw [List.isChain_cons]
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [List.head?_cons, Option.mem_some] at hy
      subst hy
      exact ⟨Or.inl ⟨c3.hux.1, hBiY⟩, hC2 i hi hpi⟩
    · rw [List.isChain_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [List.head?_cons, Option.mem_some] at hy
        subst hy
        exact ⟨Or.inr ⟨hBiY, hBjX⟩, he⟩
      · rw [List.isChain_cons]
        refine ⟨?_, c3.hb.1⟩
        intro y hy
        have hh : (c3.A ++ [c3.z]).head? = some c3.A[0] := by
          rw [List.head?_append, List.head?_eq_getElem?,
            List.getElem?_eq_some_iff.mpr ⟨hpA, rfl⟩]
          rfl
        rw [hh, Option.mem_some] at hy
        subst hy
        exact ⟨Or.inl ⟨hBjX, hA0Y⟩,
          (hF1 0 hpA j hj (by decide) hpj).symm⟩
  have hnd : (c3.ux :: c3.B[i] :: c3.B[j] :: (c3.A ++ [c3.z])).Nodup := by
    rw [List.nodup_cons, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, ?_, c3.S1_nodup⟩
    · intro h
      rw [List.mem_cons, List.mem_cons, List.mem_append,
        List.mem_singleton] at h
      rcases h with h | h | h | h
      · exact c3.ux_notMem_B (h ▸ List.getElem_mem hi)
      · exact c3.ux_notMem_B (h ▸ List.getElem_mem hj)
      · exact c3.ux_notMem_A h
      · exact c3.hux.2 (c3.mem_S_of_eq_z h)
    · intro h
      rw [List.mem_cons, List.mem_append, List.mem_singleton] at h
      rcases h with h | h | h
      · exact absurd (c3.B_nodup.getElem_inj.mp h) (by omega)
      · exact c3.disjoint_AB h (List.getElem_mem hi)
      · exact Disjoint.notMem_right hXY hBiY (h ▸ c3.hz)
    · intro h
      rw [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact c3.disjoint_AB h (List.getElem_mem hj)
      · exact c3.z_notMem_B (h ▸ List.getElem_mem hj)
  obtain ⟨p, hchp, hpl⟩ := vertPath_of_chain
    (by simp : c3.ux :: c3.B[i] :: c3.B[j] :: (c3.A ++ [c3.z]) ≠ []) hnd hch
  refine ⟨p, Or.inl ⟨hchp, ?_⟩⟩
  rw [hpl]
  simp only [List.length_cons, List.length_append, List.length_singleton]
  omega

/-- Claim E for `z`-edges inside the `A`-block: `aᵢ–z` blue (`i` even) gives
the blue path `ux :: aᵢ :: z :: B.reverse` on `|B| + 3` vertices. -/
theorem goal_Az_blue (hXY : Disjoint X Y)
    (hA2 : Color.adjXY G X Y .blue c3.z (c3.B.getLast c3.hB))
    (hC1 : ∀ i (hi : i < c3.A.length), i % 2 = 0 → ¬ G.Adj c3.ux c3.A[i])
    {i : ℕ} (hi : i < c3.A.length) (hpi : i % 2 = 0)
    (he : ¬ G.Adj c3.A[i] c3.z) {k ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ c3.B.length + 2) : BipGoal G X Y k ℓ := by
  have hchB : c3.B.IsChain (Color.adjXY G X Y .blue) := c3.hb.2.1.tail
  have hAiY : c3.A[i] ∈ Y := c3.A_memY hXY hi hpi
  have hch : (c3.ux :: c3.A[i] :: c3.z :: c3.B.reverse).IsChain
      (Color.adjXY G X Y .blue) := by
    rw [List.isChain_cons]
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [List.head?_cons, Option.mem_some] at hy
      subst hy
      exact ⟨Or.inl ⟨c3.hux.1, hAiY⟩, hC1 i hi hpi⟩
    · rw [List.isChain_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [List.head?_cons, Option.mem_some] at hy
        subst hy
        exact ⟨Or.inr ⟨hAiY, c3.hz⟩, he⟩
      · rw [List.isChain_cons]
        refine ⟨?_, ?_⟩
        · intro y hy
          rw [List.head?_reverse, List.getLast?_eq_getLast c3.hB,
            Option.mem_some] at hy
          subst hy
          exact hA2
        · exact Color.adjXY.isChain_reverse hchB
  have hnd : (c3.ux :: c3.A[i] :: c3.z :: c3.B.reverse).Nodup := by
    rw [List.nodup_cons, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      rw [List.mem_cons, List.mem_cons] at h
      rcases h with h | h | h
      · exact c3.ux_notMem_A (h ▸ List.getElem_mem hi)
      · exact c3.hux.2 (c3.mem_S_of_eq_z h)
      · exact c3.ux_notMem_B (List.mem_reverse.mp h)
    · intro h
      rw [List.mem_cons] at h
      rcases h with h | h
      · exact Disjoint.notMem_left hXY c3.hz (h ▸ hAiY)
      · exact c3.disjoint_AB (List.getElem_mem hi) (List.mem_reverse.mp h)
    · exact fun h ↦ c3.z_notMem_B (List.mem_reverse.mp h)
    · exact (List.reverse_perm _).nodup_iff.mpr c3.B_nodup
  obtain ⟨p, hchp, hpl⟩ := vertPath_of_chain
    (by simp : c3.ux :: c3.A[i] :: c3.z :: c3.B.reverse ≠ []) hnd hch
  refine ⟨p, Or.inr ⟨hchp, ?_⟩⟩
  rw [hpl]
  simp only [List.length_cons, List.length_reverse]
  omega

/-- Claim E inside `A`: `aᵢ–aⱼ` blue (`i` even, `j` odd) gives the blue path
`ux :: aᵢ :: aⱼ :: B` on `|B| + 3` vertices. -/
theorem goal_AA_blue (hXY : Disjoint X Y)
    (hC1 : ∀ i (hi : i < c3.A.length), i % 2 = 0 → ¬ G.Adj c3.ux c3.A[i])
    (hF2 : ∀ i (hi : i < c3.A.length) j (hj : j < c3.B.length),
      i % 2 = 1 → j % 2 = 0 → ¬ G.Adj c3.A[i] c3.B[j])
    {i j : ℕ} (hi : i < c3.A.length) (hpi : i % 2 = 0)
    (hj : j < c3.A.length) (hpj : j % 2 = 1)
    (he : ¬ G.Adj c3.A[i] c3.A[j]) {k ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ c3.B.length + 2) : BipGoal G X Y k ℓ := by
  have hchB : c3.B.IsChain (Color.adjXY G X Y .blue) := c3.hb.2.1.tail
  have hAiY : c3.A[i] ∈ Y := c3.A_memY hXY hi hpi
  have hAjX : c3.A[j] ∈ X := c3.A_memX hXY hj hpj
  have hpB : 0 < c3.B.length := List.length_pos_of_ne_nil c3.hB
  have hB0Y : c3.B[0]'hpB ∈ Y := c3.B_memY hXY hpB rfl
  have hch : (c3.ux :: c3.A[i] :: c3.A[j] :: c3.B).IsChain
      (Color.adjXY G X Y .blue) := by
    rw [List.isChain_cons]
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [List.head?_cons, Option.mem_some] at hy
      subst hy
      exact ⟨Or.inl ⟨c3.hux.1, hAiY⟩, hC1 i hi hpi⟩
    · rw [List.isChain_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [List.head?_cons, Option.mem_some] at hy
        subst hy
        exact ⟨Or.inr ⟨hAiY, hAjX⟩, he⟩
      · rw [List.isChain_cons]
        refine ⟨?_, hchB⟩
        intro y hy
        have hh : c3.B.head? = some c3.B[0] := by
          rw [List.head?_eq_getElem?,
            List.getElem?_eq_some_iff.mpr ⟨hpB, rfl⟩]
        rw [hh, Option.mem_some] at hy
        subst hy
        exact ⟨Or.inl ⟨hAjX, hB0Y⟩, hF2 j hj 0 hpB hpj (by decide)⟩
  have hnd : (c3.ux :: c3.A[i] :: c3.A[j] :: c3.B).Nodup := by
    rw [List.nodup_cons, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, ?_, c3.B_nodup⟩
    · intro h
      rw [List.mem_cons, List.mem_cons] at h
      rcases h with h | h | h
      · exact c3.ux_notMem_A (h ▸ List.getElem_mem hi)
      · exact c3.ux_notMem_A (h ▸ List.getElem_mem hj)
      · exact c3.ux_notMem_B h
    · intro h
      rw [List.mem_cons] at h
      rcases h with h | h
      · exact absurd (c3.A_nodup.getElem_inj.mp h) (by omega)
      · exact c3.disjoint_AB (List.getElem_mem hi) h
    · exact fun h ↦ c3.disjoint_AB (List.getElem_mem hj) h
  obtain ⟨p, hchp, hpl⟩ := vertPath_of_chain
    (by simp : c3.ux :: c3.A[i] :: c3.A[j] :: c3.B ≠ []) hnd hch
  refine ⟨p, Or.inr ⟨hchp, ?_⟩⟩
  rw [hpl]
  simp only [List.length_cons]
  omega

/-! ### Counting in the tight case -/

/-- Side counts: `S` has `X.card - 1` vertices on the `X` side and `Y.card`
vertices on the `Y` side.  Needs `|X| = |Y|` and the unique leftover. -/
theorem card_facts (hXY : Disjoint X Y) (hn : ¬ c3.HasUx2)
    (hm : X.card = Y.card) :
    c3.SL.card = X.card - 1 ∧ (c3.S.toFinset ∩ Y).card = Y.card := by
  have hnd : c3.S.Nodup := c3.hb.2.2
  have hchain : c3.S.IsChain (acrossXY X Y) := IsBipath.acrossChain c3.hb
  have hSlen : c3.S.length = c3.A.length + c3.B.length + 1 := by
    show (c3.A ++ c3.z :: c3.B).length = c3.A.length + c3.B.length + 1
    rw [List.length_append, List.length_cons]; omega
  have hmem : ∀ a ∈ c3.S, a ∈ X ∪ Y := fun a ha ↦
    across_chain_mem_union hXY hchain ha (by
      rw [hSlen]
      have := List.length_pos_of_ne_nil c3.hA
      have := List.length_pos_of_ne_nil c3.hB
      omega)
  have hsum := across_chain_side_sum hXY c3.S hchain hmem
  have hShead : c3.S.head? = some (c3.A.head c3.hA) := by
    show (c3.A ++ c3.z :: c3.B).head? = some (c3.A.head c3.hA)
    rw [List.head?_append, List.head?_eq_head c3.hA, Option.some_or]
  have hdiff := (across_chain_side_diff hXY c3.S hchain hmem).2 _
    (by rw [hShead]; exact Option.mem_some_self _) c3.hhead
  have hXc := sideCount_eq_card X hnd
  have hYc := sideCount_eq_card Y hnd
  have hm1 : 1 ≤ X.card := Finset.card_pos.mpr ⟨c3.ux, c3.hux.1⟩
  have hSLcard : c3.SL.card = X.card - 1 := by
    have hL2 := c3.L2_eq_singleton hn
    have hun : c3.SL ∪ c3.L2 = X := c3.L1_union_L2
    have hdis : Disjoint c3.SL c3.L2 := c3.disjoint_L1_L2
    rw [hL2] at hun hdis
    have hc := Finset.card_union_of_disjoint hdis
    rw [Finset.card_singleton] at hc
    rw [hun] at hc
    omega
  -- `SL` is exactly `S.toFinset ∩ X`.
  have hSL : c3.SL = c3.S.toFinset ∩ X := Finset.filter_mem_eq_inter
  have hrodd := c3.A_length_odd hXY
  have hsodd := c3.B_length_odd hXY
  have hlenodd : (c3.S.length : ℤ) % 2 = 1 := by
    have h1 : (c3.S.length : ℤ) = c3.A.length + c3.B.length + 1 := by
      rw [hSlen]; push_cast; ring
    rw [h1]
    omega
  have hCY : (c3.S.toFinset ∩ Y).card = X.card := by
    have hsum' := hsum
    rw [hXc, hYc] at hsum'
    -- hsum' : ↑(S∩X).card + ↑(S∩Y).card = ↑S.length
    have hSIXz : ((c3.S.toFinset ∩ X).card : ℤ) = (X.card : ℤ) - 1 := by
      rw [← hSL]
      omega
    rcases hdiff with h0 | h0 <;> rw [hXc, hYc] at h0
    · -- `↑(S∩X).card - ↑(S∩Y).card = 0` gives `S.length = 2·(S∩X).card`,
      -- even — contradicting `hlenodd`.
      omega
    · -- `↑(S∩X).card - ↑(S∩Y).card = -1` gives `↑(S∩Y).card = X.card`.
      omega
  exact ⟨hSLcard, hCY.trans hm⟩

/-- In the tight case `Y ⊆ S` (as a finset inclusion). -/
theorem Y_subset_S (hXY : Disjoint X Y) (hn : ¬ c3.HasUx2)
    (hm : X.card = Y.card) : Y ⊆ c3.S.toFinset := by
  obtain ⟨-, hCY⟩ := c3.card_facts hXY hn hm
  have hsub : c3.S.toFinset ∩ Y = Y :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right hCY.symm.le
  exact Finset.inter_eq_right.mp hsub

/-- Both `Y`-leftover colour classes are empty. -/
theorem sc_empty (hXY : Disjoint X Y) (hn : ¬ c3.HasUx2)
    (hm : X.card = Y.card) :
    (∀ w : V, w ∉ c3.sc1) ∧ (∀ w : V, w ∉ c3.sc2) := by
  have hsub := c3.Y_subset_S hXY hn hm
  constructor
  · intro w hw
    obtain ⟨h1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwY, hwS⟩ := Finset.mem_sdiff.mp h1
    exact hwS (hsub hwY)
  · intro w hw
    obtain ⟨h1, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwY, hwS⟩ := Finset.mem_sdiff.mp h1
    exact hwS (hsub hwY)

/-! ### The tight case theorem -/

theorem tight_case (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hn : ¬ c3.HasUx2) {k ℓ : ℕ} (hkl : k ≠ ℓ)
    (hX : X.card = (k + ℓ + 1) / 2) (hY : Y.card = (k + ℓ + 1) / 2) :
    BipGoal G X Y k ℓ := by
  obtain ⟨hA1, hA2⟩ := claimA_of_case3 hXY c3
  have hrodd := c3.A_length_odd hXY
  have hsodd := c3.B_length_odd hXY
  have hm : X.card = Y.card := hX.trans hY.symm
  have hL2 := c3.L2_eq_singleton hn
  obtain ⟨hsc1, hsc2⟩ := c3.sc_empty hXY hn hm
  have hm1 : 1 ≤ X.card := Finset.card_pos.mpr ⟨c3.ux, c3.hux.1⟩
  obtain ⟨hSLcard, hSYcard⟩ := c3.card_facts hXY hn hm
  have hSlen : c3.S.length = c3.A.length + c3.B.length + 1 := by
    show (c3.A ++ c3.z :: c3.B).length = c3.A.length + c3.B.length + 1
    rw [List.length_append, List.length_cons]; omega
  have hSsum : c3.SL.card + (c3.S.toFinset ∩ Y).card = c3.S.length := by
    have hnd : c3.S.Nodup := c3.hb.2.2
    have hchain : c3.S.IsChain (acrossXY X Y) := IsBipath.acrossChain c3.hb
    have hmem : ∀ a ∈ c3.S.toFinset, a ∈ X ∪ Y := fun a ha ↦
      across_chain_mem_union hXY hchain (List.mem_toFinset.mp ha) (by
        rw [hSlen]
        have := List.length_pos_of_ne_nil c3.hA
        have := List.length_pos_of_ne_nil c3.hB
        omega)
    have hdis : Disjoint (c3.S.toFinset ∩ X) (c3.S.toFinset ∩ Y) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact Disjoint.notMem_left hXY (Finset.mem_inter.mp ha).2
        (Finset.mem_inter.mp hb).2
    have hinter : (c3.S.toFinset ∩ X) ∪ (c3.S.toFinset ∩ Y) = c3.S.toFinset := by
      ext a
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro h
        rcases Finset.mem_union.mp (hmem a h) with hX' | hY'
        · exact Or.inl ⟨h, hX'⟩
        · exact Or.inr ⟨h, hY'⟩
    have hcard := Finset.card_union_of_disjoint hdis
    rw [hinter, List.toFinset_card_of_nodup hnd] at hcard
    -- hcard : S.length = (S∩X).card + (S∩Y).card
    have hSL : c3.SL = c3.S.toFinset ∩ X := Finset.filter_mem_eq_inter
    rw [hSL]
    exact hcard.symm
  -- |A| + |B| + 1 = 2m - 1
  have hcount : c3.A.length + c3.B.length + 1 = 2 * X.card - 1 := by
    rw [hSYcard] at hSsum
    omega
  by_cases hAok : k + 1 ≤ c3.A.length + 1
  · obtain ⟨p, hchp, hpl⟩ := vertPath_of_chain (by simp : c3.A ++ [c3.z] ≠ [])
      c3.S1_nodup c3.hb.1
    exact ⟨p, Or.inl ⟨hchp, by rw [hpl]; simp; omega⟩⟩
  · by_cases hBok : ℓ + 1 ≤ c3.B.length + 1
    · obtain ⟨p, hchp, hpl⟩ := vertPath_of_chain (by simp : c3.z :: c3.B ≠ [])
        c3.S2_nodup c3.hb.2.1
      exact ⟨p, Or.inr ⟨hchp, by rw [hpl]; simp; omega⟩⟩
    · -- tight arithmetic: `|A| = k - 1`, `|B| = ℓ - 1`, `k, ℓ` even, `k ≠ ℓ`
      push_neg at hAok hBok
      have hk : k + 1 = c3.A.length + 2 := by
        have := hX; omega
      have hℓ : ℓ + 1 = c3.B.length + 2 := by
        have := hX; omega
      have hkev : k % 2 = 0 := by omega
      have hℓev : ℓ % 2 = 0 := by omega
      -- eight dichotomies
      rcases Classical.em (∃ i, ∃ hi : i < c3.A.length,
          i % 2 = 0 ∧ G.Adj c3.ux c3.A[i]) with hbad | hC1
      · obtain ⟨i, hi, hpi, he⟩ := hbad
        exact c3.goal_uxA_red hXY hA1 hi hpi he (by omega)
      · push_neg at hC1
        rcases Classical.em (∃ j, ∃ hj : j < c3.B.length,
            j % 2 = 0 ∧ ¬ G.Adj c3.ux c3.B[j]) with hbad | hC2
        · obtain ⟨j, hj, hpj, he⟩ := hbad
          exact c3.goal_uxB_blue hXY hA2 hj hpj he (by omega)
        · push_neg at hC2
          rcases Classical.em (∃ i, ∃ hi : i < c3.A.length, ∃ j,
              ∃ hj : j < c3.B.length, i % 2 = 0 ∧ j % 2 = 1 ∧
              ¬ G.Adj c3.A[i] c3.B[j]) with hbad | hF1
          · obtain ⟨i, hi, j, hj, hpi, hpj, he⟩ := hbad
            exact c3.goal_crossAB_blue hXY hA2 hC1 hi hpi hj hpj
              (by omega) he (by omega)
          · push_neg at hF1
            rcases Classical.em (∃ i, ∃ hi : i < c3.A.length, ∃ j,
                ∃ hj : j < c3.B.length, i % 2 = 1 ∧ j % 2 = 0 ∧
                G.Adj c3.A[i] c3.B[j]) with hbad | hF2
            · obtain ⟨i, hi, j, hj, hpi, hpj, he⟩ := hbad
              exact c3.goal_crossAB_red hXY hA1 hC2 hi hpi hj hpj
                (by omega) he (by omega)
            · push_neg at hF2
              rcases Classical.em (∃ j, ∃ hj : j < c3.B.length,
                  j % 2 = 0 ∧ G.Adj c3.z c3.B[j]) with hbad | hzB
              · obtain ⟨j, hj, hpj, he⟩ := hbad
                exact c3.goal_zB_red hXY hC2 hj hpj he (by omega)
              · push_neg at hzB
                rcases Classical.em (∃ i, ∃ hi : i < c3.B.length, ∃ j,
                    ∃ hj : j < c3.B.length, i % 2 = 0 ∧ j % 2 = 1 ∧
                    G.Adj c3.B[i] c3.B[j]) with hbad | hEB
                · obtain ⟨i, hi, j, hj, hpi, hpj, he⟩ := hbad
                  exact c3.goal_BB_red hXY hC2 hF1 hi hpi hj hpj he (by omega)
                · push_neg at hEB
                  rcases Classical.em (∃ i, ∃ hi : i < c3.A.length,
                      i % 2 = 0 ∧ ¬ G.Adj c3.A[i] c3.z) with hbad | hEz
                  · obtain ⟨i, hi, hpi, he⟩ := hbad
                    exact c3.goal_Az_blue hXY hA2 hC1 hi hpi he (by omega)
                  · push_neg at hEz
                    rcases Classical.em (∃ i, ∃ hi : i < c3.A.length, ∃ j,
                        ∃ hj : j < c3.A.length, i % 2 = 0 ∧ j % 2 = 1 ∧
                        ¬ G.Adj c3.A[i] c3.A[j]) with hbad | hEA
                    · obtain ⟨i, hi, j, hj, hpi, hpj, he⟩ := hbad
                      exact c3.goal_AA_blue hXY hC1 hF2 hi hpi hj hpj he
                        (by omega)
                    · push_neg at hEA
                      -- All forced: assemble `InternalFacts`/`LeftoverFacts`.
                      have hEF : c3.InternalFacts := by
                        refine ⟨?_, ?_⟩
                        · intro u hu l hl
                          obtain ⟨i, hi, rfl, hpi⟩ := c3.mem_S1U hXY hu
                          rcases c3.mem_SL hXY hl with
                            ⟨j, hj, rfl, hpj⟩ | rfl | ⟨j, hj, rfl, hpj⟩
                          · exact hEA i hi j hj hpi hpj
                          · exact hEz i hi hpi
                          · exact hF1 i hi j hj hpi hpj
                        · intro u hu l hl
                          obtain ⟨j, hj, rfl, hpj⟩ := c3.mem_S2U hXY hu
                          rcases c3.mem_SL hXY hl with
                            ⟨i, hi, rfl, hpi⟩ | rfl | ⟨i, hi, rfl, hpi⟩
                          · exact fun h ↦ hF2 i hi j hj hpi hpj h.symm
                          · exact fun h ↦ hzB j hj hpj h.symm
                          · exact hEB j hj i hi hpj hpi
                      have hLF : c3.LeftoverFacts := by
                        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                        · intro w hw u hu
                          rw [hL2, Finset.mem_singleton] at hw
                          subst hw
                          obtain ⟨i, hi, rfl, hpi⟩ := c3.mem_S1U hXY hu
                          exact hC1 i hi hpi
                        · intro w hw u hu
                          rw [hL2, Finset.mem_singleton] at hw
                          subst hw
                          obtain ⟨j, hj, rfl, hpj⟩ := c3.mem_S2U hXY hu
                          exact hC2 j hj hpj
                        · intro w hw l hl
                          exact absurd hw (hsc1 w)
                        · intro w hw l hl
                          exact absurd hw (hsc2 w)
                        · intro w hw u hu
                          exact absurd hu (hsc1 u)
                        · intro w hw u hu
                          exact absurd hu (hsc2 u)
                      exact case3_finale hXY c3 hEF hLF hkl hX hY

end Case3Data

end JSP415
