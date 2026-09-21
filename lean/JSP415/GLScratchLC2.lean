import JSP415.GLIface
import JSP415.GLScratchA
import JSP415.GLScratchW
import JSP415.GLScratchLC

/-!
# GLScratchLC2 — Gyárfás–Lehel Thm 3: claims B′, C, C′

`claimB'`: no `X`-side vertex of `A` is red-joined to `B.head`.  The proof
rotates `S` into the equal-length bipath
`(a_{i-1},…,a₁,z,aᵣ,…,aᵢ ; b₁ ; b₂,…,bₛ)`, which has midpoint and endpoints
in `Y` and is killed by `bipathO_kill_Ymid` when `s ≥ 2`; for `s = 1` a
direct strictly-longer bipath works by casing on the colour of `ux–b₁`.

`claimC`: a leftover `w ∈ L₂` is blue to `S₁`-uppers, via the longer bipath
`w, aᵢ,…,a₁, z, aᵣ,…,a_{i+2} ; a_{i+1} ; B`.

`claimC'`: a leftover `w ∈ L₂` is red to `S₂`-uppers, via the blue-first
bipath `w, bⱼ,…,b₁, z, bₛ,…,b_{j+2} ; b_{j+1} ; A`.
-/

open Finset

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

/-! ### Membership bookkeeping for `Case3Data` finsets -/

theorem S1U_mem {c3 : Case3Data G X Y} (hXY : Disjoint X Y) {u : V}
    (hu : u ∈ c3.S1U) : u ∈ c3.A ∧ u ∈ Y := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hu
  have h3 := List.mem_toFinset.mp h1
  rw [List.mem_append, List.mem_singleton] at h3
  rcases h3 with h | h
  · exact ⟨h, h2⟩
  · exact absurd (h ▸ h2) (Disjoint.notMem_left hXY c3.hz)

theorem S2U_mem {c3 : Case3Data G X Y} (hXY : Disjoint X Y) {u : V}
    (hu : u ∈ c3.S2U) : u ∈ c3.B ∧ u ∈ Y := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hu
  have h3 := List.mem_toFinset.mp h1
  rw [List.mem_cons] at h3
  rcases h3 with h | h
  · exact absurd (h ▸ h2) (Disjoint.notMem_left hXY c3.hz)
  · exact ⟨h, h2⟩

theorem L2_mem {c3 : Case3Data G X Y} {w : V} (hw : w ∈ c3.L2) :
    w ∈ X ∧ w ∉ c3.A ++ c3.z :: c3.B :=
  let ⟨h1, h2⟩ := Finset.mem_sdiff.mp hw
  ⟨h1, fun h ↦ h2 (List.mem_toFinset.mpr h)⟩

theorem SL_mem {c3 : Case3Data G X Y} {l : V} (hl : l ∈ c3.SL) :
    l ∈ X ∧ l ∈ c3.A ++ c3.z :: c3.B :=
  let ⟨h1, h2⟩ := Finset.mem_filter.mp hl
  ⟨h2, List.mem_toFinset.mp h1⟩

theorem SL_of_mem_A {c3 : Case3Data G X Y} {l : V} (hl : l ∈ c3.A)
    (hlX : l ∈ X) : l ∈ c3.SL :=
  Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr (List.mem_append_left _ hl), hlX⟩

theorem SL_of_mem_B {c3 : Case3Data G X Y} {l : V} (hl : l ∈ c3.B)
    (hlX : l ∈ X) : l ∈ c3.SL :=
  Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr
      (List.mem_append_right _ (List.mem_cons_of_mem _ hl)), hlX⟩

theorem S1U_head {c3 : Case3Data G X Y} : c3.A.head c3.hA ∈ c3.S1U := by
  refine Finset.mem_filter.mpr ⟨?_, c3.hhead⟩
  exact List.mem_toFinset.mpr (List.mem_append_left _ (List.head_mem c3.hA))

/-! ### Parity bookkeeping in the two monochromatic branches -/

theorem chain1_head_Y (c3 : Case3Data G X Y) {h : 0 < (c3.A ++ [c3.z]).length} :
    (c3.A ++ [c3.z])[0]'h ∈ Y := by
  have e : (c3.A ++ [c3.z])[0]'h = c3.A.head c3.hA := by
    rw [List.getElem_append_left (List.length_pos_of_ne_nil c3.hA)]
    exact (List.head_eq_getElem c3.hA).symm
  rw [e]; exact c3.hhead

theorem chain2_head_X (c3 : Case3Data G X Y) {h : 0 < (c3.z :: c3.B).length} :
    (c3.z :: c3.B)[0]'h ∈ X := by
  rw [List.getElem_cons_zero]; exact c3.hz

theorem A_mem_Y_of_even (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    {p : ℕ} (hp : p < c3.A.length) (hpar : p % 2 = 0) :
    c3.A[p]'hp ∈ Y := by
  have hl : p < (c3.A ++ [c3.z]).length := by simp; omega
  have h := adjXY_mem_Y_of_even c3.hb.1 hXY hl hpar (chain1_head_Y c3)
  rwa [List.getElem_append_left hp] at h

theorem A_mem_X_of_odd (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    {p : ℕ} (hp : p < c3.A.length) (hpar : p % 2 = 1) :
    c3.A[p]'hp ∈ X := by
  have hl : p < (c3.A ++ [c3.z]).length := by simp; omega
  have h := adjXY_mem_X_of_odd c3.hb.1 hXY hl hpar (chain1_head_Y c3)
  rwa [List.getElem_append_left hp] at h

theorem B_mem_Y_of_even (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    {q : ℕ} (hq : q < c3.B.length) (hpar : q % 2 = 0) :
    c3.B[q]'hq ∈ Y := by
  have hl : q + 1 < (c3.z :: c3.B).length := by simp; omega
  have h := adjXY_mem_Y_of_odd c3.hb.2.1 hXY hl (show (q + 1) % 2 = 1 by omega)
    (chain2_head_X c3)
  rwa [List.getElem_cons_succ] at h

theorem B_mem_X_of_odd (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    {q : ℕ} (hq : q < c3.B.length) (hpar : q % 2 = 1) :
    c3.B[q]'hq ∈ X := by
  have hl : q + 1 < (c3.z :: c3.B).length := by simp; omega
  have h := adjXY_mem_X_of_even c3.hb.2.1 hXY hl (show (q + 1) % 2 = 0 by omega)
    (chain2_head_X c3)
  rwa [List.getElem_cons_succ] at h

theorem A_even_of_mem_Y (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    {p : ℕ} (hp : p < c3.A.length) (h : c3.A[p]'hp ∈ Y) : p % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one p with hpar | hpar
  · exact hpar
  · exact absurd h (Disjoint.notMem_left hXY (A_mem_X_of_odd hXY c3 hp hpar))

theorem A_odd_of_mem_X (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    {p : ℕ} (hp : p < c3.A.length) (h : c3.A[p]'hp ∈ X) : p % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one p with hpar | hpar
  · exact absurd h (Disjoint.notMem_right hXY (A_mem_Y_of_even hXY c3 hp hpar))
  · exact hpar

theorem B_even_of_mem_Y (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    {q : ℕ} (hq : q < c3.B.length) (h : c3.B[q]'hq ∈ Y) : q % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar
  · exact hpar
  · exact absurd h (Disjoint.notMem_left hXY (B_mem_X_of_odd hXY c3 hq hpar))

theorem B_head_mem_Y (hXY : Disjoint X Y) (c3 : Case3Data G X Y) :
    c3.B.head c3.hB ∈ Y := by
  have hp : 0 < c3.B.length := List.length_pos_of_ne_nil c3.hB
  have e : c3.B[0]'hp = c3.B.head c3.hB := (List.head_eq_getElem c3.hB).symm
  rw [← e]
  exact B_mem_Y_of_even hXY c3 hp (by omega)

/-! ### Claim B′ -/

theorem claimB' (hXY : Disjoint X Y) (c3 : Case3Data G X Y) : c3.ClaimB' := by
  intro l hlSL hlA hadj
  obtain ⟨hlX, -⟩ := SL_mem hlSL
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hlA
  -- l = `A[p]`; `p` is odd since `A[p] ∈ X`.
  have hpar : p % 2 = 1 := A_odd_of_mem_X hXY c3 hp hlX
  have hb1Y : c3.B.head c3.hB ∈ Y := B_head_mem_Y hXY c3
  obtain ⟨hAz, -⟩ := claimA_of_case3 hXY c3
  have harz := IsBipath.red_last_edge c3.hb c3.hA
  have hzb1 := IsBipath.blue_first_edge c3.hb c3.hB
  have hredA : c3.A.IsChain (Color.adjXY G X Y .red) := c3.hb.1.left_of_append
  have hblueB : c3.B.IsChain (Color.adjXY G X Y .blue) := c3.hb.2.1.tail
  have hnd := c3.hb.2.2
  -- pieces of the rotated red branch
  have hT1 : (c3.A.take p).reverse.IsChain (Color.adjXY G X Y .red) :=
    Color.adjXY.isChain_reverse (isChain_take_of p hredA)
  have hT2 : (c3.A.drop p).reverse.IsChain (Color.adjXY G X Y .red) :=
    Color.adjXY.isChain_reverse (isChain_drop_of p hredA)
  have hT1ne : (c3.A.take p).reverse ≠ [] := by
    rw [List.reverse_ne_nil_iff, List.ne_nil_iff_length_pos, List.length_take]
    omega
  have hT2ne : (c3.A.drop p).reverse ≠ [] := by
    rw [List.reverse_ne_nil_iff, List.ne_nil_iff_length_pos, List.length_drop]
    omega
  have hT1last : (c3.A.take p).reverse.getLast? = some (c3.A.head c3.hA) := by
    rw [List.getLast?_reverse, head?_take (by omega) (Nat.le_of_lt hp),
      List.head?_eq_some_head c3.hA]
  have hT2head : (c3.A.drop p).reverse.head? =
      some (c3.A.getLast c3.hA) := by
    rw [List.head?_reverse, getLast?_drop hp]
    congr 1
    exact (List.getLast_eq_getElem c3.hA).symm
  have hT2last : (c3.A.drop p).reverse.getLast? = some (c3.A[p]'hp) := by
    rw [List.getLast?_reverse, head?_drop hp]
  -- the rotated red chain `aₚ,…,a₁, z, aᵣ,…,a_{p+1}, b₁`
  have hA' : (((c3.A.take p).reverse ++ c3.z :: (c3.A.drop p).reverse) ++
      [c3.B.head c3.hB]).IsChain (Color.adjXY G X Y .red) := by
    rw [List.append_assoc]
    refine List.isChain_append.mpr ⟨hT1, ?_, ?_⟩
    · rw [List.cons_append]
      refine List.isChain_cons.mpr ⟨?_, ?_⟩
      · intro y hy
        rw [List.head?_append_of_ne_nil _ hT2ne, hT2head,
          Option.mem_some_iff] at hy
        subst hy
        exact Color.adjXY.symm harz
      · refine List.isChain_append.mpr ⟨hT2, List.isChain_singleton _, ?_⟩
        intro x hx y hy
        rw [hT2last, Option.mem_some_iff] at hx
        rw [List.head?_singleton, Option.mem_some_iff] at hy
        subst hx; subst hy
        exact ⟨Or.inl ⟨hlX, hb1Y⟩, hadj⟩
    · intro x hx y hy
      rw [hT1last, Option.mem_some_iff] at hx
      rw [List.head?_append_of_ne_nil _ (List.cons_ne_nil _ _),
        List.head?_cons, Option.mem_some_iff] at hy
      subst hx; subst hy
      exact hAz
  -- vertex-list permutation (for nodup and the leftover)
  have hperm : List.Perm
      (((c3.A.take p).reverse ++ c3.z :: (c3.A.drop p).reverse) ++
        c3.B.head c3.hB :: c3.B.tail)
      (c3.A ++ c3.z :: c3.B) := by
    have h := perm_rot_vertex2 (z := c3.z) (m := c3.B.head c3.hB)
      (P := c3.A.take p) (Q := c3.A.drop p) (R := c3.B.tail)
    rw [List.take_append_drop] at h
    have e : c3.A ++ c3.z :: c3.B.head c3.hB :: c3.B.tail =
        c3.A ++ c3.z :: c3.B := by
      rw [List.cons_head_tail c3.hB]
    rwa [e] at h
  by_cases hBt : c3.B.tail = []
  · -- `s = 1`: `B = [b₁]`; case on the colour of `ux–b₁`.
    have hBsing : c3.B = [c3.B.head c3.hB] := by
      have h := List.cons_head_tail c3.hB
      rw [hBt] at h
      exact h.symm
    have hBlen : c3.B.length = 1 := by rw [hBsing]; rfl
    have hndS : (c3.ux :: c3.A ++ c3.z :: c3.B).Nodup :=
      List.nodup_cons.mpr ⟨c3.hux.2, hnd⟩
    -- the strictly-longer extension `(A, z, B ++ [ux])` in the blue case
    have hp2 : List.Perm (c3.A ++ c3.z :: (c3.B ++ [c3.ux]))
        (c3.ux :: c3.A ++ c3.z :: c3.B) :=
      (List.perm_middle (l₁ := c3.A) (l₂ := c3.B ++ [c3.ux]) (a := c3.z)).trans <|
        ((List.Perm.of_eq
          (List.append_assoc c3.A c3.B [c3.ux]).symm).cons c3.z).trans <|
          (List.perm_append_comm.cons c3.z).trans <|
            (List.Perm.swap c3.ux c3.z _).trans
              ((List.perm_middle (l₁ := c3.A) (l₂ := c3.B) (a := c3.z)).symm.cons
                c3.ux)
    by_cases huxb : G.Adj c3.ux (c3.B.head c3.hB)
    · -- `ux–b₁` red: bipath `(A' ++ [b₁], ux, [])`
      have hbp : IsBipath G X Y
          (((c3.A.take p).reverse ++ c3.z :: (c3.A.drop p).reverse) ++
            [c3.B.head c3.hB]) c3.ux [] := by
        refine ⟨?_, List.isChain_singleton _, ?_⟩
        · refine List.isChain_append.mpr ⟨hA', List.isChain_singleton _, ?_⟩
          intro x hx y hy
          rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
            List.getLast?_singleton, Option.mem_some_iff] at hx
          rw [List.head?_singleton, Option.mem_some_iff] at hy
          subst hx; subst hy
          exact ⟨Or.inr ⟨hb1Y, c3.hux.1⟩, huxb.symm⟩
        · have hperm2 : List.Perm
              ((((c3.A.take p).reverse ++ c3.z :: (c3.A.drop p).reverse) ++
                [c3.B.head c3.hB]) ++ [c3.ux])
              (c3.ux :: c3.A ++ c3.z :: c3.B) := by
            rw [hBt] at hperm
            refine (hperm.append_right [c3.ux]).trans ?_
            exact List.perm_middle.trans
              ((List.Perm.of_eq (List.append_nil _)).cons c3.ux)
          exact hperm2.nodup_iff.mpr hndS
      have hbnd := c3.hmax _ _ _ (Or.inl hbp)
      simp only [bipathLen, List.length_append, List.length_cons,
        List.length_nil, List.length_reverse, List.length_take,
        List.length_drop, Nat.min_eq_left (Nat.le_of_lt hp)] at hbnd
      rw [hBlen] at hbnd
      omega
    · -- `ux–b₁` blue: bipath `(A, z, B ++ [ux])`
      have heq : c3.B.getLast c3.hB = c3.B.head c3.hB := by
        have e1 : c3.B.getLast? = some (c3.B.head c3.hB) := by
          conv_lhs => rw [← List.cons_head_tail c3.hB]
          rw [hBt, List.getLast?_singleton]
        exact Option.some.inj
          ((List.getLast?_eq_getLast_of_ne_nil c3.hB).symm.trans e1)
      have hbp : IsBipath G X Y c3.A c3.z (c3.B ++ [c3.ux]) := by
        refine ⟨c3.hb.1, ?_, ?_⟩
        · refine List.isChain_cons.mpr ⟨?_, ?_⟩
          · intro y hy
            rw [List.head?_append_of_ne_nil _ c3.hB,
              List.head?_eq_some_head c3.hB, Option.mem_some_iff] at hy
            subst hy; exact hzb1
          · refine List.isChain_append.mpr
              ⟨hblueB, List.isChain_singleton _, ?_⟩
            intro x hx y hy
            rw [List.getLast?_eq_getLast_of_ne_nil c3.hB,
              Option.mem_some_iff] at hx
            rw [List.head?_singleton, Option.mem_some_iff] at hy
            subst hx; subst hy
            exact ⟨Or.inr ⟨c3.hlast, c3.hux.1⟩,
              fun hb ↦ huxb (heq ▸ hb.symm)⟩
        · exact hp2.nodup_iff.mpr hndS
      have hbnd := c3.hmax _ _ _ (Or.inl hbp)
      simp only [bipathLen, List.length_append, List.length_cons,
        List.length_nil] at hbnd
      omega
  · -- `s ≥ 2`: the rotation `S'` is an equal-length maximal bipath with
    -- midpoint `b₁ ∈ Y` and endpoints in `Y` — killed.
    have hBt' : c3.B.tail ≠ [] := hBt
    have hnd' : (((c3.A.take p).reverse ++ c3.z :: (c3.A.drop p).reverse) ++
        c3.B.head c3.hB :: c3.B.tail).Nodup := hperm.nodup_iff.mpr hnd
    have hblue' : (c3.B.head c3.hB :: c3.B.tail).IsChain
        (Color.adjXY G X Y .blue) := by
      rw [List.cons_head_tail c3.hB]; exact hblueB
    have hbS' : IsBipath G X Y
        ((c3.A.take p).reverse ++ c3.z :: (c3.A.drop p).reverse)
        (c3.B.head c3.hB) c3.B.tail := ⟨hA', hblue', hnd'⟩
    have hA'ne : ((c3.A.take p).reverse ++ c3.z :: (c3.A.drop p).reverse) ≠ [] :=
      fun h ↦ absurd (List.append_eq_nil_iff.mp h).1 hT1ne
    have hA'hd : ((c3.A.take p).reverse ++ c3.z :: (c3.A.drop p).reverse).head
        hA'ne = c3.A[p - 1]'(by omega) := by
      have e : ((c3.A.take p).reverse ++ c3.z :: (c3.A.drop p).reverse).head? =
          some (c3.A[p - 1]'(by omega)) := by
        rw [List.head?_append_of_ne_nil _ hT1ne, List.head?_reverse,
          getLast?_take (by omega) (Nat.le_of_lt hp)]
      have e2 := List.head?_eq_some_head hA'ne
      rw [e] at e2
      exact (Option.some.inj e2).symm
    have hend1 : ((c3.A.take p).reverse ++ c3.z :: (c3.A.drop p).reverse).head
        hA'ne ∈ Y := by
      rw [hA'hd]
      exact A_mem_Y_of_even hXY c3 (by omega) (by omega)
    have hend2 : c3.B.tail.getLast hBt' ∈ Y := by
      rw [List.getLast_tail hBt']; exact c3.hlast
    have hs2 : 2 ≤ c3.B.length := by
      have := List.length_pos_of_ne_nil hBt'
      rw [List.length_tail] at this; omega
    have hlen : bipathLen
        ((c3.A.take p).reverse ++ c3.z :: (c3.A.drop p).reverse)
        (c3.B.head c3.hB) c3.B.tail = bipathLen c3.A c3.z c3.B := by
      rw [bipathLen, bipathLen]
      simp only [List.length_append, List.length_cons, List.length_reverse,
        List.length_take, List.length_drop, List.length_tail,
        Nat.min_eq_left (Nat.le_of_lt hp)]
      omega
    have hmax' := hlen.symm ▸ c3.hmax
    exact bipathO_kill_Ymid hXY hbS' hmax'
      (fun hm ↦ c3.hux.2 (hperm.mem_iff.mp hm)) hb1Y c3.hux.1 hA'ne hBt'
      hend1 hend2

/-! ### Claim C -/

theorem claimC (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    (hB' : c3.ClaimB') :
    ∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u := by
  intro w hw u hu hadj
  obtain ⟨hwX, hwS⟩ := L2_mem hw
  obtain ⟨huA, huY⟩ := S1U_mem hXY hu
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp huA
  have hpar : p % 2 = 0 := A_even_of_mem_Y hXY c3 hp huY
  obtain ⟨hAz, -⟩ := claimA_of_case3 hXY c3
  have harz := IsBipath.red_last_edge c3.hb c3.hA
  have hredA : c3.A.IsChain (Color.adjXY G X Y .red) := c3.hb.1.left_of_append
  have hblueB : c3.B.IsChain (Color.adjXY G X Y .blue) := c3.hb.2.1.tail
  have hnd := c3.hb.2.2
  have hndS : (w :: c3.A ++ c3.z :: c3.B).Nodup :=
    List.nodup_cons.mpr ⟨hwS, hnd⟩
  have hwu : Color.adjXY G X Y .red w (c3.A[p]'hp) :=
    ⟨Or.inl ⟨hwX, huY⟩, hadj⟩
  rcases Nat.lt_or_ge (p + 1) c3.A.length with hlt | hge
  · -- `p + 1 < r`: bipath `(w :: (take p+1 A).reverse ++ z :: (drop p+1 A).tail.reverse, A[p+1], B)`
    have hQ : c3.A.drop (p + 1) ≠ [] := by
      rw [List.ne_nil_iff_length_pos, List.length_drop]; omega
    have hPre : (c3.A.take (p + 1)).reverse ≠ [] := by
      rw [List.reverse_ne_nil_iff, List.ne_nil_iff_length_pos,
        List.length_take]; omega
    have hPgetLast : (c3.A.take (p + 1)).reverse.head? =
        some (c3.A[(p + 1) - 1]'(by omega)) := by
      rw [List.head?_reverse, getLast?_take (by omega) (by omega)]
    have hPlast : (c3.A.take (p + 1)).reverse.getLast? =
        some (c3.A.head c3.hA) := by
      rw [List.getLast?_reverse, head?_take (by omega) (by omega),
        List.head?_eq_some_head c3.hA]
    have hQhead : (c3.A.drop (p + 1)).reverse.head? =
        some (c3.A.getLast c3.hA) := by
      rw [List.head?_reverse, getLast?_drop hlt]
      congr 1
      exact (List.getLast_eq_getElem c3.hA).symm
    have hchainR : ((w :: (c3.A.take (p + 1)).reverse ++
        c3.z :: (c3.A.drop (p + 1)).tail.reverse) ++
        [(c3.A.drop (p + 1)).head hQ]).IsChain
        (Color.adjXY G X Y .red) := by
      rw [rot_chain_eq hQ, List.cons_append]
      refine List.isChain_cons.mpr ⟨?_, ?_⟩
      · intro y hy
        rw [List.head?_append_of_ne_nil _ hPre, hPgetLast,
          Option.mem_some_iff] at hy
        subst hy; exact hwu
      · refine List.isChain_append.mpr ⟨?_, ?_, ?_⟩
        · exact Color.adjXY.isChain_reverse (isChain_take_of _ hredA)
        · refine List.isChain_cons.mpr ⟨?_, ?_⟩
          · intro y hy
            rw [hQhead, Option.mem_some_iff] at hy
            subst hy
            exact Color.adjXY.symm harz
          · exact Color.adjXY.isChain_reverse (isChain_drop_of _ hredA)
        · intro x hx y hy
          rw [hPlast, Option.mem_some_iff] at hx
          rw [List.head?_cons, Option.mem_some_iff] at hy
          subst hx; subst hy; exact hAz
    -- the `a_{p+1}–b₁` junction is blue by claim B′
    have hb1Y : c3.B.head c3.hB ∈ Y := B_head_mem_Y hXY c3
    have hAmid : c3.A[p + 1]'hlt ∈ X :=
      A_mem_X_of_odd hXY c3 hlt (by omega)
    have hB'edge : ¬ G.Adj (c3.A[p + 1]'hlt) (c3.B.head c3.hB) :=
      hB' _ (SL_of_mem_A (List.getElem_mem hlt) hAmid)
        (List.getElem_mem hlt)
    have hchainB : ((c3.A.drop (p + 1)).head hQ :: c3.B).IsChain
        (Color.adjXY G X Y .blue) := by
      refine List.isChain_cons.mpr ⟨?_, hblueB⟩
      intro y hy
      rw [List.head?_eq_some_head c3.hB, Option.mem_some_iff] at hy
      subst hy
      have he : (c3.A.drop (p + 1)).head hQ = c3.A[p + 1]'hlt :=
        List.head_drop hQ
      rw [he]
      exact ⟨Or.inl ⟨hAmid, hb1Y⟩, hB'edge⟩
    have hperm : List.Perm
        ((w :: (c3.A.take (p + 1)).reverse ++ c3.z ::
          (c3.A.drop (p + 1)).tail.reverse) ++
          (c3.A.drop (p + 1)).head hQ :: c3.B)
        (w :: c3.A ++ c3.z :: c3.B) := by
      have h := perm_rot_vertex hQ (w := w) (z := c3.z)
        (P := c3.A.take (p + 1)) (Q := c3.A.drop (p + 1)) (R := c3.B)
      rwa [List.take_append_drop] at h
    have hnd' := hperm.nodup_iff.mpr hndS
    have hbp : IsBipath G X Y
        (w :: (c3.A.take (p + 1)).reverse ++ c3.z ::
          (c3.A.drop (p + 1)).tail.reverse)
        ((c3.A.drop (p + 1)).head hQ) c3.B := ⟨hchainR, hchainB, hnd'⟩
    have hbnd := c3.hmax _ _ _ (Or.inl hbp)
    simp only [bipathLen, List.length_append, List.length_cons,
      List.length_reverse, List.length_take, List.length_drop,
      List.length_tail,
      Nat.min_eq_left (show p + 1 ≤ c3.A.length by omega)] at hbnd
    omega
  · -- `p + 1 = r`: bipath `(w :: A.reverse, z, B)`
    have hpr : p + 1 = c3.A.length := by omega
    have hp' : p = c3.A.length - 1 := by omega
    subst hp'
    have hArev : c3.A.reverse.IsChain (Color.adjXY G X Y .red) :=
      Color.adjXY.isChain_reverse hredA
    have hArevNe : c3.A.reverse ≠ [] := List.reverse_ne_nil_iff.mpr c3.hA
    have hbp : IsBipath G X Y (w :: c3.A.reverse) c3.z c3.B := by
      refine ⟨?_, c3.hb.2.1, ?_⟩
      · rw [List.cons_append]
        refine List.isChain_cons.mpr ⟨?_, ?_⟩
        · intro y hy
          rw [List.head?_append_of_ne_nil _ hArevNe, List.head?_reverse,
            List.getLast?_eq_getLast_of_ne_nil c3.hA,
            Option.mem_some_iff] at hy
          subst hy
          rw [List.getLast_eq_getElem]; exact hwu
        · refine List.isChain_append.mpr
            ⟨hArev, List.isChain_singleton _, ?_⟩
          intro x hx y hy
          rw [List.getLast?_reverse, List.head?_eq_some_head c3.hA,
            Option.mem_some_iff] at hx
          rw [List.head?_singleton, Option.mem_some_iff] at hy
          subst hx; subst hy; exact hAz
      · have hperm : List.Perm (w :: c3.A.reverse ++ c3.z :: c3.B)
            (w :: c3.A ++ c3.z :: c3.B) :=
          ((List.reverse_perm c3.A).append_right _).cons w
        exact hperm.nodup_iff.mpr hndS
    have hbnd := c3.hmax _ _ _ (Or.inl hbp)
    simp only [bipathLen, List.length_cons, List.length_reverse] at hbnd
    omega

/-! ### Claim C′ -/

theorem claimC' (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    (hB2 : ∀ l ∈ c3.SL, l ∈ c3.B → G.Adj (c3.A.head c3.hA) l) :
    ∀ w ∈ c3.L2, ∀ u ∈ c3.S2U, G.Adj w u := by
  intro w hw u hu
  obtain ⟨hwX, hwS⟩ := L2_mem hw
  obtain ⟨huB, huY⟩ := S2U_mem hXY hu
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp huB
  have hpar : q % 2 = 0 := B_even_of_mem_Y hXY c3 hq huY
  obtain ⟨hAz, hzbs⟩ := claimA_of_case3 hXY c3
  have hzb1 := IsBipath.blue_first_edge c3.hb c3.hB
  have hredA : c3.A.IsChain (Color.adjXY G X Y .red) := c3.hb.1.left_of_append
  have hblueB : c3.B.IsChain (Color.adjXY G X Y .blue) := c3.hb.2.1.tail
  have hnd := c3.hb.2.2
  have hndS : (w :: c3.A ++ c3.z :: c3.B).Nodup :=
    List.nodup_cons.mpr ⟨hwS, hnd⟩
  by_contra hnadj
  have hwu : Color.adjXY G X Y .blue w (c3.B[q]'hq) :=
    ⟨Or.inl ⟨hwX, huY⟩, hnadj⟩
  rcases Nat.lt_or_ge (q + 1) c3.B.length with hlt | hge
  · -- `q + 1 < s`: blue-first bipath with mid `b_{q+1}`, tail `A`
    have hQ : c3.B.drop (q + 1) ≠ [] := by
      rw [List.ne_nil_iff_length_pos, List.length_drop]; omega
    have hPre : (c3.B.take (q + 1)).reverse ≠ [] := by
      rw [List.reverse_ne_nil_iff, List.ne_nil_iff_length_pos,
        List.length_take]; omega
    have hPgetLast : (c3.B.take (q + 1)).reverse.head? =
        some (c3.B[(q + 1) - 1]'(by omega)) := by
      rw [List.head?_reverse, getLast?_take (by omega) (by omega)]
    have hPlast : (c3.B.take (q + 1)).reverse.getLast? =
        some (c3.B.head c3.hB) := by
      rw [List.getLast?_reverse, head?_take (by omega) (by omega),
        List.head?_eq_some_head c3.hB]
    have hQhead : (c3.B.drop (q + 1)).reverse.head? =
        some (c3.B.getLast c3.hB) := by
      rw [List.head?_reverse, getLast?_drop hlt]
      congr 1
      exact (List.getLast_eq_getElem c3.hB).symm
    have hchainBl : ((w :: (c3.B.take (q + 1)).reverse ++
        c3.z :: (c3.B.drop (q + 1)).tail.reverse) ++
        [(c3.B.drop (q + 1)).head hQ]).IsChain
        (Color.adjXY G X Y .blue) := by
      rw [rot_chain_eq hQ, List.cons_append]
      refine List.isChain_cons.mpr ⟨?_, ?_⟩
      · intro y hy
        rw [List.head?_append_of_ne_nil _ hPre, hPgetLast,
          Option.mem_some_iff] at hy
        subst hy; exact hwu
      · refine List.isChain_append.mpr ⟨?_, ?_, ?_⟩
        · exact Color.adjXY.isChain_reverse (isChain_take_of _ hblueB)
        · refine List.isChain_cons.mpr ⟨?_, ?_⟩
          · intro y hy
            rw [hQhead, Option.mem_some_iff] at hy
            subst hy
            exact hzbs
          · exact Color.adjXY.isChain_reverse (isChain_drop_of _ hblueB)
        · intro x hx y hy
          rw [hPlast, Option.mem_some_iff] at hx
          rw [List.head?_cons, Option.mem_some_iff] at hy
          subst hx; subst hy
          exact Color.adjXY.symm hzb1
    -- the `b_{q+1}–a₁` junction is red by `hF1`
    have hBmid : c3.B[q + 1]'hlt ∈ X :=
      B_mem_X_of_odd hXY c3 hlt (by omega)
    have hchainR : ((c3.B.drop (q + 1)).head hQ :: c3.A).IsChain
        (Color.adjXY G X Y .red) := by
      refine List.isChain_cons.mpr ⟨?_, hredA⟩
      intro y hy
      rw [List.head?_eq_some_head c3.hA, Option.mem_some_iff] at hy
      subst hy
      have he : (c3.B.drop (q + 1)).head hQ = c3.B[q + 1]'hlt :=
        List.head_drop hQ
      rw [he]
      exact ⟨Or.inl ⟨hBmid, c3.hhead⟩,
        (hB2 _ (SL_of_mem_B (List.getElem_mem hlt) hBmid)
          (List.getElem_mem hlt)).symm⟩
    have hperm : List.Perm
        ((w :: (c3.B.take (q + 1)).reverse ++ c3.z ::
          (c3.B.drop (q + 1)).tail.reverse) ++
          (c3.B.drop (q + 1)).head hQ :: c3.A)
        (w :: c3.A ++ c3.z :: c3.B) := by
      have h := perm_rot_vertex hQ (w := w) (z := c3.z)
        (P := c3.B.take (q + 1)) (Q := c3.B.drop (q + 1)) (R := c3.A)
      rw [List.take_append_drop] at h
      refine h.trans ?_
      exact ((List.perm_middle (a := c3.z) (l₁ := c3.B) (l₂ := c3.A)).cons
        w).trans
        ((((List.perm_append_comm (l₁ := c3.B) (l₂ := c3.A)).cons c3.z).cons
          w).trans
          (((List.perm_middle (a := c3.z) (l₁ := c3.A) (l₂ := c3.B)).cons
            w).symm))
    have hnd' := hperm.nodup_iff.mpr hndS
    have hbp : IsBipathB G X Y
        (w :: (c3.B.take (q + 1)).reverse ++ c3.z ::
          (c3.B.drop (q + 1)).tail.reverse)
        ((c3.B.drop (q + 1)).head hQ) c3.A := ⟨hchainBl, hchainR, hnd'⟩
    have hbnd := c3.hmax _ _ _ (Or.inr hbp)
    simp only [bipathLen, List.length_append, List.length_cons,
      List.length_reverse, List.length_take, List.length_drop,
      List.length_tail,
      Nat.min_eq_left (show q + 1 ≤ c3.B.length by omega)] at hbnd
    omega
  · -- `q + 1 = s`: blue-first bipath `(w :: B.reverse, z, A)`
    have hqr : q + 1 = c3.B.length := by omega
    have hq' : q = c3.B.length - 1 := by omega
    subst hq'
    have hBrev : c3.B.reverse.IsChain (Color.adjXY G X Y .blue) :=
      Color.adjXY.isChain_reverse hblueB
    have hBrevNe : c3.B.reverse ≠ [] := List.reverse_ne_nil_iff.mpr c3.hB
    have hbp : IsBipathB G X Y (w :: c3.B.reverse) c3.z c3.A := by
      refine ⟨?_, ?_, ?_⟩
      · rw [List.cons_append]
        refine List.isChain_cons.mpr ⟨?_, ?_⟩
        · intro y hy
          rw [List.head?_append_of_ne_nil _ hBrevNe, List.head?_reverse,
            List.getLast?_eq_getLast_of_ne_nil c3.hB,
            Option.mem_some_iff] at hy
          subst hy
          rw [List.getLast_eq_getElem]; exact hwu
        · refine List.isChain_append.mpr
            ⟨hBrev, List.isChain_singleton _, ?_⟩
          intro x hx y hy
          rw [List.getLast?_reverse, List.head?_eq_some_head c3.hB,
            Option.mem_some_iff] at hx
          rw [List.head?_singleton, Option.mem_some_iff] at hy
          subst hx; subst hy
          exact Color.adjXY.symm hzb1
      · refine List.isChain_cons.mpr ⟨?_, hredA⟩
        intro y hy
        rw [List.head?_eq_some_head c3.hA, Option.mem_some_iff] at hy
        subst hy
        exact Color.adjXY.symm hAz
      · have hperm : List.Perm (w :: c3.B.reverse ++ c3.z :: c3.A)
            (w :: c3.A ++ c3.z :: c3.B) := by
          refine ((List.perm_middle (a := c3.z) (l₁ := c3.B.reverse)
            (l₂ := c3.A)).cons w).trans ?_
          refine (((List.reverse_perm c3.B).append_right c3.A).cons c3.z
            |>.cons w).trans ?_
          exact ((List.perm_append_comm (l₁ := c3.B) (l₂ := c3.A)).cons
            c3.z |>.cons w).trans
            (((List.perm_middle (a := c3.z) (l₁ := c3.A) (l₂ := c3.B)).cons
              w).symm)
        exact hperm.nodup_iff.mpr hndS
    have hbnd := c3.hmax _ _ _ (Or.inr hbp)
    simp only [bipathLen, List.length_append, List.length_cons,
      List.length_reverse] at hbnd
    omega

end JSP415
