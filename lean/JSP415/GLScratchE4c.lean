import JSP415.GLScratchE3

open Finset
open Classical
open scoped List

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

namespace Case3Data

/-- Claim E, forward direction, boundary sub-case `i = 0`, `j = r - 2`
(i.e. `j + 2 = r`).  If `A[0]–A[j]` were blue, the equal-length rotation
`(A[1],…,A[j-2], A[r-1] ; z ; B.reverse ++ [A[j], A[0], ux])` has midpoint
`z ∈ X` and both endpoints `A[1], ux ∈ X`, while `A[j-1] ∈ Y` is left
outside — contradicting `bipathO_leftover_opp_of_same_ends`. -/
theorem e_dir_i0r2 (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hB' : c3.ClaimB') (hC : ∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u)
    (hux2 : c3.HasUx2) {j : ℕ}
    (hj : j < c3.A.length) (hjp : j % 2 = 1)
    (hij : 5 ≤ j) (hjr : j + 2 = c3.A.length) :
    G.Adj c3.A[0] c3.A[j] := by
  by_contra hbad
  have hro : c3.A.length % 2 = 1 := c3.r_odd hXY
  have h0len : 0 < c3.A.length := by omega
  have h1 : 1 < c3.A.length := by omega
  have hjm : j - 1 < c3.A.length := by omega
  have hjm2 : j - 1 - 1 < c3.A.length := by omega
  have hrm : c3.A.length - 1 < c3.A.length := by omega
  have hB0 : 0 < c3.B.length := List.length_pos_of_ne_nil c3.hB
  have huL : c3.ux ∈ c3.L2 := (e3mem_L2 c3).mpr ⟨c3.ux_X, c3.ux_not_mem⟩
  -- sides of the vertices involved
  have hA0Y : (c3.A[0]'h0len) ∈ Y := (c3.a_side hXY 0 h0len).1.mpr (by omega)
  have hA0U : (c3.A[0]'h0len) ∈ c3.S1U := c3.a_mem_S1U hXY h0len (by omega)
  have hA1X : (c3.A[1]'h1) ∈ X := (c3.a_side hXY 1 h1).2.mpr (by omega)
  have hAjX : (c3.A[j]'hj) ∈ X := (c3.a_side hXY j hj).2.mpr hjp
  have hAjSL : (c3.A[j]'hj) ∈ c3.SL := c3.a_mem_SL hXY hj hjp
  have hAj1Y : (c3.A[j - 1]'hjm) ∈ Y := (c3.a_side hXY _ hjm).1.mpr (by omega)
  have hjmX : (c3.A[j - 1 - 1]'hjm2) ∈ X := (c3.a_side hXY _ hjm2).2.mpr (by omega)
  have hrmY : (c3.A[c3.A.length - 1]'hrm) ∈ Y :=
    (c3.a_side hXY _ hrm).1.mpr (by omega)
  have hB0Y : (c3.B[0]'hB0) ∈ Y := (c3.b_side hXY 0 hB0).1.mpr (by omega)
  -- red chain `seg A 1 (j-1) ++ [A[r-1]] ++ [z]`
  have hseg : (seg c3.A 1 (j - 1)).IsChain (Color.adjXY G X Y .red) :=
    chain_seg (chainA c3)
  have hsegne : seg c3.A 1 (j - 1) ≠ [] := seg_ne_nil (by omega) (by omega)
  have eD : G.Adj (c3.A[j - 1 - 1]'hjm2) (c3.A[c3.A.length - 1]'hrm) := by
    have h := c3.claimD_odd hXY hB' hC hux2
      (show j - 1 - 1 + 3 < c3.A.length by omega)
      (show (j - 1 - 1) % 2 = 1 by omega)
    simpa only [show j - 1 - 1 + 3 = c3.A.length - 1 by omega] using h
  have eR1 : Color.adjXY G X Y .red (c3.A[j - 1 - 1]'hjm2)
      (c3.A[c3.A.length - 1]'hrm) := redEdgeXY hjmX hrmY eD
  have e12 : ∀ x ∈ (seg c3.A 1 (j - 1)).getLast?,
      ∀ y ∈ [c3.A[c3.A.length - 1]'hrm].head?, Color.adjXY G X Y .red x y :=
    junc (getLast?_seg (by omega) (by omega)) rfl eR1
  have hgl : (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]).getLast?
      = some (c3.A[c3.A.length - 1]'hrm) := by
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rfl
  have e23 : ∀ x ∈ (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]).getLast?,
      ∀ y ∈ [c3.z].head?, Color.adjXY G X Y .red x y :=
    junc hgl rfl (edgeLastAi c3)
  have hR : ((seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]) ++ [c3.z]).IsChain
      (Color.adjXY G X Y .red) :=
    chain_app3 hseg (List.isChain_singleton _) (List.isChain_singleton _) e12 e23
  -- blue chain `z :: B.reverse ++ [A[j], A[0], ux]`
  have hBrev : c3.B.reverse.IsChain (Color.adjXY G X Y .blue) :=
    Color.adjXY.isChain_reverse (chainB c3)
  have hBrevne : c3.B.reverse ≠ [] := List.reverse_ne_nil_iff.mpr c3.hB
  have hBr_head : c3.B.reverse.head?
      = some (c3.B[c3.B.length - 1]'(by omega)) := by
    rw [List.head?_reverse, List.getLast?_eq_getLast_of_ne_nil c3.hB]
    congr 1
    exact List.getLast_eq_getElem c3.hB
  have hBr_last : c3.B.reverse.getLast? = some (c3.B[0]'hB0) := by
    rw [List.getLast?_reverse, List.head?_eq_some_head c3.hB]
    congr 1
    exact List.head_eq_getElem_zero c3.hB
  have hB'j : ¬ G.Adj (c3.A[j]'hj) (c3.B[0]'hB0) := by
    have hb' := hB' _ hAjSL (List.getElem_mem hj)
    rwa [List.head_eq_getElem_zero] at hb'
  have eb0j : Color.adjXY G X Y .blue (c3.B[0]'hB0) (c3.A[j]'hj) :=
    blueEdgeYX hB0Y hAjX (fun h ↦ hB'j h.symm)
  have ej0 : Color.adjXY G X Y .blue (c3.A[j]'hj) (c3.A[0]'h0len) :=
    ⟨Or.inl ⟨hAjX, hA0Y⟩, fun h ↦ hbad h.symm⟩
  have e0u : Color.adjXY G X Y .blue (c3.A[0]'h0len) c3.ux :=
    ⟨Or.inr ⟨hA0Y, c3.ux_X⟩, fun h ↦ hC c3.ux huL _ hA0U h.symm⟩
  have hTail : ([c3.A[j]'hj, c3.A[0]'h0len, c3.ux]).IsChain
      (Color.adjXY G X Y .blue) :=
    chain_cons (head_edge ej0) (chain_cons (head_edge e0u)
      (List.isChain_singleton _))
  have eBrev : ∀ x ∈ c3.B.reverse.getLast?,
      ∀ y ∈ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux].head?,
      Color.adjXY G X Y .blue x y := junc hBr_last rfl eb0j
  have hBl : (c3.z :: (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux])).IsChain
      (Color.adjXY G X Y .blue) :=
    chain_cons (by
      intro y hy
      rw [List.head?_append_of_ne_nil _ hBrevne, hBr_head,
        Option.mem_some_iff] at hy
      subst hy
      exact zbsBluei c3 hXY) (chain_app hBrev hTail eBrev)
  -- take/drop identities for the normal form
  have htk : c3.A.take (j - 1) = [c3.A[0]'h0len] ++ seg c3.A 1 (j - 1) := by
    have e3 : seg c3.A 0 1 = [c3.A[0]'h0len] := seg_singleton h0len
    rw [← seg_eq_take c3.A (j - 1),
      ← seg_cat (Nat.zero_le 1) (show 1 ≤ j - 1 by omega), e3]
  have hdr : c3.A.drop j = [c3.A[j]'hj, c3.A[c3.A.length - 1]'hrm] := by
    have e1 : j + 1 = c3.A.length - 1 := by omega
    have e2 : c3.A.length - 1 + 1 = c3.A.length := by omega
    rw [drop_cons_eq hj, e1, drop_cons_eq hrm, e2,
      List.drop_eq_nil_of_le (le_refl c3.A.length)]
  have htd : c3.A.take (j - 1) ++ c3.A.drop j ++ c3.z :: c3.B
      = c3.A[0]'h0len :: (seg c3.A 1 (j - 1) ++ c3.A[j]'hj ::
          c3.A[c3.A.length - 1]'hrm :: c3.z :: c3.B) := by
    rw [htk, hdr]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- permutation to the normal form
  have hperm : List.Perm
      ((seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]) ++ c3.z ::
        (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]))
      (c3.ux :: (c3.A.take (j - 1) ++ c3.A.drop j ++ c3.z :: c3.B)) := by
    calc (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]) ++ c3.z ::
            (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux])
        ~ (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]) ++ c3.z ::
            (c3.B ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]) :=
          (((List.reverse_perm _).append_right _).cons _).append_left _
      _ ~ c3.z :: ((seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]) ++
            (c3.B ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux])) := List.perm_middle
      _ ~ c3.z :: ((c3.B ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]) ++
            (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm])) :=
          List.perm_append_comm.cons _
      _ ~ c3.z :: (c3.B ++ c3.A[j]'hj :: c3.A[0]'h0len :: c3.ux ::
            (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm])) :=
          List.Perm.cons _ (List.Perm.of_eq (by
            simp only [List.append_assoc, List.cons_append, List.nil_append]))
      _ ~ (c3.A[j]'hj :: c3.A[0]'h0len :: c3.ux ::
            (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm])) ++
            c3.z :: c3.B := perm_z_to_mid
      _ ~ c3.A[j]'hj :: c3.A[0]'h0len :: c3.ux ::
            ((seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]) ++
              c3.z :: c3.B) := List.Perm.refl _
      _ ~ c3.ux :: c3.A[0]'h0len :: c3.A[j]'hj ::
            ((seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]) ++
              c3.z :: c3.B) :=
          ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _)).trans
            (List.Perm.swap _ _ _)
      _ ~ c3.ux :: c3.A[0]'h0len :: c3.A[j]'hj ::
            (seg c3.A 1 (j - 1) ++ c3.A[c3.A.length - 1]'hrm :: c3.z :: c3.B) :=
          List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _
            (List.Perm.of_eq (List.append_assoc _ _ _))))
      _ ~ c3.ux :: c3.A[0]'h0len ::
            (seg c3.A 1 (j - 1) ++ c3.A[j]'hj :: c3.A[c3.A.length - 1]'hrm ::
              c3.z :: c3.B) :=
          List.Perm.cons _ (List.Perm.cons _ List.perm_middle.symm)
      _ ~ c3.ux :: (c3.A.take (j - 1) ++ c3.A.drop j ++ c3.z :: c3.B) :=
          List.Perm.cons _ (List.Perm.of_eq htd.symm)
  have hndNF : (c3.ux :: (c3.A.take (j - 1) ++ c3.A.drop j ++
        c3.z :: c3.B)).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, nodup_NF_A c3 (j - 1) j (by omega)⟩
    intro h
    exact c3.ux_not_mem (mem_S_of_td_A c3 h)
  -- the rotated bipath and the length bookkeeping
  have hbip : IsBipath G X Y
      (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm])
      c3.z (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]) :=
    ⟨hR, hBl, hperm.nodup_iff.2 hndNF⟩
  have hlen : bipathLen c3.A c3.z c3.B = bipathLen
      (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm])
      c3.z (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]) := by
    simp only [bipathLen, List.length_append, List.length_reverse,
      List.length_cons, List.length_nil, seg_length]
    omega
  have hmax' : ∀ A'' z'' B'', IsBipathO G X Y A'' z'' B'' →
      bipathLen A'' z'' B'' ≤ bipathLen
        (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm])
        c3.z (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]) :=
    fun A'' z'' B'' h ↦ (c3.hmax A'' z'' B'' h).trans (le_of_eq hlen)
  -- nonemptiness and endpoints
  have hAne : seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm] ≠ [] :=
    fun e ↦ hsegne (List.append_eq_nil_iff.mp e).1
  have hBne : c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux] ≠ [] :=
    fun e ↦ hBrevne (List.append_eq_nil_iff.mp e).1
  have hhd : (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]).head?
      = some (c3.A[1]'h1) := by
    rw [List.head?_append_of_ne_nil _ hsegne]
    exact head?_seg (by omega) (by omega)
  have hhd' : (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]).head hAne
      = c3.A[1]'h1 :=
    Option.some.inj ((List.head?_eq_some_head hAne).symm.trans hhd)
  have haX : (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]).head hAne
      ∈ X := by
    rw [hhd']; exact hA1X
  have hgl2 : (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]).getLast?
      = some c3.ux := by
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rfl
  have hle : (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]).getLast hBne
      = c3.ux :=
    Option.some.inj ((List.getLast?_eq_getLast_of_ne_nil hBne).symm.trans hgl2)
  have hbX : (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]).getLast hBne
      ∈ X := by
    rw [hle]; exact c3.ux_X
  -- the leftover vertex `A[j-1]` lies outside the rotated bipath
  have hu : (c3.A[j - 1]'hjm) ∉
      (seg c3.A 1 (j - 1) ++ [c3.A[c3.A.length - 1]'hrm]) ++ c3.z ::
        (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]) := by
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · rcases List.mem_append.mp h with h1 | h2
      · obtain ⟨k, hk1, hk2, hk3, hke⟩ := mem_seg h1
        exact absurd (c3.a_inj hk3 hjm hke) (by omega)
      · have e := List.mem_singleton.mp h2
        exact absurd (c3.a_inj hjm hrm e) (by omega)
    · rcases List.mem_cons.mp h with e | h
      · exact c3.a_ne_z hjm e
      · rcases List.mem_append.mp h with hB | hT
        · exact c3.a_not_mem_B hjm (List.mem_reverse.mp hB)
        · rcases List.mem_cons.mp hT with e | hT
          · exact absurd (c3.a_inj hjm hj e) (by omega)
          · rcases List.mem_cons.mp hT with e | hT
            · exact absurd (c3.a_inj hjm h0len e) (by omega)
            · rcases List.mem_cons.mp hT with e | hnil
              · have hm : (c3.A[j - 1]'hjm) ∈ c3.A ++ c3.z :: c3.B :=
                  List.mem_append_left _ (List.getElem_mem hjm)
                rw [e] at hm
                exact c3.ux_not_mem hm
              · exact absurd hnil List.not_mem_nil
  exact bipathO_leftover_opp_of_same_ends hXY hbip hmax' hu c3.hz hAj1Y
    hAne hBne haX hbX

end Case3Data

end JSP415
