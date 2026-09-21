import JSP415.GLScratchE3

open Finset
open Classical
open scoped List

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

namespace Case3Data

/-- Claim E, forward direction with `i ≥ 2`: if `A[i]–A[j]` were blue
(`i` even, `j` odd, `i + 5 ≤ j`), the rotated bipath
`(A[j+1],…,A[r-1], z, A[0],…,A[i-1], A[i+2],…,A[j-2] ; A[j-1] ;
ux, A[i], A[j], B)` is an equal-length bipath of the killed
`Y`-midpoint type (leftover `A[i+1] ∈ X`, endpoints `A[j+1]`,
`B.getLast ∈ Y`). -/
theorem e_dir_main (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hB' : c3.ClaimB') (hC : ∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u)
    (hux2 : c3.HasUx2) {i j : ℕ}
    (hi : i < c3.A.length) (hpar : i % 2 = 0)
    (hj : j < c3.A.length) (hjp : j % 2 = 1)
    (hij : i + 5 ≤ j) (hi2 : 2 ≤ i) :
    G.Adj c3.A[i] c3.A[j] := by
  by_contra hbad
  have hro : c3.A.length % 2 = 1 := c3.r_odd hXY
  have hjr : j + 1 < c3.A.length := by omega
  have hlt : i + 1 < c3.A.length := by omega
  have hjm1 : j - 1 < c3.A.length := by omega
  have huL : c3.ux ∈ c3.L2 := (e3mem_L2 c3).mpr ⟨c3.ux_X, c3.ux_not_mem⟩
  -- side / finset facts
  have hAiY : (c3.A[i]'hi) ∈ Y := (c3.a_side hXY i hi).1.mpr hpar
  have hAiU : (c3.A[i]'hi) ∈ c3.S1U := c3.a_mem_S1U hXY hi hpar
  have hAjX : (c3.A[j]'hj) ∈ X := (c3.a_side hXY j hj).2.mpr hjp
  have hAjL : (c3.A[j]'hj) ∈ c3.SL := c3.a_mem_SL hXY hj hjp
  have hAj1Y : (c3.A[j - 1]'hjm1) ∈ Y :=
    (c3.a_side hXY _ hjm1).1.mpr (by omega)
  have hAj1U : (c3.A[j - 1]'hjm1) ∈ c3.S1U :=
    c3.a_mem_S1U hXY hjm1 (by omega)
  have hupX : (c3.A[i + 1]'hlt) ∈ X :=
    (c3.a_side hXY _ hlt).2.mpr (by omega)
  -- the five red pieces
  have hS4 : (seg c3.A (j + 1) c3.A.length).IsChain
      (Color.adjXY G X Y .red) := chain_seg (chainA c3)
  have hZ : [c3.z].IsChain (Color.adjXY G X Y .red) :=
    List.isChain_singleton _
  have hS1 : (seg c3.A 0 i).IsChain (Color.adjXY G X Y .red) :=
    chain_seg (chainA c3)
  have hS2 : (seg c3.A (i + 2) (j - 1)).IsChain
      (Color.adjXY G X Y .red) := chain_seg (chainA c3)
  have hM : [c3.A[j - 1]'hjm1].IsChain (Color.adjXY G X Y .red) :=
    List.isChain_singleton _
  have hS4ne : seg c3.A (j + 1) c3.A.length ≠ [] :=
    seg_ne_nil hjr (le_refl _)
  have hS1ne : seg c3.A 0 i ≠ [] := seg_ne_nil (by omega) (by omega)
  have hS2ne : seg c3.A (i + 2) (j - 1) ≠ [] :=
    seg_ne_nil (by omega) (by omega)
  -- the long-range junction edges
  have eD : G.Adj (c3.A[i - 1]'(by omega)) (c3.A[i + 2]'(by omega)) := by
    have h := c3.claimD_odd hXY hB' hC hux2
      (show i - 1 + 3 < c3.A.length by omega)
      (show (i - 1) % 2 = 1 by omega)
    simpa only [show i - 1 + 3 = i + 2 by omega] using h
  have eDred : Color.adjXY G X Y .red (c3.A[i - 1]'(by omega))
      (c3.A[i + 2]'(by omega)) :=
    redEdgeXY ((c3.a_side hXY (i - 1) (by omega)).2.mpr (by omega))
      ((c3.a_side hXY (i + 2) (by omega)).1.mpr (by omega)) eD
  have e45e : Color.adjXY G X Y .red (c3.A[j - 2]'(by omega))
      (c3.A[j - 1]'hjm1) := by
    have h := edgeA c3 (j - 2) (show j - 2 + 1 < c3.A.length by omega)
    simpa only [show j - 2 + 1 = j - 1 by omega] using h
  -- getLast? / head? equations for the junctions
  have hglZ : (seg c3.A (j + 1) c3.A.length ++ [c3.z]).getLast?
      = some c3.z :=
    (List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)).trans
      List.getLast?_singleton
  have hglS1 : (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++
      seg c3.A 0 i).getLast? = some (c3.A[i - 1]'(by omega)) :=
    (List.getLast?_append_of_ne_nil _ hS1ne).trans
      (getLast?_seg (by omega) (by omega))
  have hglS2 : (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
        seg c3.A (i + 2) (j - 1)).getLast?
      = some (c3.A[j - 2]'(by omega)) :=
    (List.getLast?_append_of_ne_nil _ hS2ne).trans
      (getLast?_seg (by omega) (by omega))
  have e12 : ∀ x ∈ (seg c3.A (j + 1) c3.A.length).getLast?,
      ∀ y ∈ [c3.z].head?, Color.adjXY G X Y .red x y :=
    junc (getLast?_seg hjr (le_refl _)) rfl (edgeLastAi c3)
  have e23 : ∀ x ∈ (seg c3.A (j + 1) c3.A.length ++ [c3.z]).getLast?,
      ∀ y ∈ (seg c3.A 0 i).head?, Color.adjXY G X Y .red x y :=
    junc hglZ (head?_seg (by omega) (by omega)) (za1redi c3 hXY)
  have e34 : ∀ x ∈ (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++
        seg c3.A 0 i).getLast?,
      ∀ y ∈ (seg c3.A (i + 2) (j - 1)).head?,
      Color.adjXY G X Y .red x y :=
    junc hglS1 (head?_seg (by omega) (by omega)) eDred
  have e45 : ∀ x ∈ (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++
        seg c3.A 0 i ++ seg c3.A (i + 2) (j - 1)).getLast?,
      ∀ y ∈ [c3.A[j - 1]'hjm1].head?, Color.adjXY G X Y .red x y :=
    junc hglS2 rfl e45e
  have hR : (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
        seg c3.A (i + 2) (j - 1) ++ [c3.A[j - 1]'hjm1]).IsChain
      (Color.adjXY G X Y .red) :=
    chain_app5 hS4 hZ hS1 hS2 hM e12 e23 e34 e45
  -- blue chain `A[j-1] :: ux :: A[i] :: A[j] :: B`
  have emu : Color.adjXY G X Y .blue (c3.A[j - 1]'hjm1) c3.ux :=
    ⟨Or.inr ⟨hAj1Y, c3.ux_X⟩, fun h ↦ hC c3.ux huL _ hAj1U h.symm⟩
  have eui : Color.adjXY G X Y .blue c3.ux (c3.A[i]'hi) :=
    ⟨Or.inl ⟨c3.ux_X, hAiY⟩, hC c3.ux huL _ hAiU⟩
  have eij : Color.adjXY G X Y .blue (c3.A[i]'hi) (c3.A[j]'hj) :=
    ⟨Or.inr ⟨hAiY, hAjX⟩, hbad⟩
  have ejb : ∀ y ∈ c3.B.head?,
      Color.adjXY G X Y .blue (c3.A[j]'hj) y := by
    intro y hy
    rw [List.head?_eq_some_head c3.hB, Option.mem_some_iff] at hy
    subst hy
    exact ⟨Or.inl ⟨hAjX, B_head_mem_Y hXY c3⟩,
      hB' _ hAjL (List.getElem_mem _)⟩
  have hBl : (c3.A[j - 1]'hjm1 :: c3.ux :: c3.A[i]'hi :: c3.A[j]'hj ::
      c3.B).IsChain (Color.adjXY G X Y .blue) :=
    chain_cons (head_edge emu) (chain_cons (head_edge eui)
      (chain_cons (head_edge eij) (chain_cons ejb (chainB c3))))
  -- take/drop identities for the normal form
  have htk : c3.A.take (i + 1) = seg c3.A 0 i ++ [c3.A[i]'hi] := by
    rw [take_succ_eq hi, ← seg_eq_take c3.A i]
  have hsgs : seg c3.A (i + 2) c3.A.length
      = seg c3.A (i + 2) (j - 1) ++
        (c3.A[j - 1]'hjm1 :: c3.A[j]'hj ::
          seg c3.A (j + 1) c3.A.length) := by
    have e2 : seg c3.A (j - 1) j = [c3.A[j - 1]'hjm1] := by
      have h := seg_singleton (l := c3.A) hjm1
      rwa [show j - 1 + 1 = j by omega] at h
    have e3 : seg c3.A j (j + 1) = [c3.A[j]'hj] := seg_singleton hj
    rw [← seg_cat (show i + 2 ≤ j + 1 by omega)
        (show j + 1 ≤ c3.A.length by omega),
      ← seg_cat (show i + 2 ≤ j - 1 by omega)
        (show j - 1 ≤ j + 1 by omega),
      ← seg_cat (show j - 1 ≤ j by omega) (show j ≤ j + 1 by omega),
      e2, e3]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hdr : c3.A.drop (i + 2) = seg c3.A (i + 2) (j - 1) ++
      (c3.A[j - 1]'hjm1 :: c3.A[j]'hj ::
        seg c3.A (j + 1) c3.A.length) := by
    rw [← seg_eq_drop (le_refl _), hsgs]
  -- permutation of the rotated vertex list to the normal form
  have hinner : List.Perm
      ((seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
          seg c3.A (i + 2) (j - 1)) ++
        c3.A[j - 1]'hjm1 :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B)
      (c3.A.take (i + 1) ++ c3.A.drop (i + 2) ++ c3.z :: c3.B) := by
    have e0 : (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
          seg c3.A (i + 2) (j - 1)) ++
          (c3.A[j - 1]'hjm1 :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B)
        = seg c3.A (j + 1) c3.A.length ++ c3.z ::
          (seg c3.A 0 i ++ (seg c3.A (i + 2) (j - 1) ++
            (c3.A[j - 1]'hjm1 :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B))) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    calc (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
            seg c3.A (i + 2) (j - 1)) ++
          c3.A[j - 1]'hjm1 :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B
        ~ c3.z :: (seg c3.A (j + 1) c3.A.length ++
            (seg c3.A 0 i ++ (seg c3.A (i + 2) (j - 1) ++
              (c3.A[j - 1]'hjm1 :: c3.A[i]'hi :: c3.A[j]'hj ::
                c3.B)))) :=
          (List.Perm.of_eq e0).trans List.perm_middle
      _ ~ c3.z :: ((seg c3.A 0 i ++ (seg c3.A (i + 2) (j - 1) ++
              (c3.A[j - 1]'hjm1 :: c3.A[i]'hi :: c3.A[j]'hj ::
                c3.B))) ++
            seg c3.A (j + 1) c3.A.length) :=
          List.Perm.cons _ List.perm_append_comm
      _ ~ c3.z :: (seg c3.A 0 i ++ (seg c3.A (i + 2) (j - 1) ++
            (c3.A[j - 1]'hjm1 :: c3.A[i]'hi :: c3.A[j]'hj ::
              (c3.B ++ seg c3.A (j + 1) c3.A.length)))) :=
          List.Perm.cons _ (List.Perm.of_eq (by
            simp only [List.append_assoc, List.cons_append]))
      _ ~ c3.z :: (seg c3.A 0 i ++ (seg c3.A (i + 2) (j - 1) ++
            (c3.A[j - 1]'hjm1 :: c3.A[i]'hi :: c3.A[j]'hj ::
              (seg c3.A (j + 1) c3.A.length ++ c3.B)))) :=
          List.Perm.cons _
            (((List.Perm.cons _ (List.Perm.cons _
              (List.Perm.cons _ List.perm_append_comm))).append_left _).append_left _)
      _ ~ c3.z :: (seg c3.A 0 i ++
            (c3.A[i]'hi :: (seg c3.A (i + 2) (j - 1) ++
              (c3.A[j - 1]'hjm1 :: c3.A[j]'hj ::
                (seg c3.A (j + 1) c3.A.length ++ c3.B))))) :=
          List.Perm.cons _
            ((((List.Perm.swap _ _ _).append_left _).trans
              List.perm_middle).append_left _)
      _ ~ (seg c3.A 0 i ++
            (c3.A[i]'hi :: (seg c3.A (i + 2) (j - 1) ++
              (c3.A[j - 1]'hjm1 :: c3.A[j]'hj ::
                seg c3.A (j + 1) c3.A.length)))) ++ c3.z :: c3.B :=
          (List.Perm.cons _ (List.Perm.of_eq (by
            simp only [List.append_assoc, List.cons_append]))).trans
            List.perm_middle.symm
      _ ~ c3.A.take (i + 1) ++ c3.A.drop (i + 2) ++ c3.z :: c3.B :=
          List.Perm.of_eq (by
            rw [htk, hdr]
            simp only [List.append_assoc, List.cons_append,
              List.nil_append])
  have hperm : List.Perm
      ((seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
          seg c3.A (i + 2) (j - 1)) ++
        c3.A[j - 1]'hjm1 :: c3.ux :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B)
      (c3.ux :: (c3.A.take (i + 1) ++ c3.A.drop (i + 2) ++
        c3.z :: c3.B)) :=
    (((List.Perm.swap _ _ _).append_left _).trans
      List.perm_middle).trans (List.Perm.cons _ hinner)
  have hndNF : (c3.ux :: (c3.A.take (i + 1) ++ c3.A.drop (i + 2) ++
        c3.z :: c3.B)).Nodup :=
    List.nodup_cons.mpr
      ⟨fun h ↦ c3.ux_not_mem (mem_S_of_td_A c3 h),
        nodup_NF_A c3 (i + 1) (i + 2) (by omega)⟩
  -- the rotated bipath and the length bookkeeping
  have hbip : IsBipath G X Y
      (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
        seg c3.A (i + 2) (j - 1))
      (c3.A[j - 1]'hjm1)
      (c3.ux :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B) :=
    ⟨hR, hBl, hperm.nodup_iff.2 hndNF⟩
  have hlen : bipathLen c3.A c3.z c3.B = bipathLen
      (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
        seg c3.A (i + 2) (j - 1))
      (c3.A[j - 1]'hjm1)
      (c3.ux :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B) := by
    simp only [bipathLen, List.length_append, List.length_cons,
      List.length_nil, seg_length]
    omega
  have hmax' : ∀ A'' z'' B'', IsBipathO G X Y A'' z'' B'' →
      bipathLen A'' z'' B'' ≤ bipathLen
        (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
          seg c3.A (i + 2) (j - 1))
        (c3.A[j - 1]'hjm1)
        (c3.ux :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B) :=
    fun A'' z'' B'' h ↦ (c3.hmax A'' z'' B'' h).trans (le_of_eq hlen)
  -- nonemptiness and endpoints
  have hne21 : seg c3.A (j + 1) c3.A.length ++ [c3.z] ≠ [] :=
    fun e ↦ hS4ne ((List.append_eq_nil_iff.mp e).1)
  have hne31 : seg c3.A (j + 1) c3.A.length ++ [c3.z] ++
      seg c3.A 0 i ≠ [] :=
    fun e ↦ hS4ne ((List.append_eq_nil_iff.mp
      ((List.append_eq_nil_iff.mp e).1)).1)
  have hAne : (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
        seg c3.A (i + 2) (j - 1)) ≠ [] :=
    fun e ↦ hS4ne ((List.append_eq_nil_iff.mp
      ((List.append_eq_nil_iff.mp
        ((List.append_eq_nil_iff.mp e).1)).1)).1)
  have hBne : (c3.ux :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B) ≠ [] :=
    List.cons_ne_nil _ _
  have hhd : (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
        seg c3.A (i + 2) (j - 1)).head?
      = some (c3.A[j + 1]'hjr) := by
    rw [List.head?_append_of_ne_nil _ hne31,
      List.head?_append_of_ne_nil _ hne21,
      List.head?_append_of_ne_nil _ hS4ne,
      head?_seg hjr (le_refl _)]
  have hhd' : (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
        seg c3.A (i + 2) (j - 1)).head hAne = c3.A[j + 1]'hjr :=
    Option.some.inj ((List.head?_eq_some_head hAne).symm.trans hhd)
  have hhdY : (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
        seg c3.A (i + 2) (j - 1)).head hAne ∈ Y := by
    rw [hhd']
    exact (c3.a_side hXY _ hjr).1.mpr (by omega)
  have hgl : (c3.ux :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B).getLast hBne
      = c3.B.getLast c3.hB := by
    rw [List.getLast_cons (List.cons_ne_nil _ _),
      List.getLast_cons (List.cons_ne_nil _ _),
      List.getLast_cons c3.hB]
  have hblY : (c3.ux :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B).getLast hBne
      ∈ Y := by
    rw [hgl]; exact c3.hlast
  -- the leftover vertex `A[i+1]` lies outside the rotated bipath
  have hu : (c3.A[i + 1]'hlt) ∉
      (seg c3.A (j + 1) c3.A.length ++ [c3.z] ++ seg c3.A 0 i ++
        seg c3.A (i + 2) (j - 1)) ++
        c3.A[j - 1]'hjm1 :: c3.ux :: c3.A[i]'hi :: c3.A[j]'hj :: c3.B := by
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h1 | h2
          · obtain ⟨k, hk1, hk2, hk3, hke⟩ := mem_seg h1
            exact absurd (c3.a_inj hk3 hlt hke) (by omega)
          · rcases List.mem_cons.mp h2 with e | h2
            · exact c3.a_ne_z hlt e
            · simp at h2
        · obtain ⟨k, hk1, hk2, hk3, hke⟩ := mem_seg h
          exact absurd (c3.a_inj hk3 hlt hke) (by omega)
      · obtain ⟨k, hk1, hk2, hk3, hke⟩ := mem_seg h
        exact absurd (c3.a_inj hk3 hlt hke) (by omega)
    · rcases List.mem_cons.mp h with e | h
      · exact absurd (c3.a_inj hlt hjm1 e) (by omega)
      · rcases List.mem_cons.mp h with e | h
        · have hm : (c3.A[i + 1]'hlt) ∈ c3.A ++ c3.z :: c3.B :=
            List.mem_append_left _ (List.getElem_mem hlt)
          rw [e] at hm
          exact c3.ux_not_mem hm
        · rcases List.mem_cons.mp h with e | h
          · exact absurd (c3.a_inj hlt hi e) (by omega)
          · rcases List.mem_cons.mp h with e | hB
            · exact absurd (c3.a_inj hlt hj e) (by omega)
            · exact c3.a_not_mem_B hlt hB
  exact bipathO_kill_Ymid hXY hbip hmax' hu hAj1Y hupX hAne hBne hhdY hblY

end Case3Data

end JSP415
