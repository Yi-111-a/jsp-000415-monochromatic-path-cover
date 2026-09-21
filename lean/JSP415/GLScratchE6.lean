import JSP415.GLScratchE3

open Finset
open Classical
open scoped List

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

namespace Case3Data

/-- Claim E, `l = z` case: every even-position vertex `A[i]` is red-adjacent
to `z`.  For `i = 0` this is claim A (`za1redi`); for `i = r - 1` it is the
last edge of the bipath (`edgeLastAi`); for `2 ≤ i ≤ r - 3` the rotation
`(A[r-1],…,A[i+2], A[i-1],…,A[1] ; A[0] ; ux, A[i], z, B)` is an
equal-length bipath of the killed `Y`-midpoint type (leftover `A[i+1] ∈ X`,
endpoints `A[r-1], B.getLast ∈ Y`). -/
theorem e_z (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hB' : c3.ClaimB') (hC : ∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u)
    (hux2 : c3.HasUx2) {i : ℕ}
    (hi : i < c3.A.length) (hpar : i % 2 = 0) :
    G.Adj c3.A[i] c3.z := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact (za1redi c3 hXY).2.symm
  · rcases Nat.lt_or_ge (i + 1) c3.A.length with hlt | hge
    · -- rotation case: 2 ≤ i (i even) and i + 2 < r
      by_contra hbad
      have hro : c3.A.length % 2 = 1 := c3.r_odd hXY
      have h0len : 0 < c3.A.length := by omega
      have huL : c3.ux ∈ c3.L2 := (e3mem_L2 c3).mpr ⟨c3.ux_X, c3.ux_not_mem⟩
      have hA0Y : (c3.A[0]'h0len) ∈ Y := (c3.a_side hXY 0 h0len).1.mpr (by omega)
      have hAiY : (c3.A[i]'hi) ∈ Y := (c3.a_side hXY i hi).1.mpr hpar
      have hA0U : (c3.A[0]'h0len) ∈ c3.S1U := c3.a_mem_S1U hXY h0len (by omega)
      have hAiU : (c3.A[i]'hi) ∈ c3.S1U := c3.a_mem_S1U hXY hi hpar
      have hupX : (c3.A[i + 1]'hlt) ∈ X :=
        (c3.a_side hXY (i + 1) hlt).2.mpr (by omega)
      -- descending red segments
      have hs1 : (seg c3.A (i + 2) c3.A.length).reverse.IsChain
          (Color.adjXY G X Y .red) := chain_seg_rev (chainA c3)
      have hs2 : (seg c3.A 1 i).reverse.IsChain
          (Color.adjXY G X Y .red) := chain_seg_rev (chainA c3)
      have hs1ne : (seg c3.A (i + 2) c3.A.length).reverse ≠ [] :=
        List.reverse_ne_nil_iff.mpr (seg_ne_nil (by omega) (le_refl _))
      have hs2ne : (seg c3.A 1 i).reverse ≠ [] :=
        List.reverse_ne_nil_iff.mpr (seg_ne_nil (by omega) (by omega))
      -- junction edges
      have eD : G.Adj (c3.A[i - 1]'(by omega)) (c3.A[i + 2]'(by omega)) := by
        have h := c3.claimD_odd hXY hB' hC hux2
          (show i - 1 + 3 < c3.A.length by omega)
          (show (i - 1) % 2 = 1 by omega)
        simpa only [show i - 1 + 3 = i + 2 by omega] using h
      have e12adj : Color.adjXY G X Y .red (c3.A[i + 2]'(by omega))
          (c3.A[i - 1]'(by omega)) :=
        redEdgeYX ((c3.a_side hXY (i + 2) (by omega)).1.mpr (by omega))
          ((c3.a_side hXY (i - 1) (by omega)).2.mpr (by omega)) eD.symm
      have e10 : Color.adjXY G X Y .red (c3.A[1]'(by omega))
          (c3.A[0]'h0len) :=
        Color.adjXY.symm (edgeA c3 0 (by omega))
      have e12 : ∀ x ∈ (seg c3.A (i + 2) c3.A.length).reverse.getLast?,
          ∀ y ∈ (seg c3.A 1 i).reverse.head?,
          Color.adjXY G X Y .red x y :=
        junc (getLast?_seg_rev (by omega) (le_refl _))
          (head?_seg_rev (by omega) (by omega)) e12adj
      have hgl : ((seg c3.A (i + 2) c3.A.length).reverse ++
          (seg c3.A 1 i).reverse).getLast? = some (c3.A[1]'(by omega)) := by
        rw [List.getLast?_append_of_ne_nil _ hs2ne,
          getLast?_seg_rev (by omega) (by omega)]
      have e23 : ∀ x ∈ ((seg c3.A (i + 2) c3.A.length).reverse ++
            (seg c3.A 1 i).reverse).getLast?,
          ∀ y ∈ [(c3.A[0]'h0len)].head?, Color.adjXY G X Y .red x y :=
        junc hgl rfl e10
      have hR : ((seg c3.A (i + 2) c3.A.length).reverse ++
            (seg c3.A 1 i).reverse ++ [(c3.A[0]'h0len)]).IsChain
          (Color.adjXY G X Y .red) :=
        chain_app3 hs1 hs2 (List.isChain_singleton _) e12 e23
      -- blue chain `A[0] :: ux :: A[i] :: z :: B`
      have e0u : Color.adjXY G X Y .blue (c3.A[0]'h0len) c3.ux :=
        ⟨Or.inr ⟨hA0Y, c3.ux_X⟩, fun h ↦ hC c3.ux huL _ hA0U h.symm⟩
      have eui : Color.adjXY G X Y .blue c3.ux (c3.A[i]'hi) :=
        ⟨Or.inl ⟨c3.ux_X, hAiY⟩, hC c3.ux huL _ hAiU⟩
      have eiz : Color.adjXY G X Y .blue (c3.A[i]'hi) c3.z :=
        ⟨Or.inr ⟨hAiY, c3.hz⟩, hbad⟩
      have hBl : ((c3.A[0]'h0len) :: c3.ux :: (c3.A[i]'hi) :: c3.z :: c3.B).IsChain
          (Color.adjXY G X Y .blue) :=
        chain_cons (head_edge e0u) (chain_cons (head_edge eui)
          (chain_cons (head_edge eiz) (blueChain c3)))
      -- take/drop identities for the normal form
      have htk : c3.A.take (i + 1)
          = [(c3.A[0]'h0len)] ++ seg c3.A 1 i ++ [(c3.A[i]'hi)] := by
        have e1 : c3.A.take (i + 1) = c3.A.take i ++ [(c3.A[i]'hi)] :=
          take_succ_eq hi
        have e3 : seg c3.A 0 1 = [(c3.A[0]'h0len)] := seg_singleton h0len
        have e2 : c3.A.take i = [(c3.A[0]'h0len)] ++ seg c3.A 1 i := by
          rw [← seg_eq_take c3.A i,
            ← seg_cat (Nat.zero_le 1) (show 1 ≤ i by omega), e3]
        rw [e1, e2]
      have hdr : c3.A.drop (i + 2) = seg c3.A (i + 2) c3.A.length :=
        (seg_eq_drop (le_refl _)).symm
      -- permutation to the normal form
      have hperm : List.Perm
          ((seg c3.A (i + 2) c3.A.length).reverse ++ (seg c3.A 1 i).reverse ++
            (c3.A[0]'h0len) :: c3.ux :: (c3.A[i]'hi) :: c3.z :: c3.B)
          (c3.ux :: (c3.A.take (i + 1) ++ c3.A.drop (i + 2) ++
            c3.z :: c3.B)) := by
        calc (seg c3.A (i + 2) c3.A.length).reverse ++
                (seg c3.A 1 i).reverse ++
                  (c3.A[0]'h0len) :: c3.ux :: (c3.A[i]'hi) :: c3.z :: c3.B
            ~ (seg c3.A (i + 2) c3.A.length ++ seg c3.A 1 i) ++
                (c3.A[0]'h0len) :: c3.ux :: (c3.A[i]'hi) :: c3.z :: c3.B := by
              exact (((List.reverse_perm _).append_right _).append_right _).trans
                (((List.reverse_perm _).append_left _).append_right _)
          _ ~ c3.ux :: ((seg c3.A (i + 2) c3.A.length ++ seg c3.A 1 i) ++
                (c3.A[0]'h0len) :: (c3.A[i]'hi) :: c3.z :: c3.B) := by
              exact ((List.Perm.swap _ _ _).append_left _).trans
                List.perm_middle
          _ ~ c3.ux :: (((c3.A[0]'h0len) :: (c3.A[i]'hi) :: c3.z :: c3.B) ++
                (seg c3.A (i + 2) c3.A.length ++ seg c3.A 1 i)) :=
              List.Perm.cons _ List.perm_append_comm
          _ ~ c3.ux :: ((c3.A[0]'h0len) :: (c3.A[i]'hi) ::
                ((seg c3.A (i + 2) c3.A.length ++ seg c3.A 1 i) ++
                  c3.z :: c3.B)) := by
              have h : ((c3.A[0]'h0len) :: (c3.A[i]'hi) :: c3.z :: c3.B) ++
                    (seg c3.A (i + 2) c3.A.length ++ seg c3.A 1 i)
                  = (c3.A[0]'h0len) :: (c3.A[i]'hi) :: c3.z ::
                      (c3.B ++ (seg c3.A (i + 2) c3.A.length ++ seg c3.A 1 i)) :=
                rfl
              exact (List.Perm.cons _ (List.Perm.of_eq h)).trans
                (List.Perm.cons _ (List.Perm.cons _
                  (List.Perm.cons _ perm_z_to_mid)))
          _ ~ c3.ux :: ((c3.A[0]'h0len) ::
                ((seg c3.A (i + 2) c3.A.length ++ seg c3.A 1 i) ++
                  (c3.A[i]'hi) :: c3.z :: c3.B)) := by
              exact List.Perm.cons _ (List.Perm.cons _ List.perm_middle.symm)
          _ ~ c3.ux :: ((c3.A[0]'h0len) ::
                ((seg c3.A 1 i ++ seg c3.A (i + 2) c3.A.length) ++
                  (c3.A[i]'hi) :: c3.z :: c3.B)) := by
              exact List.Perm.cons _ (List.Perm.cons _
                (List.perm_append_comm.append_right _))
          _ ~ c3.ux :: ((c3.A[0]'h0len) ::
                (seg c3.A 1 i ++ (seg c3.A (i + 2) c3.A.length ++
                  (c3.A[i]'hi) :: c3.z :: c3.B))) := by
              exact List.Perm.cons _ (List.Perm.cons _
                (List.Perm.of_eq (List.append_assoc _ _ _)))
          _ ~ c3.ux :: ((c3.A[0]'h0len) ::
                (seg c3.A 1 i ++ (c3.A[i]'hi) ::
                  (seg c3.A (i + 2) c3.A.length ++ c3.z :: c3.B))) := by
              exact List.Perm.cons _ (List.Perm.cons _
                (List.perm_middle.append_left _))
          _ ~ c3.ux :: (c3.A.take (i + 1) ++ c3.A.drop (i + 2) ++
                c3.z :: c3.B) := by
              have htd : c3.A.take (i + 1) ++ c3.A.drop (i + 2) ++ c3.z :: c3.B
                  = (c3.A[0]'h0len) :: (seg c3.A 1 i ++ ((c3.A[i]'hi) ::
                      (seg c3.A (i + 2) c3.A.length ++ (c3.z :: c3.B)))) := by
                rw [htk, hdr]
                simp only [List.append_assoc, List.cons_append,
                  List.nil_append]
              exact List.Perm.of_eq (congrArg _ htd.symm)
      have hndNF : (c3.ux :: (c3.A.take (i + 1) ++ c3.A.drop (i + 2) ++
            c3.z :: c3.B)).Nodup := by
        refine List.nodup_cons.mpr ⟨?_,
          nodup_NF_A c3 (i + 1) (i + 2) (by omega)⟩
        intro h
        exact c3.ux_not_mem (mem_S_of_td_A c3 h)
      -- the rotated bipath and the length bookkeeping
      have hbip : IsBipath G X Y
          ((seg c3.A (i + 2) c3.A.length).reverse ++ (seg c3.A 1 i).reverse)
          (c3.A[0]'h0len) (c3.ux :: (c3.A[i]'hi) :: c3.z :: c3.B) :=
        ⟨hR, hBl, hperm.nodup_iff.2 hndNF⟩
      have hlen : bipathLen c3.A c3.z c3.B = bipathLen
          ((seg c3.A (i + 2) c3.A.length).reverse ++ (seg c3.A 1 i).reverse)
          (c3.A[0]'h0len) (c3.ux :: (c3.A[i]'hi) :: c3.z :: c3.B) := by
        simp only [bipathLen, List.length_append, List.length_reverse,
          List.length_cons, seg_length]
        omega
      have hmax' : ∀ A'' z'' B'', IsBipathO G X Y A'' z'' B'' →
          bipathLen A'' z'' B'' ≤ bipathLen
            ((seg c3.A (i + 2) c3.A.length).reverse ++ (seg c3.A 1 i).reverse)
            (c3.A[0]'h0len) (c3.ux :: (c3.A[i]'hi) :: c3.z :: c3.B) :=
        fun A'' z'' B'' h ↦ (c3.hmax A'' z'' B'' h).trans (le_of_eq hlen)
      -- nonemptiness and endpoints
      have hAne : (seg c3.A (i + 2) c3.A.length).reverse ++
          (seg c3.A 1 i).reverse ≠ [] :=
        fun e ↦ hs1ne (List.append_eq_nil_iff.mp e).1
      have hBne : (c3.ux :: (c3.A[i]'hi) :: c3.z :: c3.B) ≠ [] :=
        List.cons_ne_nil _ _
      have hhd : ((seg c3.A (i + 2) c3.A.length).reverse ++
            (seg c3.A 1 i).reverse).head? =
          some (c3.A[c3.A.length - 1]'(by omega)) := by
        rw [List.head?_append_of_ne_nil _ hs1ne]
        exact head?_seg_rev (by omega) (le_refl _)
      have hhd' : ((seg c3.A (i + 2) c3.A.length).reverse ++
            (seg c3.A 1 i).reverse).head hAne =
          (c3.A[c3.A.length - 1]'(by omega)) :=
        Option.some.inj ((List.head?_eq_some_head hAne).symm.trans hhd)
      have hhdY : ((seg c3.A (i + 2) c3.A.length).reverse ++
            (seg c3.A 1 i).reverse).head hAne ∈ Y := by
        rw [hhd']
        exact (c3.a_side hXY _ (by omega)).1.mpr (by omega)
      have hgl2 : (c3.ux :: (c3.A[i]'hi) :: c3.z :: c3.B).getLast hBne
          = c3.B.getLast c3.hB := by
        rw [List.getLast_cons (List.cons_ne_nil _ _),
          List.getLast_cons (List.cons_ne_nil _ _),
          List.getLast_cons c3.hB]
      have hblY : (c3.ux :: (c3.A[i]'hi) :: c3.z :: c3.B).getLast hBne ∈ Y := by
        rw [hgl2]; exact c3.hlast
      -- the leftover vertex `A[i+1]` lies outside the rotated bipath
      have hu : (c3.A[i + 1]'hlt) ∉
          (seg c3.A (i + 2) c3.A.length).reverse ++ (seg c3.A 1 i).reverse ++
            (c3.A[0]'h0len) :: c3.ux :: (c3.A[i]'hi) :: c3.z :: c3.B := by
        intro hmem
        rcases List.mem_append.mp hmem with h | h
        · rcases List.mem_append.mp h with h1 | h2
          · obtain ⟨k, hk1, hk2, hk3, hke⟩ :=
              mem_seg (List.mem_reverse.mp h1)
            exact absurd (c3.a_inj hk3 hlt hke) (by omega)
          · obtain ⟨k, hk1, hk2, hk3, hke⟩ :=
              mem_seg (List.mem_reverse.mp h2)
            exact absurd (c3.a_inj hk3 hlt hke) (by omega)
        · rcases List.mem_cons.mp h with e | h
          · exact absurd (c3.a_inj hlt h0len e) (by omega)
          · rcases List.mem_cons.mp h with e | h
            · have hm : (c3.A[i + 1]'hlt) ∈ c3.A ++ c3.z :: c3.B :=
                List.mem_append_left _ (List.getElem_mem hlt)
              rw [e] at hm
              exact c3.ux_not_mem hm
            · rcases List.mem_cons.mp h with e | h
              · exact absurd (c3.a_inj hlt hi e) (by omega)
              · rcases List.mem_cons.mp h with e | hB
                · exact c3.a_ne_z hlt e
                · exact c3.a_not_mem_B hlt hB
      exact bipathO_kill_Ymid hXY hbip hmax' hu hA0Y hupX hAne hBne hhdY hblY
    · -- boundary case `i = r - 1`: the last red edge of the bipath
      have hieq : i = c3.A.length - 1 := by omega
      subst hieq
      exact (edgeLastAi c3).2

end Case3Data

end JSP415
