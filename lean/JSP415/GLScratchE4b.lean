import JSP415.GLScratchE3

open Finset
open Classical
open scoped List

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

namespace Case3Data

/-- Claim E, forward direction, `i = 0`, `j + 2 < r`: the edge `A[0]–A[j]` is
red.  Otherwise the rotated bipath
`(A[1..j-1] ++ A[j+2..r-1] ; z ; B.reverse ++ [A[j], A[0], ux])` is an
equal-length bipath killed by `bipathO_leftover_opp_of_same_ends` (leftover
`A[j+1] ∈ Y`, endpoints `A[1], ux ∈ X`, midpoint `z ∈ X`). -/
theorem e_dir_i0 (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hB' : c3.ClaimB') (hC : ∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u)
    (hux2 : c3.HasUx2) {j : ℕ}
    (hj : j < c3.A.length) (hjp : j % 2 = 1)
    (hij : 5 ≤ j) (hjr : j + 2 < c3.A.length) :
    G.Adj c3.A[0] c3.A[j] := by
  by_contra hbad
  have hro : c3.A.length % 2 = 1 := c3.r_odd hXY
  have h0len : 0 < c3.A.length := by omega
  have h1len : 1 < c3.A.length := by omega
  have hjm1 : j - 1 < c3.A.length := by omega
  have hjp1 : j + 1 < c3.A.length := by omega
  have hsB : 0 < c3.B.length := List.length_pos_of_ne_nil c3.hB
  have huL : c3.ux ∈ c3.L2 := (e3mem_L2 c3).mpr ⟨c3.ux_X, c3.ux_not_mem⟩
  -- side facts
  have hA0Y : (c3.A[0]'h0len) ∈ Y := (c3.a_side hXY 0 h0len).1.mpr (by omega)
  have hAjX : (c3.A[j]'hj) ∈ X := (c3.a_side hXY j hj).2.mpr hjp
  have hA1X : (c3.A[1]'h1len) ∈ X := (c3.a_side hXY 1 h1len).2.mpr (by omega)
  have hAj1Y : (c3.A[j + 1]'hjp1) ∈ Y :=
    (c3.a_side hXY (j + 1) hjp1).1.mpr (by omega)
  have hA0U : (c3.A[0]'h0len) ∈ c3.S1U := c3.a_mem_S1U hXY h0len (by omega)
  have hB0Y : (c3.B[0]'hsB) ∈ Y := (c3.b_side hXY 0 hsB).1.mpr (by omega)
  -- red chain pieces
  have hs1 : (seg c3.A 1 j).IsChain (Color.adjXY G X Y .red) :=
    chain_seg (chainA c3)
  have hs2 : (seg c3.A (j + 2) c3.A.length).IsChain (Color.adjXY G X Y .red) :=
    chain_seg (chainA c3)
  have hs1ne : seg c3.A 1 j ≠ [] := seg_ne_nil (by omega) (by omega)
  have hs2ne : seg c3.A (j + 2) c3.A.length ≠ [] :=
    seg_ne_nil (by omega) (le_refl _)
  -- junction `A[j-1]–A[j+2]` via claim D (even)
  have eD : G.Adj (c3.A[j - 1]'hjm1) (c3.A[j + 2]'hjr) := by
    have h := c3.claimD_even hXY hB' hC hux2
      (show j - 1 + 3 < c3.A.length by omega)
      (show (j - 1) % 2 = 0 by omega)
    simpa only [show j - 1 + 3 = j + 2 by omega] using h
  have e12adj : Color.adjXY G X Y .red (c3.A[j - 1]'hjm1) (c3.A[j + 2]'hjr) :=
    redEdgeYX ((c3.a_side hXY (j - 1) hjm1).1.mpr (by omega))
      ((c3.a_side hXY (j + 2) hjr).2.mpr (by omega)) eD
  have e12 : ∀ x ∈ (seg c3.A 1 j).getLast?,
      ∀ y ∈ (seg c3.A (j + 2) c3.A.length).head?,
      Color.adjXY G X Y .red x y :=
    junc (getLast?_seg (by omega) (by omega))
      (head?_seg (by omega) (le_refl _)) e12adj
  have hgl : (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length).getLast? =
      some (c3.A[c3.A.length - 1]'(by omega)) := by
    rw [List.getLast?_append_of_ne_nil _ hs2ne,
      getLast?_seg (by omega) (le_refl _)]
  have e23 : ∀ x ∈ (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length).getLast?,
      ∀ y ∈ [c3.z].head?, Color.adjXY G X Y .red x y :=
    junc hgl rfl (edgeLastAi c3)
  have hR : (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length ++ [c3.z]).IsChain
      (Color.adjXY G X Y .red) :=
    chain_app3 hs1 hs2 (List.isChain_singleton _) e12 e23
  -- blue chain `z :: B.reverse ++ [A[j], A[0], ux]`
  have hBrevC : c3.B.reverse.IsChain (Color.adjXY G X Y .blue) :=
    Color.adjXY.isChain_reverse (chainB c3)
  have hBj : ¬ G.Adj (c3.A[j]'hj) (c3.B[0]'hsB) := by
    have h := hB' _ (c3.a_mem_SL hXY hj hjp) (List.getElem_mem hj)
    rwa [List.head_eq_getElem_zero] at h
  have eb0j : Color.adjXY G X Y .blue (c3.B[0]'hsB) (c3.A[j]'hj) :=
    blueEdgeYX hB0Y hAjX (fun h ↦ hBj h.symm)
  have ej0 : Color.adjXY G X Y .blue (c3.A[j]'hj) (c3.A[0]'h0len) :=
    blueEdgeXY hAjX hA0Y (fun h ↦ hbad h.symm)
  have e0u : Color.adjXY G X Y .blue (c3.A[0]'h0len) c3.ux :=
    blueEdgeYX hA0Y c3.ux_X (fun h ↦ hC c3.ux huL _ hA0U h.symm)
  have hglB : c3.B.reverse.getLast? = some (c3.B[0]'hsB) := by
    rw [List.getLast?_reverse, List.head?_eq_some_head c3.hB,
      List.head_eq_getElem_zero]
  have eBj : ∀ x ∈ c3.B.reverse.getLast?,
      ∀ y ∈ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux].head?,
      Color.adjXY G X Y .blue x y :=
    junc hglB rfl eb0j
  have htail : ([c3.A[j]'hj, c3.A[0]'h0len, c3.ux]).IsChain
      (Color.adjXY G X Y .blue) :=
    chain_cons (head_edge ej0)
      (chain_cons (head_edge e0u) (List.isChain_singleton _))
  have hBi : (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]).IsChain
      (Color.adjXY G X Y .blue) :=
    chain_app hBrevC htail eBj
  have hBrevNe : c3.B.reverse ≠ [] := List.reverse_ne_nil_iff.mpr c3.hB
  have hhdB : (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]).head? =
      some (c3.B[c3.B.length - 1]'(by omega)) := by
    rw [List.head?_append_of_ne_nil _ hBrevNe, List.head?_reverse,
      List.getLast?_eq_getLast c3.hB, List.getLast_eq_getElem]
  have hBl : (c3.z ::
        (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux])).IsChain
      (Color.adjXY G X Y .blue) := by
    refine chain_cons ?_ hBi
    intro y hy
    rw [hhdB, Option.mem_some_iff] at hy
    subst hy
    exact zbsBluei c3 hXY
  -- take/drop identities for the normal form
  have htk : c3.A.take (j + 1)
      = [c3.A[0]'h0len] ++ seg c3.A 1 j ++ [c3.A[j]'hj] := by
    have e1 : c3.A.take (j + 1) = c3.A.take j ++ [c3.A[j]'hj] := take_succ_eq hj
    have e3 : seg c3.A 0 1 = [c3.A[0]'h0len] := seg_singleton h0len
    have e2 : c3.A.take j = [c3.A[0]'h0len] ++ seg c3.A 1 j := by
      rw [← seg_eq_take c3.A j,
        ← seg_cat (Nat.zero_le 1) (show 1 ≤ j by omega), e3]
    rw [e1, e2]
  have hdr : c3.A.drop (j + 2) = seg c3.A (j + 2) c3.A.length :=
    (seg_eq_drop (le_refl _)).symm
  have hNF : c3.A[0]'h0len ::
      ((seg c3.A 1 j ++ c3.A[j]'hj :: seg c3.A (j + 2) c3.A.length) ++
        c3.z :: c3.B)
      = c3.A.take (j + 1) ++ c3.A.drop (j + 2) ++ c3.z :: c3.B := by
    rw [htk, hdr]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- permutation of the vertex list to the normal form
  have hperm : List.Perm
      ((seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length) ++
        c3.z :: (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]))
      (c3.ux :: (c3.A.take (j + 1) ++ c3.A.drop (j + 2) ++ c3.z :: c3.B)) := by
    calc (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length) ++
            c3.z :: (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux])
        ~ (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length) ++
            c3.z :: (c3.B ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]) :=
          (((List.reverse_perm _).append_right _).cons _).append_left _
      _ ~ (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length) ++
            c3.z :: ([c3.A[j]'hj, c3.A[0]'h0len, c3.ux] ++ c3.B) :=
          ((List.perm_append_comm).cons _).append_left _
      _ ~ (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length) ++
            (c3.A[j]'hj :: c3.A[0]'h0len :: c3.ux :: c3.z :: c3.B) :=
          perm_rot3.append_left _
      _ ~ (c3.A[j]'hj :: c3.A[0]'h0len :: c3.ux :: c3.z :: c3.B) ++
            (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length) :=
          List.perm_append_comm
      _ ~ c3.A[j]'hj :: c3.A[0]'h0len :: c3.ux :: c3.z ::
            (c3.B ++ (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length)) :=
          List.Perm.of_eq rfl
      _ ~ c3.A[j]'hj :: c3.A[0]'h0len :: c3.ux ::
            ((seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length) ++ c3.z :: c3.B) :=
          List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ perm_z_to_mid))
      _ ~ c3.ux :: c3.A[0]'h0len :: c3.A[j]'hj ::
            ((seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length) ++ c3.z :: c3.B) :=
          perm_rot2.trans (List.Perm.swap _ _ _)
      _ ~ c3.ux :: c3.A[0]'h0len ::
            ((c3.A[j]'hj :: (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length)) ++
              c3.z :: c3.B) :=
          List.Perm.cons _ (List.Perm.cons _ (List.Perm.of_eq rfl))
      _ ~ c3.ux :: c3.A[0]'h0len ::
            ((seg c3.A 1 j ++ c3.A[j]'hj :: seg c3.A (j + 2) c3.A.length) ++
              c3.z :: c3.B) :=
          List.Perm.cons _ (List.Perm.cons _ (List.perm_middle.symm.append_right _))
      _ ~ c3.ux ::
            (c3.A.take (j + 1) ++ c3.A.drop (j + 2) ++ c3.z :: c3.B) :=
          List.Perm.cons _ (List.Perm.of_eq hNF)
  have hndNF : (c3.ux :: (c3.A.take (j + 1) ++ c3.A.drop (j + 2) ++
        c3.z :: c3.B)).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, nodup_NF_A c3 (j + 1) (j + 2) (by omega)⟩
    intro h
    exact c3.ux_not_mem (mem_S_of_td_A c3 h)
  -- the rotated bipath and the length bookkeeping
  have hbip : IsBipath G X Y
      (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length)
      c3.z (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]) :=
    ⟨hR, hBl, hperm.nodup_iff.2 hndNF⟩
  have hlen : bipathLen c3.A c3.z c3.B = bipathLen
      (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length)
      c3.z (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]) := by
    simp only [bipathLen, List.length_append, List.length_reverse,
      List.length_cons, List.length_nil, seg_length]
    omega
  have hmax' : ∀ A'' z'' B'', IsBipathO G X Y A'' z'' B'' →
      bipathLen A'' z'' B'' ≤ bipathLen
        (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length)
        c3.z (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]) :=
    fun A'' z'' B'' h ↦ (c3.hmax A'' z'' B'' h).trans (le_of_eq hlen)
  -- nonemptiness and endpoints
  have hAne : seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length ≠ [] :=
    fun e ↦ hs2ne (List.append_eq_nil_iff.mp e).2
  have hBne : c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux] ≠ [] :=
    fun e ↦ List.cons_ne_nil _ _ (List.append_eq_nil_iff.mp e).2
  have hhd : (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length).head? =
      some (c3.A[1]'h1len) := by
    rw [List.head?_append_of_ne_nil _ hs1ne]
    exact head?_seg (by omega) (by omega)
  have hhd' : (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length).head hAne =
      (c3.A[1]'h1len) :=
    Option.some.inj ((List.head?_eq_some_head hAne).symm.trans hhd)
  have hhdX : (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length).head hAne ∈ X := by
    rw [hhd']
    exact hA1X
  have hgl2 : (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]).getLast? =
      some c3.ux := by
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rfl
  have hgl2' : (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]).getLast hBne =
      c3.ux :=
    Option.some.inj ((List.getLast?_eq_getLast hBne).symm.trans hgl2)
  have hglX : (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]).getLast hBne
      ∈ X := by
    rw [hgl2']
    exact c3.ux_X
  -- the leftover vertex `A[j+1]` lies outside the rotated bipath
  have hu : (c3.A[j + 1]'hjp1) ∉
      (seg c3.A 1 j ++ seg c3.A (j + 2) c3.A.length) ++
        c3.z :: (c3.B.reverse ++ [c3.A[j]'hj, c3.A[0]'h0len, c3.ux]) := by
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · rcases List.mem_append.mp h with h1 | h2
      · obtain ⟨k, hk1, hk2, hk3, hke⟩ := mem_seg h1
        exact absurd (c3.a_inj hk3 hjp1 hke) (by omega)
      · obtain ⟨k, hk1, hk2, hk3, hke⟩ := mem_seg h2
        exact absurd (c3.a_inj hk3 hjp1 hke) (by omega)
    · rcases List.mem_cons.mp h with e | h'
      · exact c3.a_ne_z hjp1 e
      · rcases List.mem_append.mp h' with hB | ht
        · exact c3.a_not_mem_B hjp1 (List.mem_reverse.mp hB)
        · rcases List.mem_cons.mp ht with e | ht'
          · exact absurd (c3.a_inj hjp1 hj e) (by omega)
          · rcases List.mem_cons.mp ht' with e | ht''
            · exact absurd (c3.a_inj hjp1 h0len e) (by omega)
            · rcases List.mem_cons.mp ht'' with e | hnil
              · have hm : (c3.A[j + 1]'hjp1) ∈ c3.A ++ c3.z :: c3.B :=
                  List.mem_append_left _ (List.getElem_mem hjp1)
                rw [e] at hm
                exact c3.ux_not_mem hm
              · exact absurd hnil List.not_mem_nil
  exact bipathO_leftover_opp_of_same_ends hXY hbip hmax' hu c3.hz hAj1Y
    hAne hBne hhdX hglX

end Case3Data

end JSP415
