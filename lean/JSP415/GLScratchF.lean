import JSP415.GLIface
import JSP415.GLScratchA
import JSP415.GLScratchW
import JSP415.GLScratchLC
import JSP415.GLScratchLC2
import JSP415.GLScratchGH

/-!
# GLScratchF — Gyárfás–Lehel Thm 3, case (iii): claims B″, F1, F2
-/

open Finset
open Classical

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

/-- `B[q] ∈ X` forces `q` odd (0-based). -/
theorem B_odd_of_mem_X (hXY : Disjoint X Y) (c3 : Case3Data G X Y)
    {q : ℕ} (hq : q < c3.B.length) (h : c3.B[q]'hq ∈ X) : q % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar
  · exact absurd h
      (Disjoint.notMem_right hXY (B_mem_Y_of_even hXY c3 hq hpar))
  · exact hpar

/-! ### Claim B″ -/

theorem claimB2 (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    ∀ l ∈ c3.SL, l ∈ c3.B → G.Adj (c3.A.head c3.hA) l := by
  intro l hlSL hlB
  obtain ⟨hlX, -⟩ := SL_mem hlSL
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hlB
  -- `B[n] ∈ X` forces `n` odd (0-based).
  have hpar : n % 2 = 1 := B_odd_of_mem_X hXY c3 hn hlX
  by_contra hnadj
  obtain ⟨hAz, hzbs⟩ := claimA_of_case3 hXY c3
  have hzb1 := IsBipath.blue_first_edge c3.hb c3.hB
  have hredA : c3.A.IsChain (Color.adjXY G X Y .red) := c3.hb.1.left_of_append
  have hblueB : c3.B.IsChain (Color.adjXY G X Y .blue) := c3.hb.2.1.tail
  have hnd := c3.hb.2.2
  obtain ⟨hrodd, hsodd⟩ := c3.parity_len hXY
  -- `n` odd `< s`, `s` odd ⇒ `n + 1 < s`.
  have hns : n + 1 < c3.B.length := by
    rcases Nat.lt_or_ge (n + 1) c3.B.length with h | h
    · exact h
    · have : n + 1 = c3.B.length := by omega
      omega
  -- the two reversed blue pieces
  have hP1 : (c3.B.take n).reverse.IsChain (Color.adjXY G X Y .blue) :=
    Color.adjXY.isChain_reverse (isChain_take_of n hblueB)
  have hP2 : (c3.B.drop (n + 1)).reverse.IsChain (Color.adjXY G X Y .blue) :=
    Color.adjXY.isChain_reverse (isChain_drop_of (n + 1) hblueB)
  have hP1ne : (c3.B.take n).reverse ≠ [] := by
    rw [List.reverse_ne_nil_iff, List.ne_nil_iff_length_pos, List.length_take]
    omega
  have hP2ne : (c3.B.drop (n + 1)).reverse ≠ [] := by
    rw [List.reverse_ne_nil_iff, List.ne_nil_iff_length_pos, List.length_drop]
    omega
  have hP1last : (c3.B.take n).reverse.getLast? =
      some (c3.B.head c3.hB) := by
    rw [List.getLast?_reverse, head?_take (by omega) (by omega),
      List.head?_eq_some_head c3.hB]
  have hP2head : (c3.B.drop (n + 1)).reverse.head? =
      some (c3.B.getLast c3.hB) := by
    rw [List.head?_reverse, getLast?_drop hns]
    congr 1
    exact (List.getLast_eq_getElem c3.hB).symm
  have hP2last : (c3.B.drop (n + 1)).reverse.getLast? =
      some (c3.B[n + 1]'hns) := by
    rw [List.getLast?_reverse, head?_drop hns]
  -- `dropRev ++ [B[n]]`: descending blues, last edge `B[n+1]–B[n]` consec.
  have hDR : ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn]).IsChain
      (Color.adjXY G X Y .blue) := by
    apply List.isChain_snoc' hP2
    intro x hx
    rw [hP2last, Option.mem_some_iff] at hx
    subst hx
    exact Color.adjXY.symm ((List.isChain_iff_getElem.mp hblueB) n hns)
  -- `z :: dropRev ++ [B[n]]`: first edge `z–b_{s-1}` from claim A.
  have hRest : (c3.z :: ((c3.B.drop (n + 1)).reverse ++
      [c3.B[n]'hn])).IsChain (Color.adjXY G X Y .blue) := by
    refine List.isChain_cons.mpr ⟨?_, hDR⟩
    intro y hy
    rw [List.head?_append_of_ne_nil _ hP2ne, hP2head,
      Option.mem_some_iff] at hy
    subst hy
    exact hzbs
  -- `M = takeRev ++ z :: (dropRev ++ [B[n]])`
  have hM : ((c3.B.take n).reverse ++ c3.z ::
      ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn])).IsChain
      (Color.adjXY G X Y .blue) := by
    refine List.isChain_append.mpr ⟨hP1, hRest, ?_⟩
    intro x hx y hy
    rw [hP1last, Option.mem_some_iff] at hx
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hx; subst hy
    exact Color.adjXY.symm hzb1
  have hMlast : ((c3.B.take n).reverse ++ c3.z ::
      ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn])).getLast? =
      some (c3.B[n]'hn) := by
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
      getLast?_cons_ne_nil
        (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
      List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast?_singleton]
  -- blue branch `M ++ [a₁]`, last edge `B[n]–a₁` assumed blue.
  have hBlue : (((c3.B.take n).reverse ++ c3.z ::
      ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn])) ++
      [c3.A.head c3.hA]).IsChain (Color.adjXY G X Y .blue) := by
    apply List.isChain_snoc' hM
    intro x hx
    rw [hMlast, Option.mem_some_iff] at hx
    subst hx
    exact ⟨Or.inl ⟨hlX, c3.hhead⟩, fun h ↦ hnadj h.symm⟩
  -- red branch `a₁ :: A.tail = A`
  have hRed : (c3.A.head c3.hA :: c3.A.tail).IsChain
      (Color.adjXY G X Y .red) := by
    rw [List.cons_head_tail c3.hA]; exact hredA
  -- `(drop n).reverse = dropRev ++ [B[n]]`
  have hdropn : (c3.B.drop n).reverse =
      (c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn] := by
    conv_lhs => rw [List.drop_eq_getElem_cons hn]
    rw [List.reverse_cons]
  -- vertex-list permutation `M ++ a₁ :: A.tail ~ A ++ z :: B`
  have hperm : List.Perm
      (((c3.B.take n).reverse ++ c3.z ::
        ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn])) ++
        c3.A.head c3.hA :: c3.A.tail)
      (c3.A ++ c3.z :: c3.B) := by
    rw [List.cons_head_tail c3.hA, List.append_assoc, List.cons_append]
    -- goal: `P1 ++ z :: (M2 ++ A) ~ A ++ z :: B`
    have hP1M2 : List.Perm
        ((c3.B.take n).reverse ++
          ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn])) c3.B := by
      rw [← hdropn]
      refine List.perm_append_comm.trans ?_
      rw [← List.reverse_append, List.take_append_drop]
      exact List.reverse_perm c3.B
    refine (List.perm_middle.trans (List.Perm.cons c3.z ?_)).trans
      List.perm_middle.symm
    -- goal: `P1 ++ (M2 ++ A) ~ A ++ B`
    refine (List.perm_append_comm.append_left _).trans ?_
    -- goal: `P1 ++ (A ++ M2) ~ A ++ B`
    refine (List.Perm.of_eq (List.append_assoc _ _ _).symm).trans ?_
    -- goal: `(P1 ++ A) ++ M2 ~ A ++ B`
    refine (List.perm_append_comm.append_right _).trans ?_
    -- goal: `(A ++ P1) ++ M2 ~ A ++ B`
    refine (List.Perm.of_eq (List.append_assoc _ _ _)).trans ?_
    -- goal: `A ++ (P1 ++ M2) ~ A ++ B`
    exact hP1M2.append_left _
  -- lengths: `|M| = s + 1`, so the rotation is equal-length
  have hlen : bipathLen
      ((c3.B.take n).reverse ++ c3.z ::
        ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn]))
      (c3.A.head c3.hA) c3.A.tail = bipathLen c3.A c3.z c3.B := by
    simp only [bipathLen, List.length_append, List.length_cons,
      List.length_reverse, List.length_take, List.length_drop,
      List.length_tail, List.length_nil]
    rw [Nat.min_eq_left hn.le]
    omega
  rcases Nat.lt_or_ge c3.A.length 2 with hr | hr
  · -- `r = 1`: `A = [a₁]`, tail empty — use a strictly-longer `ux`-extension.
    have hr1 : c3.A.length = 1 := by
      have := List.length_pos_of_ne_nil c3.hA; omega
    have hAt : c3.A.tail = [] := by
      rw [List.tail_eq_nil_iff]; omega
    rw [hAt] at hRed hperm
    -- vertex list `M ++ a₁ :: [] = M ++ [a₁]` ~ `A ++ z :: B`
    have hndS : (c3.ux :: c3.A ++ c3.z :: c3.B).Nodup :=
      List.nodup_cons.mpr ⟨c3.hux.2, hnd⟩
    -- `(M ++ [a₁]) ++ [ux] ~ ux :: (A ++ z :: B)`
    have hperm2 : List.Perm
        ((((c3.B.take n).reverse ++ c3.z ::
          ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn])) ++
          [c3.A.head c3.hA]) ++ [c3.ux])
        (c3.ux :: c3.A ++ c3.z :: c3.B) :=
      (hperm.append_right _).trans List.perm_append_comm
    have hnd2 := hperm2.nodup_iff.mpr hndS
    by_cases haux : G.Adj (c3.A.head c3.hA) c3.ux
    · -- `a₁–ux` red: blue-first bipath `(M, a₁, [ux])`, length `s+3`.
      have hbp : IsBipathB G X Y
          ((c3.B.take n).reverse ++ c3.z ::
            ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn]))
          (c3.A.head c3.hA) [c3.ux] := by
        refine ⟨hBlue, ?_,
          ((List.append_assoc _ _ _) ▸ hperm2).nodup_iff.mpr hndS⟩
        refine List.isChain_cons.mpr ⟨?_, List.isChain_singleton _⟩
        intro y hy
        rw [List.head?_singleton, Option.mem_some_iff] at hy
        subst hy
        exact ⟨Or.inr ⟨c3.hhead, c3.hux.1⟩, haux⟩
      have hbnd := c3.hmax _ _ _ (Or.inr hbp)
      simp only [bipathLen, List.length_append, List.length_cons,
        List.length_reverse, List.length_take, List.length_drop,
        List.length_nil] at hbnd
      omega
    · -- `a₁–ux` blue: blue-first bipath `(M ++ [a₁], ux, [])`, length `s+3`.
      have hBlue2 : ((((c3.B.take n).reverse ++ c3.z ::
          ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn])) ++
          [c3.A.head c3.hA]) ++ [c3.ux]).IsChain
          (Color.adjXY G X Y .blue) := by
        apply List.isChain_snoc' hBlue
        intro x hx
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
          List.getLast?_singleton, Option.mem_some_iff] at hx
        subst hx
        exact ⟨Or.inr ⟨c3.hhead, c3.hux.1⟩, haux⟩
      have hbp : IsBipathB G X Y
          (((c3.B.take n).reverse ++ c3.z ::
            ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn])) ++
            [c3.A.head c3.hA]) c3.ux [] := by
        refine ⟨hBlue2, List.isChain_singleton _, ?_⟩
        exact hperm2.nodup_iff.mpr hndS
      have hbnd := c3.hmax _ _ _ (Or.inr hbp)
      simp only [bipathLen, List.length_append, List.length_cons,
        List.length_reverse, List.length_take, List.length_drop,
        List.length_nil] at hbnd
      omega
  · -- `r ≥ 2`: equal-length blue-first bipath killed by `bipathO_kill_Ymid_B`.
    have hAt : c3.A.tail ≠ [] := by
      rw [List.ne_nil_iff_length_pos, List.length_tail]; omega
    have hbp : IsBipathB G X Y
        ((c3.B.take n).reverse ++ c3.z ::
          ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn]))
        (c3.A.head c3.hA) c3.A.tail := ⟨hBlue, hRed, hperm.nodup_iff.mpr hnd⟩
    have hmax' := hlen.symm ▸ c3.hmax
    have hMne : ((c3.B.take n).reverse ++ c3.z ::
        ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn])) ≠ [] :=
      fun h ↦ absurd (List.append_eq_nil_iff.mp h).1 hP1ne
    have hMhead : ((c3.B.take n).reverse ++ c3.z ::
        ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn])).head hMne =
        c3.B[n - 1]'(by omega) := by
      rw [List.head_append_left hP1ne hMne]
      have h : (c3.B.take n).reverse.head? =
          some (c3.B[n - 1]'(by omega)) := by
        rw [List.head?_reverse,
          getLast?_take (by omega : 0 < n) (by omega : n ≤ c3.B.length)]
      rw [List.head?_eq_some_head hP1ne] at h
      exact Option.some_inj.mp h
    have harY : c3.A.getLast c3.hA ∈ Y := by
      have harz := IsBipath.red_last_edge c3.hb c3.hA
      rcases harz.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h2 (Disjoint.notMem_left hXY c3.hz)
      · exact h1
    have hend1 : ((c3.B.take n).reverse ++ c3.z ::
        ((c3.B.drop (n + 1)).reverse ++ [c3.B[n]'hn])).head hMne ∈ Y := by
      rw [hMhead]
      exact B_mem_Y_of_even hXY c3 (by omega) (by omega)
    have hend2 : c3.A.tail.getLast hAt ∈ Y := by
      rw [List.getLast_tail hAt]; exact harY
    exact bipathO_kill_Ymid_B hXY hbp hmax'
      (fun hm ↦ c3.hux.2 (hperm.mem_iff.mp hm)) c3.hhead c3.hux.1
      hMne hAt hend1 hend2

/-! ### Claim F₂ -/

theorem claimF2 (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hE : c3.ClaimE) (hE' : c3.ClaimE') :
    ∀ l ∈ c3.SL, l ∈ c3.A → ∀ u ∈ c3.S2U, ¬ G.Adj l u := by
  intro l hlSL hlA u huS2 hadj
  obtain ⟨hlX, -⟩ := SL_mem hlSL
  obtain ⟨huB, huY⟩ := S2U_mem hXY huS2
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hlA
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp huB
  have hpar : p % 2 = 1 := A_odd_of_mem_X hXY c3 hp hlX
  have hqpar : q % 2 = 0 := B_even_of_mem_Y hXY c3 hq huY
  obtain ⟨hrodd, hsodd⟩ := c3.parity_len hXY
  have hredA : c3.A.IsChain (Color.adjXY G X Y .red) := c3.hb.1.left_of_append
  have hblueB : c3.B.IsChain (Color.adjXY G X Y .blue) := c3.hb.2.1.tail
  have hnd := c3.hb.2.2
  obtain ⟨hAz, -⟩ := claimA_of_case3 hXY c3
  have harz := IsBipath.red_last_edge c3.hb c3.hA
  have hpr : p + 1 < c3.A.length := by omega
  -- red side `A'' = A.drop(p+1) ++ z :: A.take(p+1)`
  have hDA : (c3.A.drop (p + 1)).IsChain (Color.adjXY G X Y .red) :=
    isChain_drop_of _ hredA
  have hTA : (c3.A.take (p + 1)).IsChain (Color.adjXY G X Y .red) :=
    isChain_take_of _ hredA
  have hDAne : c3.A.drop (p + 1) ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_drop]; omega
  have hTAne : c3.A.take (p + 1) ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_take]; omega
  have hTAlast : (c3.A.take (p + 1)).getLast? = some (c3.A[p]'hp) :=
    getLast?_take (by omega) (by omega)
  have hTAu : (c3.A.take (p + 1) ++ [c3.B[q]'hq]).IsChain
      (Color.adjXY G X Y .red) := by
    apply List.isChain_snoc' hTA
    intro x hx
    rw [hTAlast, Option.mem_some_iff] at hx
    subst hx
    exact ⟨Or.inl ⟨hlX, huY⟩, hadj⟩
  have hRed' : (c3.z :: (c3.A.take (p + 1) ++ [c3.B[q]'hq])).IsChain
      (Color.adjXY G X Y .red) := by
    refine List.isChain_cons.mpr ⟨?_, hTAu⟩
    intro y hy
    rw [List.head?_append_of_ne_nil _ hTAne,
      head?_take (by omega : 0 < p + 1) (by omega : p + 1 ≤ c3.A.length),
      List.head?_eq_some_head c3.hA, Option.mem_some_iff] at hy
    subst hy
    exact Color.adjXY.symm hAz
  have hRed'' : (c3.A.drop (p + 1) ++
      c3.z :: (c3.A.take (p + 1) ++ [c3.B[q]'hq])).IsChain
      (Color.adjXY G X Y .red) := by
    refine List.isChain_append.mpr ⟨hDA, hRed', ?_⟩
    intro x hx y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    rw [getLast?_drop hpr, Option.mem_some_iff] at hx
    subst hx
    rw [← List.getLast_eq_getElem]
    exact harz
  -- red branch `A'' ++ [u]`
  have hRed : ((c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) ++
      [c3.B[q]'hq]).IsChain (Color.adjXY G X Y .red) := by
    rw [List.append_assoc, List.cons_append]
    exact hRed''
  -- head of `A''` is `A[p+1] ∈ Y`
  have hA''ne : (c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) ≠ [] :=
    List.append_ne_nil_of_left_ne_nil hDAne _
  have hA''head : (c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)).head hA''ne
      ∈ Y := by
    rw [List.head_append_left hDAne hA''ne]
    have h : (c3.A.drop (p + 1)).head? = some (c3.A[p + 1]'hpr) :=
      head?_drop hpr
    rw [List.head?_eq_some_head hDAne] at h
    rw [Option.some_inj.mp h]
    exact A_mem_Y_of_even hXY c3 hpr (by omega)
  have hlen : bipathLen
      (c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) (c3.B[q]'hq)
      (c3.B.drop (q + 1) ++ (c3.B.take q).reverse) =
      bipathLen c3.A c3.z c3.B := by
    simp only [bipathLen, List.length_append, List.length_cons,
      List.length_reverse, List.length_take, List.length_drop, List.length_nil]
    rw [Nat.min_eq_left (by omega : p + 1 ≤ c3.A.length),
      Nat.min_eq_left (by omega : q ≤ c3.B.length)]
    omega
  have hDrop : (c3.B.drop (q + 1)).IsChain (Color.adjXY G X Y .blue) :=
    isChain_drop_of _ hblueB
  have hTR : (c3.B.take q).reverse.IsChain (Color.adjXY G X Y .blue) :=
    Color.adjXY.isChain_reverse (isChain_take_of q hblueB)
  rcases Nat.lt_or_ge c3.B.length 3 with hs3 | hs3
  · -- `s = 1`: `B = [u]`; the blue side is empty — extend via `ux`.
    have hs1 : c3.B.length = 1 := by omega
    have hq0 : q = 0 := by omega
    subst hq0
    have hb : c3.B = [c3.B[0]'hq] := by
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hs1
      have hhead : c3.B.head? = some b := by rw [hb]; rfl
      have hub : c3.B[0]'hq = b := by
        rw [(List.head_eq_getElem c3.hB).symm]
        exact Option.some_inj.mp
          ((List.head?_eq_some_head c3.hB).symm.trans hhead)
      rw [← hub] at hb
      exact hb
    have hndS : (c3.ux :: c3.A ++ c3.z :: c3.B).Nodup :=
      List.nodup_cons.mpr ⟨c3.hux.2, hnd⟩
    -- `A'' ++ u :: [ux] ~ ux :: A ++ z :: B`
    have hinner : List.Perm
        (c3.A.drop (p + 1) ++
          (c3.A.take (p + 1) ++ c3.B[0]'hq :: [c3.ux]))
        (c3.ux :: (c3.A ++ [c3.B[0]'hq])) := by
      refine ((List.perm_append_comm).append_left _).trans ?_
      -- `DA ++ ((u::[ux]) ++ TA)`
      refine (List.perm_append_comm).trans ?_
      -- `((u::[ux]) ++ TA) ++ DA`
      refine (List.Perm.of_eq (List.append_assoc _ _ _)).trans ?_
      -- `(u::[ux]) ++ (TA ++ DA)`
      refine (List.Perm.of_eq
        (congrArg _ (List.take_append_drop _ _))).trans ?_
      -- `(u::[ux]) ++ A`, i.e. `u :: ux :: A`
      rw [List.cons_append, List.cons_append, List.nil_append]
      refine (List.Perm.swap _ _ _).trans ?_
      -- `ux :: u :: A`
      exact (List.perm_append_comm (l₁ := [c3.B[0]'hq])
        (l₂ := c3.A)).cons _
    have hperm : List.Perm
        ((c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) ++
          c3.B[0]'hq :: [c3.ux])
        (c3.ux :: c3.A ++ c3.z :: c3.B) := by
      conv_rhs => rw [hb]
      rw [List.append_assoc, List.cons_append]
      exact (((List.perm_middle (a := c3.z) (l₁ := c3.A.drop (p + 1))
              (l₂ := c3.A.take (p + 1) ++ [c3.B[0]'hq, c3.ux])).trans
            (List.Perm.cons c3.z hinner)).trans
            (List.Perm.swap c3.ux c3.z (c3.A ++ [c3.B[0]'hq]))).trans
          (List.Perm.cons c3.ux
            (List.perm_middle (a := c3.z) (l₁ := c3.A)
              (l₂ := [c3.B[0]'hq])).symm)
    have hperm2 : List.Perm
        (((c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) ++ [c3.B[0]'hq]) ++
          c3.ux :: [])
        (c3.ux :: c3.A ++ c3.z :: c3.B) :=
      (List.Perm.of_eq (List.append_assoc _ _ _)).trans hperm
    by_cases haux : G.Adj (c3.B[0]'hq) c3.ux
    · -- `u–ux` red: `IsBipath (A'' ++ [u]) ux []`, length `r+3`.
      have hRed2 : (((c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) ++
          [c3.B[0]'hq]) ++ [c3.ux]).IsChain
          (Color.adjXY G X Y .red) := by
        apply List.isChain_snoc' hRed
        intro x hx
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
          List.getLast?_singleton, Option.mem_some_iff] at hx
        subst hx
        exact ⟨Or.inr ⟨huY, c3.hux.1⟩, haux⟩
      have hbp : IsBipath G X Y
          ((c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) ++ [c3.B[0]'hq])
          c3.ux [] :=
        ⟨hRed2, List.isChain_singleton _, hperm2.nodup_iff.mpr hndS⟩
      have hbnd := c3.hmax _ _ _ (Or.inl hbp)
      simp only [bipathLen, List.length_append, List.length_cons,
        List.length_reverse, List.length_take, List.length_drop,
        List.length_nil] at hbnd
      rw [Nat.min_eq_left (by omega : p + 1 ≤ c3.A.length)] at hbnd
      omega
    · -- `u–ux` blue: `IsBipath A'' u [ux]`, length `r+3`.
      have hBlu : (c3.B[0]'hq :: [c3.ux]).IsChain
          (Color.adjXY G X Y .blue) := by
        refine List.isChain_cons.mpr ⟨?_, List.isChain_singleton _⟩
        intro y hy
        rw [List.head?_singleton, Option.mem_some_iff] at hy
        subst hy
        exact ⟨Or.inr ⟨huY, c3.hux.1⟩, haux⟩
      have hbp : IsBipath G X Y
          (c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) (c3.B[0]'hq)
          [c3.ux] := ⟨hRed, hBlu, hperm.nodup_iff.mpr hndS⟩
      have hbnd := c3.hmax _ _ _ (Or.inl hbp)
      simp only [bipathLen, List.length_append, List.length_cons,
        List.length_reverse, List.length_take, List.length_drop,
        List.length_nil] at hbnd
      rw [Nat.min_eq_left (by omega : p + 1 ≤ c3.A.length)] at hbnd
      omega
  · -- `s ≥ 3`
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · -- `q = 0`: `u = b₁`; blue side `u :: B.drop 1 = B`.
      subst hq0
      have hD1ne : c3.B.drop 1 ≠ [] := by
        rw [List.ne_nil_iff_length_pos, List.length_drop]; omega
      have hBlue : (c3.B[0]'hq :: c3.B.drop 1).IsChain
          (Color.adjXY G X Y .blue) := by
        refine List.isChain_cons.mpr ⟨?_, isChain_drop_of 1 hblueB⟩
        intro y hy
        rw [head?_drop (by omega : 1 < c3.B.length), Option.mem_some_iff] at hy
        subst hy
        exact (List.isChain_iff_getElem.mp hblueB) 0 (by omega)
      have hgl : (c3.B.drop 1).getLast hD1ne ∈ Y := by
        have h : (c3.B.drop 1).getLast? = some (c3.B.getLast c3.hB) := by
          rw [getLast?_drop (by omega : 1 < c3.B.length)]
          congr 1
          exact (List.getLast_eq_getElem c3.hB).symm
        have e := Option.some_inj.mp ((List.getLast?_eq_some_getLast hD1ne).symm.trans h)
        rw [e]; exact c3.hlast
      have hcons : c3.B[0]'hq :: c3.B.drop 1 = c3.B := by
        rw [List.drop_one]
        conv_rhs => rw [← List.cons_head_tail c3.hB]
        congr 1
        exact (List.head_eq_getElem c3.hB).symm
      have hperm : List.Perm
          ((c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) ++
            c3.B[0]'hq :: c3.B.drop 1)
          (c3.A ++ c3.z :: c3.B) := by
        rw [hcons, List.append_assoc, List.cons_append]
        refine (List.perm_middle.trans (List.Perm.cons c3.z ?_)).trans
          List.perm_middle.symm
        -- `DA ++ (TA ++ B) ~ A ++ B`
        exact (List.Perm.of_eq (List.append_assoc _ _ _).symm).trans
          (((List.perm_append_comm).trans
            (List.Perm.of_eq (List.take_append_drop _ _))).append_right _)
      have hlen0 : bipathLen
          (c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) (c3.B[0]'hq)
          (c3.B.drop 1) = bipathLen c3.A c3.z c3.B := by
        simp only [bipathLen, List.length_append, List.length_cons,
          List.length_reverse, List.length_take, List.length_drop,
          List.length_nil]
        rw [Nat.min_eq_left (by omega : p + 1 ≤ c3.A.length)]
        omega
      have hbp : IsBipath G X Y
          (c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) (c3.B[0]'hq)
          (c3.B.drop 1) := ⟨hRed, hBlue, hperm.nodup_iff.mpr hnd⟩
      have hmax' := hlen0.symm ▸ c3.hmax
      exact bipathO_kill_Ymid hXY hbp hmax'
        (fun hm ↦ c3.hux.2 (hperm.mem_iff.mp hm)) huY c3.hux.1
        hA''ne hD1ne hA''head hgl
    · -- `q ≥ 2` (even): blue side `u :: drop(q+1) ++ (take q).reverse`.
      have hq2 : 2 ≤ q := by omega
      have hTRne : (c3.B.take q).reverse ≠ [] := by
        rw [List.reverse_ne_nil_iff, List.ne_nil_iff_length_pos,
          List.length_take]; omega
      have hB''ne : (c3.B.drop (q + 1) ++ (c3.B.take q).reverse) ≠ [] :=
        List.append_ne_nil_of_right_ne_nil _ hTRne
      have hJ : ∀ x ∈ (c3.B.drop (q + 1)).getLast?,
          ∀ y ∈ (c3.B.take q).reverse.head?,
          Color.adjXY G X Y .blue x y := by
        intro x hx y hy
        have hq1 : q + 1 < c3.B.length := by
          by_contra h'
          have hd : c3.B.drop (q + 1) = [] := by
            rw [List.drop_eq_nil_iff]; omega
          rw [hd, List.getLast?_nil] at hx; simp at hx
        rw [getLast?_drop hq1, Option.mem_some_iff] at hx
        rw [List.head?_reverse,
          getLast?_take (by omega : 0 < q) (by omega : q ≤ c3.B.length),
          Option.mem_some_iff] at hy
        subst hx; subst hy
        rw [← List.getLast_eq_getElem c3.hB]
        exact ⟨Or.inr ⟨c3.hlast,
            B_mem_X_of_odd hXY c3 (by omega) (by omega)⟩,
          hE' (c3.B.getLast c3.hB)
            (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
              (List.mem_cons_of_mem _ (List.getLast_mem c3.hB)), c3.hlast⟩)
            (c3.B[q - 1]'(by omega))
            (SL_of_mem_B (List.getElem_mem _)
              (B_mem_X_of_odd hXY c3 (by omega) (by omega)))
            (Or.inl (List.getElem_mem _))⟩
      have hBlue : (c3.B[q]'hq ::
          (c3.B.drop (q + 1) ++ (c3.B.take q).reverse)).IsChain
          (Color.adjXY G X Y .blue) := by
        refine List.isChain_cons.mpr ⟨?_,
          List.isChain_append.mpr ⟨hDrop, hTR, hJ⟩⟩
        intro y hy
        rcases eq_or_ne (c3.B.drop (q + 1)) [] with hd | hd
        · rw [hd, List.nil_append, List.head?_reverse,
            getLast?_take (by omega : 0 < q) (by omega : q ≤ c3.B.length),
            Option.mem_some_iff] at hy
          subst hy
          have e : Color.adjXY G X Y .blue (c3.B[q - 1]'(by omega)) (c3.B[q]'hq) := by
            simpa only [show q - 1 + 1 = q by omega]
              using (List.isChain_iff_getElem.mp hblueB) (q - 1) (by omega)
          exact Color.adjXY.symm e
        · have hq1 : q + 1 < c3.B.length := by
            have h' := List.ne_nil_iff_length_pos.mp hd
            rw [List.length_drop] at h'; omega
          rw [List.head?_append_of_ne_nil _ hd, head?_drop hq1,
            Option.mem_some_iff] at hy
          subst hy
          exact (List.isChain_iff_getElem.mp hblueB) q hq1
      have huB : List.Perm
          (c3.B[q]'hq ::
            (c3.B.drop (q + 1) ++ (c3.B.take q).reverse)) c3.B := by
        rw [← List.cons_append, ← List.drop_eq_getElem_cons hq]
        exact ((List.perm_append_comm).trans
          ((List.reverse_perm _).append_right _)).trans
          (List.Perm.of_eq (List.take_append_drop _ _))
      have hperm : List.Perm
          ((c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) ++
            c3.B[q]'hq :: (c3.B.drop (q + 1) ++ (c3.B.take q).reverse))
          (c3.A ++ c3.z :: c3.B) := by
        rw [List.append_assoc, List.cons_append]
        refine (List.perm_middle.trans (List.Perm.cons c3.z ?_)).trans
          List.perm_middle.symm
        -- `DA ++ (TA ++ uB'') ~ A ++ B`
        refine ((List.perm_append_comm).append_left _).trans ?_
        -- `DA ++ (uB'' ++ TA)`
        refine (List.Perm.of_eq (List.append_assoc _ _ _).symm).trans ?_
        -- `(DA ++ uB'') ++ TA`
        refine ((List.perm_append_comm).append_right _).trans ?_
        -- `(uB'' ++ DA) ++ TA`
        refine (List.Perm.of_eq (List.append_assoc _ _ _)).trans ?_
        -- `uB'' ++ (DA ++ TA)`
        refine ((List.perm_append_comm).append_left _).trans ?_
        -- `uB'' ++ (TA ++ DA)`
        rw [List.take_append_drop]
        -- `uB'' ++ A ~ A ++ B`
        exact (List.perm_append_comm).trans (huB.append_left _)
      have hgl : (c3.B.drop (q + 1) ++ (c3.B.take q).reverse).getLast hB''ne
          ∈ Y := by
        have h : (c3.B.drop (q + 1) ++ (c3.B.take q).reverse).getLast? =
            some (c3.B.head c3.hB) := by
          rw [List.getLast?_append_of_ne_nil _ hTRne, List.getLast?_reverse,
            head?_take (by omega : 0 < q) (by omega : q ≤ c3.B.length),
            List.head?_eq_some_head c3.hB]
        have e := Option.some_inj.mp ((List.getLast?_eq_some_getLast hB''ne).symm.trans h)
        rw [e]; exact B_head_mem_Y hXY c3
      have hbp : IsBipath G X Y
          (c3.A.drop (p + 1) ++ c3.z :: c3.A.take (p + 1)) (c3.B[q]'hq)
          (c3.B.drop (q + 1) ++ (c3.B.take q).reverse) :=
        ⟨hRed, hBlue, hperm.nodup_iff.mpr hnd⟩
      have hmax' := hlen.symm ▸ c3.hmax
      exact bipathO_kill_Ymid hXY hbp hmax'
        (fun hm ↦ c3.hux.2 (hperm.mem_iff.mp hm)) huY c3.hux.1
        hA''ne hB''ne hA''head hgl

end JSP415
