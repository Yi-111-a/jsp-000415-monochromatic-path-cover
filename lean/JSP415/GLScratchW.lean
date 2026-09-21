import JSP415.GLIface
import JSP415.GLScratchA

/-!
# Coordinator file: swapped killing lemmas + claim-A recovery

The BipLemmas killing lemmas require a maximal `IsBipath` whose midpoint
lies in `X` and a leftover in `Y`.  Rotations of a maximal bipath often put
the midpoint in `Y` with a leftover in `X` instead — the X↔Y-swapped
versions below handle that.  Consequences (`claimA_leftover_X`): even in the
`U ⊆ X` subcase (no `Y`-leftover), maximality forces `a₁–z` red and `z–bₛ`
blue — the "claim A" edges of the GL argument.
-/

open Finset
open Classical

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

/-- X↔Y-swapped form of `bipathO_leftover_opp_of_same_ends`: midpoint and
endpoints in `Y`, leftover in `X`. -/
theorem bipathO_kill_Ymid (hXY : Disjoint X Y)
    {A : List V} {z : V} {B : List V}
    (hb : IsBipath G X Y A z B)
    (hmax : ∀ A' z' B', IsBipathO G X Y A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B)
    {u : V} (hu : u ∉ A ++ z :: B) (hz : z ∈ Y) (huX : u ∈ X)
    (hA : A ≠ []) (hB : B ≠ [])
    (haY : A.head hA ∈ Y) (hbY : B.getLast hB ∈ Y) : False := by
  have hb' : IsBipath G Y X A z B := isBipath_swapXY.mp hb
  have hmax' : ∀ A' z' B', IsBipathO G Y X A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B :=
    fun A' z' B' h ↦ hmax A' z' B' (isBipathO_swapXY.mpr h)
  exact bipathO_leftover_opp_of_same_ends hXY.symm hb' hmax' hu hz huX hA hB haY hbY

/-- The `IsBipathB` (blue-first) version of `bipathO_kill_Ymid`, via the
complement colouring. -/
theorem bipathO_kill_Ymid_B (hXY : Disjoint X Y)
    {A : List V} {z : V} {B : List V}
    (hb : IsBipathB G X Y A z B)
    (hmax : ∀ A' z' B', IsBipathO G X Y A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B)
    {u : V} (hu : u ∉ A ++ z :: B) (hz : z ∈ Y) (huX : u ∈ X)
    (hA : A ≠ []) (hB : B ≠ [])
    (haY : A.head hA ∈ Y) (hbY : B.getLast hB ∈ Y) : False := by
  have hb' : IsBipath Gᶜ Y X A z B :=
    isBipath_swapXY.mp (IsBipathB.to_compl hXY hb)
  have hmax' : ∀ A' z' B', IsBipathO Gᶜ Y X A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B := by
    intro A' z' B' h
    rcases h with h | h
    · exact hmax A' z' B'
        (Or.inr (isBipathB_swapXY.mpr (IsBipath.of_compl hXY.symm h)))
    · exact hmax A' z' B'
        (Or.inl (isBipath_swapXY.mpr (IsBipathB.of_compl hXY.symm h)))
  exact bipathO_leftover_opp_of_same_ends hXY.symm hb' hmax' hu hz huX hA hB
    haY hbY

/-- **Claim A (i), leftover-`X` version.**  For a maximal red-first bipath
with endpoints in `Y`, midpoint `z ∈ X`, and a leftover `u ∈ X`, the edge
`A.head–z` is red; else the rotation `S' = (A.tail.reverse, A.head, z::B)`
is an equal-length — hence maximal — bipath of the killed type (ii). -/
theorem claimA_head_mid_red (hXY : Disjoint X Y)
    {A : List V} {z : V} {B : List V}
    (hb : IsBipath G X Y A z B)
    (hmax : ∀ A' z' B', IsBipathO G X Y A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B)
    {u : V} (hu : u ∉ A ++ z :: B) (huX : u ∈ X)
    (hz : z ∈ X) (hA : A ≠ []) (hB : B ≠ [])
    (haY : A.head hA ∈ Y) (hbY : B.getLast hB ∈ Y)
    (hA2 : 2 ≤ A.length) :
    Color.adjXY G X Y .red (A.head hA) z := by
  have harz := IsBipath.red_last_edge hb hA
  obtain ⟨hred, hblue, hnd⟩ := hb
  set a₁ := A.head hA
  have hAt : A.tail ≠ [] := by
    intro e
    have hlen := congrArg List.length e
    simp only [List.length_tail, List.length_nil] at hlen
    omega
  have hAtail : A.tail.reverse ++ [a₁] = A.reverse := by
    conv_rhs => rw [← List.cons_head_tail hA, List.reverse_cons]
  rcases Color.adjXY_cases (show acrossXY X Y a₁ z from Or.inr ⟨haY, hz⟩)
    with haz | haz
  · exact haz
  · -- `a₁–z` blue: the rotation `S' = (A.tail.reverse, a₁, z::B)` is an
    -- equal-length bipath with midpoint and endpoints in `Y` — killed.
    exfalso
    have hArev : (A.tail.reverse ++ [a₁]).IsChain
        (Color.adjXY G X Y .red) := by
      rw [hAtail]
      exact Color.adjXY.isChain_reverse hred.left_of_append
    have hblue' : (a₁ :: z :: B).IsChain (Color.adjXY G X Y .blue) := by
      rw [List.isChain_cons]
      refine ⟨fun y hy ↦ ?_, hblue⟩
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hy; exact haz
    have hp : List.Perm (A.tail.reverse ++ a₁ :: z :: B) (A ++ z :: B) := by
      have h1 : List.Perm (A.tail.reverse ++ a₁ :: z :: B)
          ((A.tail.reverse ++ [a₁]) ++ z :: B) :=
        (List.append_assoc _ _ _).symm ▸ List.Perm.refl _
      rw [hAtail] at h1
      exact h1.trans ((List.reverse_perm A).append_right _)
    have hnd' : (A.tail.reverse ++ a₁ :: z :: B).Nodup :=
      hp.nodup_iff.mpr hnd
    have hbS' : IsBipath G X Y A.tail.reverse a₁ (z :: B) :=
      ⟨hArev, hblue', hnd'⟩
    have hlen : bipathLen A.tail.reverse a₁ (z :: B) = bipathLen A z B := by
      simp [bipathLen]; omega
    have hmax' := hlen.symm ▸ hmax
    have harY : A.getLast hA ∈ Y := by
      rcases harz.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h2 (Disjoint.notMem_left hXY hz)
      · exact h1
    have hAtr : A.tail.reverse ≠ [] := List.reverse_ne_nil_iff.mpr hAt
    have hzB : z :: B ≠ [] := List.cons_ne_nil _ _
    have hthead : (A.tail.reverse).head hAtr = A.getLast hA := by
      rw [List.head_reverse, List.getLast_tail]
    have hblast : (z :: B).getLast hzB = B.getLast hB :=
      List.getLast_cons hB
    have hend1 : (A.tail.reverse).head hAtr ∈ Y := hthead ▸ harY
    have hend2 : (z :: B).getLast hzB ∈ Y := hblast ▸ hbY
    exact bipathO_kill_Ymid hXY hbS' hmax'
      (fun hm ↦ hu (hp.mem_iff.mp hm)) haY huX hAtr hzB hend1 hend2

/-- **Claim A (ii), leftover-`X` version.**  In the same configuration, the
edge `z–B.getLast` is blue; else `S' = (A ++ [z], B.getLast,
B.dropLast.reverse)` (list `A ++ z :: B.reverse`) is an equal-length killed
bipath. -/
theorem claimA_mid_last_blue (hXY : Disjoint X Y)
    {A : List V} {z : V} {B : List V}
    (hb : IsBipath G X Y A z B)
    (hmax : ∀ A' z' B', IsBipathO G X Y A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A z B)
    {u : V} (hu : u ∉ A ++ z :: B) (huX : u ∈ X)
    (hz : z ∈ X) (hA : A ≠ []) (hB : B ≠ [])
    (haY : A.head hA ∈ Y) (hbY : B.getLast hB ∈ Y)
    (hB2 : 2 ≤ B.length) :
    Color.adjXY G X Y .blue z (B.getLast hB) := by
  have hzb1 := IsBipath.blue_first_edge hb hB
  obtain ⟨hred, hblue, hnd⟩ := hb
  set bₛ := B.getLast hB
  have hBsnoc : B.dropLast ++ [bₛ] = B :=
    List.dropLast_append_getLast? _
      (by rw [List.getLast?_eq_getLast_of_ne_nil hB]
          exact Option.mem_some_iff.mpr rfl)
  have hBrev_eq : B.reverse = bₛ :: B.dropLast.reverse := by
    conv_lhs => rw [← hBsnoc]
    simp
  have hBt : B.dropLast ≠ [] := by
    intro e
    have hlen := congrArg List.length e
    simp only [List.length_dropLast, List.length_nil] at hlen
    omega
  have hBrev : B.reverse.IsChain (Color.adjXY G X Y .blue) :=
    Color.adjXY.isChain_reverse hblue.tail
  rcases Color.adjXY_cases (show acrossXY X Y z bₛ from Or.inl ⟨hz, hbY⟩)
    with hzb | hzb
  · -- `z–bₛ` red: the rotation `S' = (A++[z], bₛ, B.dropLast.reverse)` is
    -- an equal-length bipath with midpoint and endpoints in `Y` — killed.
    exfalso
    have hred' : ((A ++ [z]) ++ [bₛ]).IsChain (Color.adjXY G X Y .red) := by
      rw [List.isChain_append]
      refine ⟨hred, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
        List.getLast?_singleton] at hx
      rw [List.head?_singleton] at hy
      simp only [Option.mem_some_iff] at hx hy
      subst hx; subst hy; exact hzb
    have hblue' : (bₛ :: B.dropLast.reverse).IsChain
        (Color.adjXY G X Y .blue) := by
      rw [← hBrev_eq]; exact hBrev
    have hp : List.Perm ((A ++ [z]) ++ bₛ :: B.dropLast.reverse)
        (A ++ z :: B) := by
      rw [← hBrev_eq, List.append_assoc]
      exact ((List.reverse_perm B).cons z).append_left A
    have hnd' : ((A ++ [z]) ++ bₛ :: B.dropLast.reverse).Nodup :=
      hp.nodup_iff.mpr hnd
    have hbS' : IsBipath G X Y (A ++ [z]) bₛ B.dropLast.reverse :=
      ⟨hred', hblue', hnd'⟩
    have hlen : bipathLen (A ++ [z]) bₛ B.dropLast.reverse =
        bipathLen A z B := by
      simp only [bipathLen, List.length_append, List.length_cons,
        List.length_reverse, List.length_dropLast, List.length_nil]
      omega
    have hmax' := hlen.symm ▸ hmax
    have hAz' : A ++ [z] ≠ [] :=
      fun e ↦ absurd (List.append_eq_nil_iff.mp e).1 hA
    have hBdr : B.dropLast.reverse ≠ [] := List.reverse_ne_nil_iff.mpr hBt
    have hAhd : (A ++ [z]).head hAz' = A.head hA := by
      have e1 : (A ++ [z]).head? = A.head? :=
        List.head?_append_of_ne_nil _ hA
      rw [List.head?_eq_some_head hAz', List.head?_eq_some_head hA] at e1
      exact Option.some.inj e1
    have hb1 : B.dropLast.reverse.getLast hBdr = B.head hB := by
      rw [List.getLast_reverse, List.head_dropLast]
    have hb1Y : B.head hB ∈ Y := by
      rcases hzb1.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact absurd h1 (Disjoint.notMem_left hXY hz)
    have hend1 : (A ++ [z]).head hAz' ∈ Y := hAhd ▸ haY
    have hend2 : B.dropLast.reverse.getLast hBdr ∈ Y := hb1 ▸ hb1Y
    exact bipathO_kill_Ymid hXY hbS' hmax'
      (fun hm ↦ hu (hp.mem_iff.mp hm)) hbY huX hAz' hBdr hend1 hend2
  · exact hzb

/-- **Claim A** for the case-(iii) configuration: both outer edges are
forced — `A.head–z` is red and `z–B.getLast` is blue.  The length-1 branches
(`A = [a]`, `B = [b]`) are exactly the last red / first blue edges of the
bipath itself; the length-≥2 branches are the rotation arguments. -/
theorem claimA_of_case3 (hXY : Disjoint X Y) (c3 : Case3Data G X Y) :
    c3.ClaimA := by
  obtain ⟨A, z, B, hb, hmax, hz, hA, hB, hhead, hlast, ux, hux⟩ := c3
  show Color.adjXY G X Y .red (A.head hA) z ∧
    Color.adjXY G X Y .blue z (B.getLast hB)
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge A.length 2 with hlen | hlen
    · have h1 : A.length = 1 := by
        have := List.length_pos_of_ne_nil hA; omega
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h1
      exact IsBipath.red_last_edge hb hA
    · exact claimA_head_mid_red hXY hb hmax hux.2 hux.1 hz hA hB
        hhead hlast hlen
  · rcases Nat.lt_or_ge B.length 2 with hlen | hlen
    · have h1 : B.length = 1 := by
        have := List.length_pos_of_ne_nil hB; omega
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp h1
      exact IsBipath.blue_first_edge hb hB
    · exact claimA_mid_last_blue hXY hb hmax hux.2 hux.1 hz hA hB
        hhead hlast hlen

end JSP415
