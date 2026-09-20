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
  obtain ⟨hred, hblue, hnd⟩ := hb
  have huz : acrossXY X Y (A.head hA) z := Or.inr ⟨haY, hz⟩
  rcases Color.adjXY_cases huz with h | h
  · exact h
  exfalso
  have hAt : A.tail ≠ [] := by
    intro e
    have hlen := congrArg List.length e
    rw [List.length_tail, List.length_nil] at hlen
    omega
  have hcons : A.head hA :: A.tail = A := List.cons_head_tail hA
  have hArev : (A.tail.reverse ++ [A.head hA]).IsChain
      (Color.adjXY G X Y .red) := by
    have h1 : (A.tail.reverse).IsChain (Color.adjXY G X Y .red) :=
      Color.adjXY.isChain_reverse (List.isChain_append.mp hred).1.tail
    rw [List.isChain_append]
    refine ⟨h1, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
    rw [List.getLast?_reverse] at hx
    simp only [List.head?_eq_head hAt, List.head?_cons,
      Option.mem_some_iff] at hx hy
    subst hx; subst hy
    have h2 : (A.head hA :: A.tail).IsChain (Color.adjXY G X Y .red) := by
      rw [hcons]; exact (List.isChain_append.mp hred).1
    rw [List.isChain_cons] at h2
    exact h2.1 _ (by
      rw [List.head?_eq_head hAt]; exact Option.mem_some_iff.mpr rfl)
  have hblue' : (A.head hA :: z :: B).IsChain (Color.adjXY G X Y .blue) := by
    rw [List.isChain_cons]
    refine ⟨fun y hy ↦ ?_, hblue⟩
    simp only [List.head?_cons, Option.mem_some_iff] at hy
    subst hy; exact h
  have e : A.tail.reverse ++ [A.head hA] = A.reverse := by
    rw [← hcons, List.reverse_cons]
  have hp : List.Perm (A.tail.reverse ++ A.head hA :: z :: B)
      (A ++ z :: B) := by
    rw [show A.tail.reverse ++ A.head hA :: z :: B =
        (A.tail.reverse ++ [A.head hA]) ++ z :: B from List.append_assoc ..]
    rw [e]
    exact (List.reverse_perm A).append_right _
  have hnd' : (A.tail.reverse ++ A.head hA :: z :: B).Nodup :=
    hp.nodup_iff.mpr hnd
  have hbS' : IsBipath G X Y A.tail.reverse (A.head hA) (z :: B) :=
    ⟨hArev, hblue', hnd'⟩
  have hlen : bipathLen A.tail.reverse (A.head hA) (z :: B) =
      bipathLen A z B := by
    simp only [bipathLen, List.length_reverse, List.length_tail,
      List.length_cons]
    omega
  have hmax' : ∀ A' z' B', IsBipathO G X Y A' z' B' →
      bipathLen A' z' B' ≤ bipathLen A.tail.reverse (A.head hA) (z :: B) :=
    fun A' z' B' h ↦ hlen ▸ hmax A' z' B' h
  have harY : A.getLast hA ∈ Y := by
    have hla := IsBipath.red_last_edge hb hA
    rcases hla.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h2 (Disjoint.notMem_right hXY hz)
    · exact h1
  have hdro : A.reverse.dropLast = A.tail.reverse := by
    conv_lhs => rw [← hcons, List.reverse_cons]
    simp
  have hthead : (A.tail.reverse).head (List.reverse_ne_nil_iff.mpr hAt) =
      A.getLast hA := by
    rw [← hdro, List.head_dropLast, List.head_reverse]
  have hblast : (z :: B).getLast (List.cons_ne_nil _ _) = B.getLast hB := by
    simp [List.getLast_cons hB]
  exact bipathO_kill_Ymid hXY hbS' hmax'
    (fun hm ↦ hu (hp.mem_iff.mp hm)) haY huX
    (List.reverse_ne_nil_iff.mpr hAt) (List.cons_ne_nil _ _)
    (hthead ▸ harY) (hblast ▸ hbY)

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
  obtain ⟨hred, hblue, hnd⟩ := hb
  have huz : acrossXY X Y z (B.getLast hB) := Or.inl ⟨hz, hbY⟩
  rcases Color.adjXY_cases huz with h | h
  swap
  · exact h
  exfalso
  obtain ⟨hacr, hadj⟩ := h
  have hAz : (A ++ [z] ++ [B.getLast hB]).IsChain
      (Color.adjXY G X Y .red) := by
    rw [List.isChain_append]
    refine ⟨(List.isChain_append.mp hred).1, ?_, ?_⟩
    · rw [List.isChain_cons]
      refine ⟨fun y hy ↦ ?_, List.isChain_singleton _⟩
      simp only [List.head?_singleton, Option.mem_some_iff] at hy
      subst hy
      exact ⟨hacr, hadj⟩
    · intro x hx y hy
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hy
      exact (List.isChain_append.mp hred).2.2 x hx y
        (Option.mem_some_iff.mpr rfl)
  have hBrev : B.reverse.IsChain (Color.adjXY G X Y .blue) :=
    Color.adjXY.isChain_reverse hblue.tail
  have hBsnoc : B.dropLast ++ [B.getLast hB] = B :=
    List.dropLast_append_getLast? _
      (by rw [List.getLast?_eq_getLast_of_ne_nil hB]
          exact Option.mem_some_iff.mpr rfl)
  have hBcons : B.getLast hB :: B.dropLast.reverse = B.reverse := by
    conv_rhs => rw [← hBsnoc, List.reverse_append, List.reverse_singleton]
  have hBrev' : (B.getLast hB :: B.dropLast.reverse).IsChain
      (Color.adjXY G X Y .blue) := hBcons ▸ hBrev
  have hp : List.Perm (A ++ ([z] ++ B.getLast hB :: B.dropLast.reverse))
      (A ++ z :: B) := by
    have e : A ++ ([z] ++ B.getLast hB :: B.dropLast.reverse) =
        A ++ z :: B.reverse :=
      congrArg (A ++ ·) (congrArg (z :: ·) hBcons)
    exact e ▸ ((List.reverse_perm B).cons z).append_left A
  have hnd' : (A ++ [z] ++ B.getLast hB :: B.dropLast.reverse).Nodup :=
    hp.nodup_iff.mpr hnd
  have hred' : ((A ++ [z]) ++ [B.getLast hB]).IsChain
      (Color.adjXY G X Y .red) := by
    rw [List.append_assoc]; exact hAz
  have hnd'' : ((A ++ [z]) ++ B.getLast hB :: B.dropLast.reverse).Nodup := by
    rw [List.append_assoc]; exact hnd'
  have hbS' : IsBipath G X Y (A ++ [z]) (B.getLast hB) B.dropLast.reverse :=
    ⟨hred', hBrev', hnd''⟩
  have hlen : bipathLen (A ++ [z]) (B.getLast hB) B.dropLast.reverse =
      bipathLen A z B := by
    simp only [bipathLen, List.length_append, List.length_cons,
      List.length_reverse, List.length_dropLast, List.length_nil]
    omega
  have hmax' : ∀ A' z' B', IsBipathO G X Y A' z' B' →
      bipathLen A' z' B' ≤
        bipathLen (A ++ [z]) (B.getLast hB) B.dropLast.reverse :=
    fun A' z' B' h ↦ hlen ▸ hmax A' z' B' h
  have hAz' : A ++ [z] ≠ [] :=
    fun e ↦ absurd (List.append_eq_nil_iff.mp e).1 hA
  have hBdr : B.dropLast.reverse ≠ [] := by
    rwa [List.reverse_ne_nil_iff]
  have hAhd : (A ++ [z]).head hAz' = A.head hA := by
    have e1 : (A ++ [z]).head? = A.head? := by
      rw [List.head?_append_of_ne_nil _ hA]
    rw [List.head?_eq_head hAz', List.head?_eq_head hA] at e1
    exact Option.some.inj e1
  have hb1 : B.dropLast.reverse.getLast hBdr = B.head hB :=
    (List.getLast_reverse hBdr).trans (List.head_dropLast _)
  have hb1Y : B.head hB ∈ Y := by
    have hfb := IsBipath.blue_first_edge hb hB
    rcases hfb.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd h1 (Disjoint.notMem_right hXY hz)
  exact bipathO_kill_Ymid hXY hbS' hmax'
    (fun hm ↦ hu (hp.mem_iff.mp hm)) hbY huX
    hAz' hBdr
    (hAhd ▸ haY) (hb1 ▸ hb1Y)

end JSP415
