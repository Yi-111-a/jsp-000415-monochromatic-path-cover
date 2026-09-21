import JSP415.GLScratchE3

open Finset
open Classical
open scoped List

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

namespace Case3Data

/-- The `A`-reversed case-3 datum: `S' = A.reverse ++ z :: B`.  Reversing the
red branch preserves the red chain (`adjXY` is symmetric) with junction edge
`A[r-1]–z` replaced by `z–A[0]` (`za1red`); the blue branch `z :: B` is
unchanged; the vertex list is a permutation of the original, so maximality,
nodup, endpoints and the leftover all transport. -/
def revCase3 (c3 : Case3Data G X Y) (hXY : Disjoint X Y) : Case3Data G X Y where
  A := c3.A.reverse
  z := c3.z
  B := c3.B
  hb := by
    have hgl : c3.A.reverse.getLast? = some (c3.A.head c3.hA) := by
      rw [List.getLast?_reverse, List.head?_eq_some_head]
    have hR : (c3.A.reverse ++ [c3.z]).IsChain (Color.adjXY G X Y .red) :=
      chain_app (Color.adjXY.isChain_reverse (chainA c3))
        (List.isChain_singleton _)
        (junc hgl rfl (Color.adjXY.symm (za1red c3 hXY)))
    have hnd' : (c3.A.reverse ++ c3.z :: c3.B).Nodup :=
      ((List.reverse_perm c3.A).append_right _).nodup_iff.mpr (hnd c3)
    exact ⟨hR, blueChain c3, hnd'⟩
  hmax := fun A' z' B' h ↦ (c3.hmax A' z' B' h).trans
    (le_of_eq (by simp only [bipathLen, List.length_reverse]))
  hz := c3.hz
  hA := List.reverse_ne_nil_iff.mpr c3.hA
  hB := c3.hB
  hhead := by
    rw [List.head_reverse, List.getLast_eq_getElem]
    have hro : c3.A.length % 2 = 1 := c3.r_odd hXY
    exact (c3.a_side hXY (c3.A.length - 1)
      (Nat.sub_lt (List.length_pos_of_ne_nil c3.hA) Nat.one_pos)).1.mpr (by omega)
  hlast := c3.hlast
  ux := c3.ux
  hux := ⟨c3.ux_X, fun h ↦
    c3.ux_not_mem (((List.reverse_perm c3.A).append_right _).mem_iff.mp h)⟩

/-- The `X`-side finset of the vertex list is unchanged by `A`-reversal. -/
theorem revCase3_SL (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    (revCase3 c3 hXY).SL = c3.SL := by
  have hperm : List.Perm (c3.A.reverse ++ c3.z :: c3.B)
      (c3.A ++ c3.z :: c3.B) := (List.reverse_perm _).append_right _
  have hts : (c3.A.reverse ++ c3.z :: c3.B).toFinset =
      (c3.A ++ c3.z :: c3.B).toFinset := by
    ext x
    simp only [List.mem_toFinset]
    exact hperm.mem_iff
  show (c3.A.reverse ++ c3.z :: c3.B).toFinset.filter (· ∈ X) = c3.SL
  rw [hts]

/-- The `Y`-side finset of the red branch is unchanged by `A`-reversal. -/
theorem revCase3_S1U (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    (revCase3 c3 hXY).S1U = c3.S1U := by
  have hperm : List.Perm (c3.A.reverse ++ [c3.z]) (c3.A ++ [c3.z]) :=
    (List.reverse_perm _).append_right _
  have hts : (c3.A.reverse ++ [c3.z]).toFinset = (c3.A ++ [c3.z]).toFinset := by
    ext x
    simp only [List.mem_toFinset]
    exact hperm.mem_iff
  show (c3.A.reverse ++ [c3.z]).toFinset.filter (· ∈ Y) = c3.S1U
  rw [hts]

/-- The lower-leftover finset is unchanged by `A`-reversal. -/
theorem revCase3_L2 (c3 : Case3Data G X Y) (hXY : Disjoint X Y) :
    (revCase3 c3 hXY).L2 = c3.L2 := by
  have hperm : List.Perm (c3.A.reverse ++ c3.z :: c3.B)
      (c3.A ++ c3.z :: c3.B) := (List.reverse_perm _).append_right _
  have hts : (c3.A.reverse ++ c3.z :: c3.B).toFinset =
      (c3.A ++ c3.z :: c3.B).toFinset := by
    ext x
    simp only [List.mem_toFinset]
    exact hperm.mem_iff
  show X \ (c3.A.reverse ++ c3.z :: c3.B).toFinset = c3.L2
  rw [hts]

/-- A second leftover vertex of the original datum is one of the reversed
datum. -/
theorem revCase3_HasUx2 (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (h : c3.HasUx2) : (revCase3 c3 hXY).HasUx2 := by
  obtain ⟨u₂, hu₂X, hu₂S, hu₂ne⟩ := h
  refine ⟨u₂, hu₂X, ?_, hu₂ne⟩
  show u₂ ∉ c3.A.reverse ++ c3.z :: c3.B
  intro hm
  exact hu₂S (((List.reverse_perm _).append_right _).mem_iff.mp hm)

/-- Claim B′ transports across `A`-reversal. -/
theorem revCase3_ClaimB' (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (h : c3.ClaimB') : (revCase3 c3 hXY).ClaimB' := by
  intro l hl hlA
  show ¬ G.Adj l (c3.B.head c3.hB)
  exact h l (by rwa [revCase3_SL c3 hXY] at hl)
    (List.mem_reverse.mp hlA)

/-- Claim C transports across `A`-reversal. -/
theorem revCase3_hC (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (h : ∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u) :
    ∀ w ∈ (revCase3 c3 hXY).L2, ∀ u ∈ (revCase3 c3 hXY).S1U,
      ¬ G.Adj w u := by
  intro w hw u hu
  exact h w (by rwa [revCase3_L2 c3 hXY] at hw) u
    (by rwa [revCase3_S1U c3 hXY] at hu)

/-- **Claim E, reverse direction** (`j + 5 ≤ i`): the edge `A[i]–A[j]` is red.
Obtained by applying the forward direction `hdir` to the `A`-reversed datum:
index `k` of `A.reverse` is index `r - 1 - k` of `A`, and `r` odd flips the
parities `i' = r-1-i` (even), `j' = r-1-j` (odd) with `i' + 5 ≤ j'` from
`j + 5 ≤ i`. -/
theorem e_rev_core
    (hdir : ∀ (c' : Case3Data G X Y) (hXY' : Disjoint X Y)
      (hB'' : c'.ClaimB') (hC' : ∀ w ∈ c'.L2, ∀ u ∈ c'.S1U, ¬ G.Adj w u)
      (hux2' : c'.HasUx2) {i' j' : ℕ}
      (hi' : i' < c'.A.length) (hpar' : i' % 2 = 0)
      (hj' : j' < c'.A.length) (hjp' : j' % 2 = 1) (hij' : i' + 5 ≤ j'),
      G.Adj c'.A[i'] c'.A[j'])
    (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hB' : c3.ClaimB') (hC : ∀ w ∈ c3.L2, ∀ u ∈ c3.S1U, ¬ G.Adj w u)
    (hux2 : c3.HasUx2) {i j : ℕ}
    (hi : i < c3.A.length) (hpar : i % 2 = 0)
    (hj : j < c3.A.length) (hjp : j % 2 = 1) (hij : j + 5 ≤ i) :
    G.Adj c3.A[i] c3.A[j] := by
  have hro : c3.A.length % 2 = 1 := c3.r_odd hXY
  have hi'' : c3.A.length - 1 - i < (revCase3 c3 hXY).A.length := by
    show c3.A.length - 1 - i < c3.A.reverse.length
    rw [List.length_reverse]
    omega
  have hj'' : c3.A.length - 1 - j < (revCase3 c3 hXY).A.length := by
    show c3.A.length - 1 - j < c3.A.reverse.length
    rw [List.length_reverse]
    omega
  have happ := hdir (revCase3 c3 hXY) hXY
    (revCase3_ClaimB' c3 hXY hB') (revCase3_hC c3 hXY hC)
    (revCase3_HasUx2 c3 hXY hux2)
    hi'' (by omega) hj'' (by omega) (by omega)
  have e1 : (revCase3 c3 hXY).A[c3.A.length - 1 - i]'hi'' = c3.A[i] := by
    have hlt : c3.A.length - 1 - i < c3.A.length := by omega
    have hlt2 : c3.A.length - 1 - i < c3.A.reverse.length := by
      rw [List.length_reverse]; omega
    have e : c3.A.length - 1 - (c3.A.length - 1 - i) = i := by omega
    have h1 := List.getElem?_reverse (l := c3.A) (i := c3.A.length - 1 - i) hlt
    rw [e, List.getElem?_eq_getElem hlt2, List.getElem?_eq_getElem hi] at h1
    exact Option.some.inj h1
  have e2 : (revCase3 c3 hXY).A[c3.A.length - 1 - j]'hj'' = c3.A[j] := by
    have hlt : c3.A.length - 1 - j < c3.A.length := by omega
    have hlt2 : c3.A.length - 1 - j < c3.A.reverse.length := by
      rw [List.length_reverse]; omega
    have e : c3.A.length - 1 - (c3.A.length - 1 - j) = j := by omega
    have h1 := List.getElem?_reverse (l := c3.A) (i := c3.A.length - 1 - j) hlt
    rw [e, List.getElem?_eq_getElem hlt2, List.getElem?_eq_getElem hj] at h1
    exact Option.some.inj h1
  rw [e1, e2] at happ
  exact happ

end Case3Data

end JSP415
