import JSP415.GLIface
import JSP415.GLScratchA
import JSP415.GLScratchW

/-!
# GL73 Theorem 3, case (iii): claims G and H

Target: `ghfacts` — the four leftover claims

* **G1** `∀ w ∈ sc1, ∀ l ∈ SL, G.Adj w l` (sc1 × SL red),
* **G2** `∀ w ∈ sc2, ∀ l ∈ SL, ¬ G.Adj w l` (sc2 × SL blue),
* **H1** `∀ w ∈ L2, ∀ u ∈ sc1, ¬ G.Adj w u` (L2 × sc1 blue),
* **H2** `∀ w ∈ L2, ∀ u ∈ sc2, G.Adj w u` (L2 × sc2 red).

Strategy.  Each instance is proved by contradiction via `c3.hmax`:
assuming the edge has the wrong colour we exhibit an either-order bipath
`S'` that is either strictly longer (contradiction outright) or has equal
length and is killed by `bipathO_kill_Ymid` using the leftover `c3.ux`.

Let `r = A.length`, `s = B.length` (both odd), `p = |S1U| = (r+1)/2`,
`q = |S2U| = (s+1)/2`, `m = |SL| = (r+s)/2`.

* G1: `A' = P ++ [z]`, mid `w`, `B' = l :: Q` where `P` interleaves
  `YR ⊆ S1U` with `XR ⊆ SL∖{z,l}` (`|YR| = |XR|+1`, ends at an upper, so
  the last red edge into `z` is `E`-red) and `Q` interleaves `YB ⊆ S2U`
  with the rest `XB = SL∖{z,l}∖XR` (`|YB| = |XB|+1`, blue by internal
  facts).  Equal length `r+s+1`; endpoints `P.head, YB.last ∈ Y`,
  midpoint `w ∈ Y`, leftover `ux ∈ X` — killed.
* G2: `A' = R ++ [l]` (same `P`-skeleton ending at an `S1U`-upper, then
  `u–l` red), mid `w`, `B' = z :: Q` (`w–z` blue by `sc2`, `z–y` blue by
  `hI.2`).  Same kill.
* H1: assuming `w–u` red, the longer path
  `P1 ++ [u, w] ++ [b₁]` on the red side (`P1` on `Y1 ⊆ S1U`, `X1 ⊆ SL`,
  ending at an `SL`-vertex which is `G1`-red to `u`; `w–b₁` red by `C′`),
  and `b₁ :: B'` blue on `X3 = SL ∖ X1`, `Y3 = S2U ∖ {b₁}`.
* H2: assuming `w–u` blue, the longer path with midpoint `a₁`: red
  `R ++ [a₁]` on `Y1 = S1U ∖ {a₁}`, `X1 ⊆ SL`; blue
  `a₁ :: w :: u :: Q` (`a₁–w` blue by `C`, `u–x` blue by `G2`) with `Q`
  on `XQ = SL ∖ X1`, `YQ = S2U`.
-/

open Finset
open Classical

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

/-- Snoc a chain: `(l ++ [a])` is a chain if `l` is and every
`getLast?`-element relates to `a`. -/
theorem List.isChain_snoc' {R : V → V → Prop} {l : List V} {a : V}
    (hl : l.IsChain R) (h : ∀ x ∈ l.getLast?, R x a) :
    (l ++ [a]).IsChain R :=
  hl.append (List.isChain_singleton a) fun x hx y hy ↦ by
    obtain rfl := Option.mem_some_iff.mp (List.head?_singleton ▸ hy)
    exact h x hx

/-- In an `adjXY`-chain whose head lies in `Y`, the last vertex lies in `Y`
whenever `l.length - 1` is even. -/
private theorem adjXY_getLast_mem_Y {c : Color} {l : List V}
    (hXY : Disjoint X Y) (h : l.IsChain (Color.adjXY G X Y c)) (hl : l ≠ [])
    (hpar : (l.length - 1) % 2 = 0) (hhead : l.head hl ∈ Y) :
    l.getLast hl ∈ Y := by
  have hp : 0 < l.length := List.length_pos_of_ne_nil hl
  have hs := (Color.adjXY.same_side h hXY hp (j := l.length - 1)
    (by omega) (Nat.zero_le _) (by simpa using hpar)).2
  rw [List.getLast_eq_getElem hl]
  rw [List.head_eq_getElem_zero hl] at hhead
  exact hs.mp hhead

/-- In an `adjXY`-chain whose head lies in `X`, the last vertex lies in `X`
whenever `l.length - 1` is even. -/
private theorem adjXY_getLast_mem_X {c : Color} {l : List V}
    (hXY : Disjoint X Y) (h : l.IsChain (Color.adjXY G X Y c)) (hl : l ≠ [])
    (hpar : (l.length - 1) % 2 = 0) (hhead : l.head hl ∈ X) :
    l.getLast hl ∈ X := by
  have hp : 0 < l.length := List.length_pos_of_ne_nil hl
  have hs := (Color.adjXY.same_side h hXY hp (j := l.length - 1)
    (by omega) (Nat.zero_le _) (by simpa using hpar)).1
  rw [List.getLast_eq_getElem hl]
  rw [List.head_eq_getElem_zero hl] at hhead
  exact hs.mp hhead

/-- `head` of an append with a nonempty left part. -/
theorem List.head_append_left {l₁ l₂ : List V} (h₁ : l₁ ≠ [])
    (h : l₁ ++ l₂ ≠ []) :
    (l₁ ++ l₂).head h = l₁.head h₁ := by
  have e : (l₁ ++ l₂).head? = some (l₁.head h₁) := by
    rw [List.head?_append_of_ne_nil _ h₁, List.head?_eq_some_head h₁]
  rw [List.head?_eq_some_head h] at e
  exact Option.some_inj.mp e

/-- Membership inherited from `getLast?`. -/
theorem mem_of_mem_getLast? {a : V} {l : List V} (h : a ∈ l.getLast?) :
    a ∈ l := by
  obtain ⟨hl, rfl⟩ := List.mem_getLast?_eq_getLast h
  exact List.getLast_mem hl

/-- Membership inherited from `head?`. -/
theorem mem_of_mem_head? {a : V} {l : List V} (h : a ∈ l.head?) :
    a ∈ l := by
  rw [List.eq_cons_of_mem_head? h]
  exact List.mem_cons_self

/-- Append two nodup lists whose members lie in disjoint finsets. -/
theorem nodup_append_disj {l₁ l₂ : List V} {F₁ F₂ : Finset V}
    (h1 : l₁.Nodup) (h2 : l₂.Nodup)
    (hs1 : ∀ a ∈ l₁, a ∈ F₁) (hs2 : ∀ a ∈ l₂, a ∈ F₂)
    (hd : Disjoint F₁ F₂) : (l₁ ++ l₂).Nodup := by
  rw [List.nodup_append]
  exact ⟨h1, h2, fun a ha b hb e ↦
    Finset.disjoint_left.mp hd (hs1 a ha) (e ▸ hs2 b hb)⟩

/-- Prepend a vertex not occurring in the bounded pool of a nodup list. -/
theorem nodup_cons' {a : V} {l : List V} {F : Finset V}
    (ha : a ∉ F) (hs : ∀ b ∈ l, b ∈ F) (h : l.Nodup) : (a :: l).Nodup :=
  List.nodup_cons.mpr ⟨fun h ↦ ha (hs _ h), h⟩

namespace Case3Data

variable (c3 : Case3Data G X Y)

/-! ### Membership characterisations -/

theorem mem_sc1 {w : V} :
    w ∈ c3.sc1 ↔ w ∈ Y ∧ w ∉ c3.A ++ c3.z :: c3.B ∧ G.Adj w c3.z := by
  unfold sc1
  simp only [Finset.mem_filter, Finset.mem_sdiff, List.mem_toFinset]
  tauto

theorem mem_sc2 {w : V} :
    w ∈ c3.sc2 ↔ w ∈ Y ∧ w ∉ c3.A ++ c3.z :: c3.B ∧ ¬G.Adj w c3.z := by
  unfold sc2
  simp only [Finset.mem_filter, Finset.mem_sdiff, List.mem_toFinset]
  tauto

theorem mem_L2 {w : V} :
    w ∈ c3.L2 ↔ w ∈ X ∧ w ∉ c3.A ++ c3.z :: c3.B := by
  unfold L2
  simp only [Finset.mem_sdiff, List.mem_toFinset]

private theorem mem_SL {l : V} :
    l ∈ c3.SL ↔ l ∈ X ∧ (l ∈ c3.A ∨ l = c3.z ∨ l ∈ c3.B) := by
  unfold SL S
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_append,
    List.mem_cons]
  tauto

private theorem mem_S1U {u : V} :
    u ∈ c3.S1U ↔ u ∈ (c3.A ++ [c3.z]) ∧ u ∈ Y := by
  unfold S1U S1
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false]

private theorem mem_S2U {u : V} :
    u ∈ c3.S2U ↔ u ∈ (c3.z :: c3.B) ∧ u ∈ Y := by
  unfold S2U S2
  simp [Finset.mem_filter, List.mem_toFinset]

theorem S1U_mem_A (hXY : Disjoint X Y) {u : V} (hu : u ∈ c3.S1U) :
    u ∈ c3.A := by
  obtain ⟨h, hY⟩ := (c3.mem_S1U).mp hu
  rcases List.mem_append.mp h with h | h
  · exact h
  · rw [List.mem_singleton] at h; subst h
    exact absurd hY (Disjoint.notMem_left hXY c3.hz)

theorem S2U_mem_B (hXY : Disjoint X Y) {u : V} (hu : u ∈ c3.S2U) :
    u ∈ c3.B := by
  obtain ⟨h, hY⟩ := (c3.mem_S2U).mp hu
  rcases List.mem_cons.mp h with h | h
  · subst h; exact absurd hY (Disjoint.notMem_left hXY c3.hz)
  · exact h

theorem S1U_Y {u : V} (hu : u ∈ c3.S1U) : u ∈ Y := ((c3.mem_S1U).mp hu).2
theorem S2U_Y {u : V} (hu : u ∈ c3.S2U) : u ∈ Y := ((c3.mem_S2U).mp hu).2
theorem SL_X {l : V} (hl : l ∈ c3.SL) : l ∈ X := ((c3.mem_SL).mp hl).1

theorem S1U_mem_S {u : V} (hu : u ∈ c3.S1U) : u ∈ c3.A ++ c3.z :: c3.B := by
  obtain ⟨h, -⟩ := (c3.mem_S1U).mp hu
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · rw [List.mem_singleton] at h; subst h
    exact List.mem_append_right _ List.mem_cons_self

theorem S2U_mem_S {u : V} (hu : u ∈ c3.S2U) : u ∈ c3.A ++ c3.z :: c3.B := by
  obtain ⟨h, -⟩ := (c3.mem_S2U).mp hu
  rcases List.mem_cons.mp h with h | h
  · subst h; exact List.mem_append_right _ List.mem_cons_self
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

theorem SL_mem_S {l : V} (hl : l ∈ c3.SL) : l ∈ c3.A ++ c3.z :: c3.B := by
  obtain ⟨-, h⟩ := (c3.mem_SL).mp hl
  rcases h with h | h | h
  · exact List.mem_append_left _ h
  · subst h; exact List.mem_append_right _ List.mem_cons_self
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

theorem z_mem_SL : c3.z ∈ c3.SL :=
  (c3.mem_SL).mpr ⟨c3.hz, Or.inr (Or.inl rfl)⟩

theorem disjoint_S1U_S2U (hXY : Disjoint X Y) : Disjoint c3.S1U c3.S2U := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨-, -, hAB⟩ := c3.hb.disjoint_pieces
  exact hAB (c3.S1U_mem_A hXY hx) (c3.S2U_mem_B hXY hy)

theorem disjoint_S1U_SL (hXY : Disjoint X Y) : Disjoint c3.S1U c3.SL := by
  rw [Finset.disjoint_left]
  intro x hx hy
  exact (Disjoint.notMem_left hXY (c3.SL_X hy)) (c3.S1U_Y hx)

theorem disjoint_S2U_SL (hXY : Disjoint X Y) : Disjoint c3.S2U c3.SL := by
  rw [Finset.disjoint_left]
  intro x hx hy
  exact (Disjoint.notMem_left hXY (c3.SL_X hy)) (c3.S2U_Y hx)

theorem head_mem_S1U : c3.A.head c3.hA ∈ c3.S1U :=
  (c3.mem_S1U).mpr
    ⟨List.mem_append_left _ (List.head_mem c3.hA), c3.hhead⟩

theorem getLast_mem_S2U : c3.B.getLast c3.hB ∈ c3.S2U :=
  (c3.mem_S2U).mpr
    ⟨List.mem_cons_of_mem _ (List.getLast_mem c3.hB), c3.hlast⟩

theorem head_mem_S2U (hXY : Disjoint X Y) : c3.B.head c3.hB ∈ c3.S2U := by
  obtain ⟨hred, hblue, -⟩ := c3.hb
  have he : Color.adjXY G X Y .blue c3.z (c3.B.head c3.hB) :=
    IsBipath.blue_first_edge c3.hb c3.hB
  have hbY : c3.B.head c3.hB ∈ Y :=
    (acrossXY.left_mem_iff hXY (Color.adjXY.across he)).mp c3.hz
  exact (c3.mem_S2U).mpr
    ⟨List.mem_cons_of_mem _ (List.head_mem c3.hB), hbY⟩

/-- The two branch lengths are odd. -/
theorem parity_len (hXY : Disjoint X Y) :
    c3.A.length % 2 = 1 ∧ c3.B.length % 2 = 1 := by
  constructor
  · rcases Nat.mod_two_eq_zero_or_one c3.A.length with h | h
    · exfalso
      have hlen : (c3.A ++ [c3.z]).length - 1 = c3.A.length := by simp
      have hne : c3.A ++ [c3.z] ≠ [] := by simp
      have hg : (c3.A ++ [c3.z]).getLast hne ∈ Y := by
        apply adjXY_getLast_mem_Y hXY c3.hb.1 hne
        · rw [hlen]; exact h
        · rw [List.head_append_left c3.hA hne]; exact c3.hhead
      rw [List.getLast_append_of_right_ne_nil _ _ (List.cons_ne_nil _ _)] at hg
      exact Disjoint.notMem_left hXY c3.hz (by simpa using hg)
    · exact h
  · rcases Nat.mod_two_eq_zero_or_one c3.B.length with h | h
    · exfalso
      have hlen : (c3.z :: c3.B).length - 1 = c3.B.length := by simp
      have hne : c3.z :: c3.B ≠ [] := List.cons_ne_nil _ _
      have hg : (c3.z :: c3.B).getLast hne ∈ X := by
        apply adjXY_getLast_mem_X hXY c3.hb.2.1 hne
        · rw [hlen]; exact h
        · exact c3.hz
      rw [List.getLast_cons c3.hB] at hg
      exact Disjoint.notMem_right hXY c3.hlast hg
    · exact h

/-- Cardinality content of an `acrossXY`-chain over a nodup list whose
elements lie in `X ∪ Y`: the `X`- and `Y`-finset counts sum to the length
and differ by at most one (direction controlled by the head side). -/
theorem across_chain_cards (hXY : Disjoint X Y) {l : List V}
    (hac : l.IsChain (acrossXY X Y)) (hnd : l.Nodup)
    (hmem : ∀ a ∈ l, a ∈ X ∪ Y) :
    ((l.toFinset ∩ X).card : ℤ) + ((l.toFinset ∩ Y).card : ℤ) = l.length ∧
    (∀ a ∈ l.head?, a ∈ X →
      ((l.toFinset ∩ X).card : ℤ) - (l.toFinset ∩ Y).card = 0 ∨
      ((l.toFinset ∩ X).card : ℤ) - (l.toFinset ∩ Y).card = 1) ∧
    (∀ a ∈ l.head?, a ∈ Y →
      ((l.toFinset ∩ X).card : ℤ) - (l.toFinset ∩ Y).card = 0 ∨
      ((l.toFinset ∩ X).card : ℤ) - (l.toFinset ∩ Y).card = -1) := by
  have hsum := across_chain_side_sum hXY l hac hmem
  have hdiff := across_chain_side_diff hXY l hac hmem
  rw [sideCount_eq_card X hnd, sideCount_eq_card Y hnd] at hsum hdiff
  exact ⟨hsum, hdiff.1, hdiff.2⟩

/-- The side-counts of the maximal bipath:
`|S1U| = (r+1)/2`, `|S2U| = (s+1)/2`, `|SL| = (r+s)/2`. -/
theorem cards (hXY : Disjoint X Y) :
    c3.S1U.card = (c3.A.length + 1) / 2 ∧
    c3.S2U.card = (c3.B.length + 1) / 2 ∧
    c3.SL.card = (c3.A.length + c3.B.length) / 2 := by
  obtain ⟨hred, hblue, hnd⟩ := c3.hb
  obtain ⟨hr, hs⟩ := c3.parity_len hXY
  have hmemA : ∀ a ∈ c3.A ++ [c3.z], a ∈ X ∪ Y := fun a ha ↦
    across_chain_mem_union hXY (hred.imp fun _ _ h ↦ Color.adjXY.across h) ha
      (by have h1 := List.length_pos_of_ne_nil c3.hA; simp; omega)
  have hmemB : ∀ a ∈ c3.z :: c3.B, a ∈ X ∪ Y := fun a ha ↦
    across_chain_mem_union hXY (hblue.imp fun _ _ h ↦ Color.adjXY.across h) ha
      (by have h1 := List.length_pos_of_ne_nil c3.hB; simp; omega)
  have hmemS : ∀ a ∈ c3.A ++ c3.z :: c3.B, a ∈ X ∪ Y := fun a ha ↦
    across_chain_mem_union hXY (IsBipath.acrossChain c3.hb) ha
      (by have h1 := List.length_pos_of_ne_nil c3.hA; simp; omega)
  have hndB : (c3.z :: c3.B).Nodup := (List.nodup_append.mp hnd).2.1
  have hndA : (c3.A ++ [c3.z]).Nodup := by
    have e : c3.A ++ c3.z :: c3.B = (c3.A ++ [c3.z]) ++ c3.B := by simp
    rw [e] at hnd
    exact (List.nodup_append.mp hnd).1
  -- S1U
  have key1 : c3.S1U.card = (c3.A.length + 1) / 2 := by
    have h1 : c3.S1U = (c3.A ++ [c3.z]).toFinset ∩ Y := by
      ext u
      unfold S1U S1
      simp [Finset.mem_filter, List.mem_toFinset, Finset.mem_inter]
    obtain ⟨hsum, -, hdY⟩ := across_chain_cards hXY
      (hred.imp fun _ _ h ↦ Color.adjXY.across h) hndA hmemA
    have hhd : (c3.A ++ [c3.z]).head? = some (c3.A.head c3.hA) := by
      rw [List.head?_append_of_ne_nil _ c3.hA, List.head?_eq_some_head c3.hA]
    have hlen : (c3.A ++ [c3.z]).length = c3.A.length + 1 := by simp
    rcases hdY _ (by simp [hhd]) c3.hhead with h0 | h0
    · rw [h1]; omega
    · exfalso; omega
  -- S2U
  have key2 : c3.S2U.card = (c3.B.length + 1) / 2 := by
    have h1 : c3.S2U = (c3.z :: c3.B).toFinset ∩ Y := by
      ext u
      unfold S2U S2
      simp [Finset.mem_filter, List.mem_toFinset, Finset.mem_inter]
    obtain ⟨hsum, hdX, -⟩ := across_chain_cards hXY
      (hblue.imp fun _ _ h ↦ Color.adjXY.across h) hndB hmemB
    have hhd : (c3.z :: c3.B).head? = some c3.z := by simp
    have hlen : (c3.z :: c3.B).length = c3.B.length + 1 := by simp
    rcases hdX _ (by simp [hhd]) c3.hz with h0 | h0
    · rw [h1]; omega
    · exfalso; omega
  -- SL
  have key3 : c3.SL.card = (c3.A.length + c3.B.length) / 2 := by
    have h1 : c3.SL = (c3.A ++ c3.z :: c3.B).toFinset ∩ X := by
      ext u
      unfold SL S
      simp [Finset.mem_filter, List.mem_toFinset, Finset.mem_inter]
    obtain ⟨hsum, -, hdY⟩ := across_chain_cards hXY
      (IsBipath.acrossChain c3.hb) hnd hmemS
    have hhd : (c3.A ++ c3.z :: c3.B).head? = some (c3.A.head c3.hA) := by
      rw [List.head?_append_of_ne_nil _ c3.hA, List.head?_eq_some_head c3.hA]
    have hlen : (c3.A ++ c3.z :: c3.B).length =
        c3.A.length + c3.B.length + 1 := by simp; omega
    rcases hdY _ (by simp [hhd]) c3.hhead with h0 | h0
    · exfalso; omega
    · rw [h1]; omega
  exact ⟨key1, key2, key3⟩

/-! ### The interleaving gadget -/

/-- Interleave two lists whose elements are drawn from finsets `S₁`, `S₂`
with a complete `c`-coloured bipartite connection between them. -/
theorem interleave_pack {c : Color} {S₁ S₂ : Finset V}
    (hXY : Disjoint X Y) (hdisj : Disjoint S₁ S₂)
    (hcol : ∀ a ∈ S₁, ∀ b ∈ S₂, Color.adjXY G X Y c a b)
    {xs ys : List V}
    (hxs : ∀ a ∈ xs, a ∈ S₁) (hys : ∀ b ∈ ys, b ∈ S₂)
    (hxn : xs.Nodup) (hyn : ys.Nodup)
    (hle : xs.length ≤ ys.length + 1) (hge : ys.length ≤ xs.length) :
    (interleave xs ys).IsChain (Color.adjXY G X Y c) ∧ (interleave xs ys).Nodup ∧
      (∀ x ∈ interleave xs ys, x ∈ S₁ ∨ x ∈ S₂) := by
  refine ⟨interleave_adjXY_isChain (fun a ha b hb ↦ hcol a (hxs a ha)
      b (hys b hb)) hle hge, ?_, ?_⟩
  · exact interleave_nodup hxn hyn fun a ha hb ↦
      Finset.disjoint_left.mp hdisj (hxs a ha) (hys a hb)
  · intro x hx
    rcases (mem_interleave.mp hx) with h | h
    · exact Or.inl (hxs x h)
    · exact Or.inr (hys x h)

/-- Elements of a `toList` enumeration lie in the finset. -/
theorem toList_mem {S : Finset V} : ∀ a ∈ S.toList, a ∈ S :=
  fun _ ↦ Finset.mem_toList.mp

theorem toList_nodup {S : Finset V} : S.toList.Nodup := Finset.nodup_toList S

theorem toList_len {S : Finset V} : S.toList.length = S.card :=
  Finset.length_toList S

/-- `x` adjacent-`red` facts lifted to `adjXY` from `Y`-side to `X`-side. -/
theorem adjXY_red_YX {a b : V} (h : G.Adj a b) (ha : a ∈ Y) (hb : b ∈ X) :
    Color.adjXY G X Y .red a b := ⟨Or.inr ⟨ha, hb⟩, h⟩

theorem adjXY_red_XY {a b : V} (h : G.Adj a b) (ha : a ∈ X) (hb : b ∈ Y) :
    Color.adjXY G X Y .red a b := ⟨Or.inl ⟨ha, hb⟩, h⟩

theorem adjXY_blue_YX {a b : V} (h : ¬G.Adj a b) (ha : a ∈ Y) (hb : b ∈ X) :
    Color.adjXY G X Y .blue a b := ⟨Or.inr ⟨ha, hb⟩, h⟩

theorem adjXY_blue_XY {a b : V} (h : ¬G.Adj a b) (ha : a ∈ X) (hb : b ∈ Y) :
    Color.adjXY G X Y .blue a b := ⟨Or.inl ⟨ha, hb⟩, h⟩

theorem ne_of_disjoint {S₁ S₂ : Finset V} (hd : Disjoint S₁ S₂)
    {a b : V} (ha : a ∈ S₁) (hb : b ∈ S₂) : a ≠ b :=
  fun e ↦ Finset.disjoint_left.mp hd ha (e ▸ hb)

theorem ne_of_XY (hXY : Disjoint X Y) {a b : V} (ha : a ∈ X) (hb : b ∈ Y) :
    a ≠ b :=
  fun e ↦ (Disjoint.notMem_left hXY ha) (e ▸ hb)

theorem ne_of_YX (hXY : Disjoint X Y) {a b : V} (ha : a ∈ Y) (hb : b ∈ X) :
    a ≠ b :=
  fun e ↦ (Disjoint.notMem_right hXY ha) (e ▸ hb)

/-! ### Claims G1 and G2 -/

/-- **Auxiliary engine for G1 and G2.**  Given `w ∈ Y ∖ S` and two distinct
`s, t ∈ SL` such that `s–w` is red and `w–t` is blue, the bipath
`(P ++ [s], w, t :: Q)` — where `P` interleaves `YR ⊆ S1U` with
`XR ⊆ SL∖{s,t}` and `Q` interleaves `YB ⊆ S2U` with `XB = SL∖{s,t}∖XR` —
is an equal-length bipath killed by `bipathO_kill_Ymid` (both endpoints lie
in `Y`, midpoint `w ∈ Y`, leftover `ux ∈ X`). -/
theorem claimG_aux (hXY : Disjoint X Y) (hI : c3.InternalFacts)
    {w s t : V} (hwY : w ∈ Y) (hwS : w ∉ c3.A ++ c3.z :: c3.B)
    (hs : s ∈ c3.SL) (ht : t ∈ c3.SL) (hst : s ≠ t)
    (hsw : G.Adj s w) (hwt : ¬G.Adj w t) : False := by
  have hsX := c3.SL_X hs
  have htX := c3.SL_X ht
  obtain ⟨hred, hblue, hnd⟩ := c3.hb
  obtain ⟨hr, hsr⟩ := c3.parity_len hXY
  obtain ⟨cS1, cS2, cSL⟩ := c3.cards hXY
  -- finset skeleton
  have hlT0 : t ∈ c3.SL.erase s :=
    Finset.mem_erase.mpr ⟨fun h ↦ hst h.symm, ht⟩
  have hTc : ((c3.SL.erase s).erase t).card = c3.SL.card - 2 := by
    rw [Finset.card_erase_of_mem hlT0, Finset.card_erase_of_mem hs]
    omega
  have hTsub : (c3.SL.erase s).erase t ⊆ c3.SL :=
    (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hTsub' : (c3.SL.erase s).erase t ⊆ c3.SL.erase s :=
    Finset.erase_subset _ _
  obtain ⟨XR, hXRT, hXRc⟩ := Finset.exists_subset_card_eq
    (s := (c3.SL.erase s).erase t) (n := (c3.A.length - 3) / 2) (by
      rw [hTc, cSL]
      have h1 := List.length_pos_of_ne_nil c3.hA
      have h2 := List.length_pos_of_ne_nil c3.hB
      omega)
  have hXRSL : XR ⊆ c3.SL := hXRT.trans hTsub
  have hXBc : (((c3.SL.erase s).erase t) \ XR).card =
      c3.SL.card - 2 - (c3.A.length - 3) / 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hXRT, hTc, hXRc]
  have hXBSL : ((c3.SL.erase s).erase t) \ XR ⊆ c3.SL :=
    Finset.sdiff_subset.trans hTsub
  have hXBsubT : ((c3.SL.erase s).erase t) \ XR ⊆ (c3.SL.erase s).erase t :=
    Finset.sdiff_subset
  have hXBle : (((c3.SL.erase s).erase t) \ XR).card + 1 ≤ c3.S2U.card := by
    rw [hXBc, cSL, cS2]
    have h1 := List.length_pos_of_ne_nil c3.hA
    have h2 := List.length_pos_of_ne_nil c3.hB
    omega
  obtain ⟨YR, hYRS1, hYRc⟩ := Finset.exists_subset_card_eq (s := c3.S1U)
    (n := (c3.A.length - 3) / 2 + 1) (by
      rw [cS1]; have h1 := List.length_pos_of_ne_nil c3.hA; omega)
  obtain ⟨YB, hYBS2, hYBc⟩ := Finset.exists_subset_card_eq (s := c3.S2U)
    (n := (((c3.SL.erase s).erase t) \ XR).card + 1) hXBle
  -- list skeleton
  have hlenYR : YR.toList.length = XR.toList.length + 1 := by
    rw [toList_len, toList_len, hYRc, hXRc]
  have hlenYB : YB.toList.length =
      (((c3.SL.erase s).erase t) \ XR).toList.length + 1 := by
    rw [toList_len, toList_len, hYBc]
  have hYRne : YR.toList ≠ [] := by
    intro e
    have e' : YR.toList.length = 0 := by rw [e]; rfl
    rw [toList_len, hYRc] at e'; omega
  have hYBne : YB.toList ≠ [] := by
    intro e
    have e' : YB.toList.length = 0 := by rw [e]; rfl
    rw [toList_len, hYBc] at e'; omega
  obtain ⟨hPred, hPnd, hPm⟩ := interleave_pack hXY
    (c := Color.red)
    (Disjoint.mono hYRS1 hXRSL (c3.disjoint_S1U_SL hXY))
    (fun a ha b hb ↦
      ⟨Or.inr ⟨c3.S1U_Y (hYRS1 ha), c3.SL_X (hXRSL hb)⟩,
       hI.1 a (hYRS1 ha) b (hXRSL hb)⟩)
    (fun _ ↦ Finset.mem_toList.mp) (fun _ ↦ Finset.mem_toList.mp)
    (Finset.nodup_toList _) (Finset.nodup_toList _)
    (by omega) (by omega)
  obtain ⟨hQblue, hQnd, hQm⟩ := interleave_pack hXY
    (c := Color.blue)
    (Disjoint.mono hYBS2 hXBSL (c3.disjoint_S2U_SL hXY))
    (fun a ha b hb ↦
      ⟨Or.inr ⟨c3.S2U_Y (hYBS2 ha), c3.SL_X (hXBSL hb)⟩,
       hI.2 a (hYBS2 ha) b (hXBSL hb)⟩)
    (fun _ ↦ Finset.mem_toList.mp) (fun _ ↦ Finset.mem_toList.mp)
    (Finset.nodup_toList _) (Finset.nodup_toList _)
    (by omega) (by omega)
  -- red chain `(P ++ [s]) ++ [w]`
  have hA1 : (interleave YR.toList XR.toList ++ [s]).IsChain
      (Color.adjXY G X Y .red) := by
    apply List.isChain_snoc' hPred
    intro x hx
    rw [interleave_getLast?_succ hlenYR] at hx
    have hxm := hYRS1 (Finset.mem_toList.mp (mem_of_mem_getLast? hx))
    exact ⟨Or.inr ⟨c3.S1U_Y hxm, hsX⟩, hI.1 x hxm s hs⟩
  have hA' : (interleave YR.toList XR.toList ++ [s] ++ [w]).IsChain
      (Color.adjXY G X Y .red) := by
    apply List.isChain_snoc' hA1
    intro x hx
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast?_singleton] at hx
    obtain rfl := Option.mem_some_iff.mp hx
    exact ⟨Or.inl ⟨hsX, hwY⟩, hsw⟩
  -- blue chain `w :: t :: Q`
  have hB' : (w :: t :: interleave YB.toList
      (((c3.SL.erase s).erase t) \ XR).toList).IsChain
      (Color.adjXY G X Y .blue) := by
    apply List.isChain_cons.mpr
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [List.head?_cons] at hy
      obtain rfl := Option.mem_some_iff.mp hy
      exact ⟨Or.inr ⟨hwY, htX⟩, hwt⟩
    · apply List.isChain_cons.mpr
      refine ⟨?_, hQblue⟩
      intro y hy
      rw [interleave_head? hYBne] at hy
      have hym := hYBS2 (Finset.mem_toList.mp (mem_of_mem_head? hy))
      exact ⟨Or.inl ⟨htX, c3.S2U_Y hym⟩,
        fun h ↦ hI.2 y hym t ht h.symm⟩
  -- nodup of `(P ++ [s]) ++ w :: t :: Q`
  have hnd' : ((interleave YR.toList XR.toList ++ [s]) ++
      w :: t :: interleave YB.toList
        (((c3.SL.erase s).erase t) \ XR).toList).Nodup := by
    apply nodup_append_disj
        (F₁ := YR ∪ XR ∪ ({s} : Finset V))
        (F₂ := ({w} ∪ {t} : Finset V) ∪
          (YB ∪ ((c3.SL.erase s).erase t) \ XR))
    · apply nodup_append_disj (F₁ := YR ∪ XR) (F₂ := ({s} : Finset V))
      · exact hPnd
      · exact List.nodup_singleton _
      · intro x hx
        rcases hPm x hx with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h
      · intro x hx
        rw [List.mem_singleton] at hx; subst hx
        exact Finset.mem_singleton_self _
      · rw [Finset.disjoint_singleton_right]
        intro hz'
        rcases Finset.mem_union.mp hz' with h | h
        · exact Disjoint.notMem_left hXY hsX (c3.S1U_Y (hYRS1 h))
        · exact Finset.notMem_erase _ _ (hTsub' (hXRT h))
    · apply nodup_cons' (F := ({t} : Finset V) ∪
        (YB ∪ ((c3.SL.erase s).erase t) \ XR))
      · simp only [Finset.mem_union, Finset.mem_singleton]
        rintro (rfl | h | h)
        · exact Disjoint.notMem_right hXY hwY htX
        · exact hwS (c3.S2U_mem_S (hYBS2 h))
        · exact Disjoint.notMem_right hXY hwY (c3.SL_X (hXBSL h))
      · intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
        · rcases hQm x hx with h | h
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
              (Or.inl h)))
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
              (Or.inr h)))
      · apply nodup_cons' (F := YB ∪ ((c3.SL.erase s).erase t) \ XR)
        · simp only [Finset.mem_union]
          rintro (h | h)
          · exact Disjoint.notMem_left hXY htX (c3.S2U_Y (hYBS2 h))
          · exact Finset.notMem_erase _ _ (hXBsubT h)
        · intro x hx
          rcases hQm x hx with h | h
          · exact Finset.mem_union_left _ h
          · exact Finset.mem_union_right _ h
        · exact hQnd
    · intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · rcases hPm x hx with h | h
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union_left _ h))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union_right _ h))
      · rw [List.mem_singleton] at hx; subst hx
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
    · intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_singleton_self _))))
      · rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inr (Finset.mem_singleton_self _))))
        · rcases hQm x hx with h | h
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
              (Or.inl h)))
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
              (Or.inr h)))
    · rw [Finset.disjoint_left]
      intro x hx hx2
      rcases Finset.mem_union.mp hx with hx | hxz
      · rcases Finset.mem_union.mp hx with hx | hx
        · have hxY := c3.S1U_Y (hYRS1 hx)
          have hxS := c3.S1U_mem_S (hYRS1 hx)
          rcases Finset.mem_union.mp hx2 with hx2 | hx2
          · rcases Finset.mem_union.mp hx2 with hx2 | hx2
            · rw [Finset.mem_singleton] at hx2; subst hx2
              exact hwS hxS
            · rw [Finset.mem_singleton] at hx2; subst hx2
              exact Disjoint.notMem_right hXY hxY htX
          · rcases Finset.mem_union.mp hx2 with hx2 | hx2
            · exact Finset.disjoint_left.mp (c3.disjoint_S1U_S2U hXY)
                (hYRS1 hx) (hYBS2 hx2)
            · exact Disjoint.notMem_right hXY hxY (c3.SL_X (hXBSL hx2))
        · have hxX := c3.SL_X (hXRSL hx)
          have hxS := c3.SL_mem_S (hXRSL hx)
          rcases Finset.mem_union.mp hx2 with hx2 | hx2
          · rcases Finset.mem_union.mp hx2 with hx2 | hx2
            · rw [Finset.mem_singleton] at hx2; subst hx2
              exact hwS hxS
            · rw [Finset.mem_singleton] at hx2; subst hx2
              exact Finset.notMem_erase _ _ (hXRT hx)
          · rcases Finset.mem_union.mp hx2 with hx2 | hx2
            · exact Disjoint.notMem_left hXY hxX (c3.S2U_Y (hYBS2 hx2))
            · exact (Finset.mem_sdiff.mp hx2).2 hx
      · rw [Finset.mem_singleton] at hxz; subst hxz
        rcases Finset.mem_union.mp hx2 with hx2 | hx2
        · rcases Finset.mem_union.mp hx2 with hx2 | hx2
          · rw [Finset.mem_singleton] at hx2; subst hx2
            exact Disjoint.notMem_left hXY hsX hwY
          · rw [Finset.mem_singleton] at hx2; subst hx2
            exact hst rfl
        · rcases Finset.mem_union.mp hx2 with hx2 | hx2
          · exact Disjoint.notMem_left hXY hsX (c3.S2U_Y (hYBS2 hx2))
          · exact Finset.notMem_erase _ _ (hTsub' (hXBsubT hx2))
  -- length equality
  have hlen_eq : bipathLen c3.A c3.z c3.B =
      bipathLen (interleave YR.toList XR.toList ++ [s]) w
        (t :: interleave YB.toList
          (((c3.SL.erase s).erase t) \ XR).toList) := by
    have e : (interleave YR.toList XR.toList ++ [s]).length +
        (t :: interleave YB.toList
          (((c3.SL.erase s).erase t) \ XR).toList).length + 1 =
        c3.A.length + c3.B.length + 1 := by
      have hSL2 : 2 ≤ c3.SL.card := by
        have hp := Finset.card_pos.mpr ⟨t, hlT0⟩
        rw [Finset.card_erase_of_mem hs] at hp
        omega
      rw [List.length_append, List.length_cons, List.length_cons, List.length_nil,
        interleave_length, interleave_length,
        toList_len, toList_len, toList_len, toList_len,
        hYRc, hXRc, hYBc, hXBc]
      omega
    exact e.symm
  have hmax' : ∀ A' z' B', IsBipathO G X Y A' z' B' →
      bipathLen A' z' B' ≤
        bipathLen (interleave YR.toList XR.toList ++ [s]) w
          (t :: interleave YB.toList
            (((c3.SL.erase s).erase t) \ XR).toList) :=
    fun A' z' B' h ↦ hlen_eq ▸ c3.hmax A' z' B' h
  -- leftover vertex `ux`
  have huxOut : c3.ux ∉ (interleave YR.toList XR.toList ++ [s]) ++
      w :: t :: interleave YB.toList
        (((c3.SL.erase s).erase t) \ XR).toList := by
    intro hmem
    have hbnd : ∀ x ∈ (interleave YR.toList XR.toList ++ [s]) ++
        w :: t :: interleave YB.toList
          (((c3.SL.erase s).erase t) \ XR).toList,
        x ∈ (c3.A ++ c3.z :: c3.B).toFinset ∨ x = w := by
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · rw [List.mem_append] at hx
        rcases hx with hx | hx
        · rcases hPm x hx with h | h
          · exact Or.inl (List.mem_toFinset.mpr (c3.S1U_mem_S (hYRS1 h)))
          · exact Or.inl (List.mem_toFinset.mpr (c3.SL_mem_S (hXRSL h)))
        · rw [List.mem_singleton] at hx; subst hx
          exact Or.inl (List.mem_toFinset.mpr (c3.SL_mem_S hs))
      · rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inr rfl
        · rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Or.inl (List.mem_toFinset.mpr (c3.SL_mem_S ht))
          · rcases hQm x hx with h | h
            · exact Or.inl (List.mem_toFinset.mpr (c3.S2U_mem_S (hYBS2 h)))
            · exact Or.inl (List.mem_toFinset.mpr (c3.SL_mem_S (hXBSL h)))
    rcases hbnd c3.ux hmem with h | h
    · exact c3.hux.2 (List.mem_toFinset.mp h)
    · subst h; exact Disjoint.notMem_left hXY c3.hux.1 hwY
  -- endpoints in `Y`
  have hAne : interleave YR.toList XR.toList ++ [s] ≠ [] := by simp
  have hBne : t :: interleave YB.toList
      (((c3.SL.erase s).erase t) \ XR).toList ≠ [] := List.cons_ne_nil _ _
  have hAhead : (interleave YR.toList XR.toList ++ [s]).head hAne ∈ Y := by
    rw [List.head_append_left (interleave_ne_nil hYRne) hAne]
    have e : (interleave YR.toList XR.toList).head (interleave_ne_nil hYRne)
        = YR.toList.head hYRne := by
      have e' : (interleave YR.toList XR.toList).head? =
          some (YR.toList.head hYRne) := by
        rw [interleave_head? hYRne, List.head?_eq_some_head hYRne]
      rw [List.head?_eq_some_head (interleave_ne_nil hYRne)] at e'
      exact Option.some_inj.mp e'
    rw [e]
    exact c3.S1U_Y (hYRS1 (Finset.mem_toList.mp (List.head_mem hYRne)))
  have hBlast : (t :: interleave YB.toList
      (((c3.SL.erase s).erase t) \ XR).toList).getLast hBne ∈ Y := by
    have hQne : interleave YB.toList
        (((c3.SL.erase s).erase t) \ XR).toList ≠ [] :=
      interleave_ne_nil hYBne
    have e : (t :: interleave YB.toList
        (((c3.SL.erase s).erase t) \ XR).toList).getLast? =
        some (YB.toList.getLast hYBne) := by
      rw [getLast?_cons_ne_nil hQne, interleave_getLast?_succ hlenYB,
        List.getLast?_eq_getLast_of_ne_nil hYBne]
    rw [List.getLast?_eq_getLast_of_ne_nil hBne] at e
    rw [Option.some_inj.mp e]
    exact c3.S2U_Y (hYBS2 (Finset.mem_toList.mp (List.getLast_mem hYBne)))
  exact bipathO_kill_Ymid hXY ⟨hA', hB', hnd'⟩ hmax' huxOut hwY c3.hux.1
    hAne hBne hAhead hBlast

/-- **Claim G1.** Every `w ∈ sc1` is red-adjacent to every `l ∈ SL`.
For `l = z` this is the definition of `sc1`; for `l ≠ z` a hypothetical
blue `w–l` edge gives `claimG_aux` with `s = z`, `t = l`. -/
theorem claimG1 (hXY : Disjoint X Y) (hI : c3.InternalFacts) :
    ∀ w ∈ c3.sc1, ∀ l ∈ c3.SL, G.Adj w l := by
  intro w hw l hl
  obtain ⟨hwY, hwS, hwz⟩ := (c3.mem_sc1).mp hw
  by_cases hlz : l = c3.z
  · subst hlz; exact hwz
  by_contra hwl
  exact c3.claimG_aux hXY hI hwY hwS c3.z_mem_SL hl
    (fun h ↦ hlz h.symm) hwz.symm hwl

/-- **Claim G2.** Every `w ∈ sc2` is blue-adjacent to every `l ∈ SL`.
For `l = z` this is the definition of `sc2`; for `l ≠ z` a hypothetical
red `w–l` edge gives `claimG_aux` with `s = l`, `t = z`. -/
theorem claimG2 (hXY : Disjoint X Y) (hI : c3.InternalFacts) :
    ∀ w ∈ c3.sc2, ∀ l ∈ c3.SL, ¬ G.Adj w l := by
  intro w hw l hl
  obtain ⟨hwY, hwS, hwz⟩ := (c3.mem_sc2).mp hw
  by_cases hlz : l = c3.z
  · subst hlz; exact hwz
  intro hwl
  exact c3.claimG_aux hXY hI hwY hwS hl c3.z_mem_SL
    hlz hwl.symm hwz

/-! ### Claim H1 -/

/-- **Claim H1.** Every `w ∈ L2` is blue-adjacent to every `u ∈ sc1`.
Assuming a red `w–u` edge, take `SL₁ ⊆ SL` of size `(r+1)/2` and
`b₀ ∈ S2U`; the bipath
`A' = interleave (S1U.toList ++ [u]) SL₁.toList ++ [w]`, `z' = b₀`,
`B' = interleave (SL ∖ SL₁).toList (S2U ∖ {b₀}).toList`
is a bipath on `S ∪ {w,u}`, strictly longer than the maximum. -/
theorem claimH1 (hXY : Disjoint X Y) (hI : c3.InternalFacts)
    (hC : c3.LeftoverC)
    (hG1 : ∀ w ∈ c3.sc1, ∀ l ∈ c3.SL, G.Adj w l) :
    ∀ w ∈ c3.L2, ∀ u ∈ c3.sc1, ¬ G.Adj w u := by
  intro w hw u hu hwu
  obtain ⟨hwX, hwS⟩ := (c3.mem_L2).mp hw
  obtain ⟨huY, huS, huz⟩ := (c3.mem_sc1).mp hu
  obtain ⟨hr, hsr⟩ := c3.parity_len hXY
  obtain ⟨cS1, cS2, cSL⟩ := c3.cards hXY
  -- pick `b₀ ∈ S2U`
  set b₀ := c3.B.getLast c3.hB with hb₀def
  have hb₀ : b₀ ∈ c3.S2U := c3.getLast_mem_S2U
  have hb₀Y := c3.S2U_Y hb₀
  -- `SL₁ ⊆ SL` with `(r+1)/2` elements
  obtain ⟨SL₁, hSL₁sub, hSL₁c⟩ := Finset.exists_subset_card_eq
    (s := c3.SL) (n := (c3.A.length + 1) / 2) (by
      rw [cSL]; have h2 := List.length_pos_of_ne_nil c3.hB; omega)
  -- `YB = S2U ∖ {b₀}` with `(s-1)/2` elements; `#(SL ∖ SL₁) = (s-1)/2`
  have hYBc : (c3.S2U.erase b₀).card = (c3.B.length - 1) / 2 := by
    rw [Finset.card_erase_of_mem hb₀, cS2]
    have h2 := List.length_pos_of_ne_nil c3.hB
    omega
  have hSL₂c : (c3.SL \ SL₁).card = (c3.B.length - 1) / 2 := by
    rw [Finset.card_sdiff_of_subset hSL₁sub, cSL, hSL₁c]
    have h1 := List.length_pos_of_ne_nil c3.hA
    have h2 := List.length_pos_of_ne_nil c3.hB
    omega
  -- red chain `P ++ [w] ++ [b₀]` where `P = interleave (S1U ++ [u]) SL₁`
  have hlenP : (c3.S1U.toList ++ [u]).length = SL₁.toList.length + 1 := by
    rw [List.length_append, List.length_cons, List.length_nil, toList_len,
      toList_len, cS1, hSL₁c]
  obtain ⟨hP, hPnd, hPm⟩ := interleave_pack hXY (c := Color.red)
    (S₁ := c3.S1U ∪ {u}) (S₂ := SL₁)
    (xs := c3.S1U.toList ++ [u]) (ys := SL₁.toList)
    (by
      rw [Finset.disjoint_left]
      intro a ha hb
      rcases Finset.mem_union.mp ha with ha | ha
      · exact Finset.disjoint_left.mp hXY.symm (c3.S1U_Y ha)
          (c3.SL_X (hSL₁sub hb))
      · rw [Finset.mem_singleton] at ha; subst ha
        exact Finset.disjoint_left.mp hXY.symm huY (c3.SL_X (hSL₁sub hb)))
    (by
      intro a ha b hb
      rcases Finset.mem_union.mp ha with ha | ha
      · exact adjXY_red_YX (hI.1 a ha b (hSL₁sub hb)) (c3.S1U_Y ha)
          (c3.SL_X (hSL₁sub hb))
      · rw [Finset.mem_singleton] at ha; rw [ha]
        exact adjXY_red_YX (hG1 u hu b (hSL₁sub hb)) huY
          (c3.SL_X (hSL₁sub hb)))
    (by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact Finset.mem_union_left _ (toList_mem a ha)
      · rw [List.mem_singleton] at ha; subst ha
        exact Finset.mem_union_right _ (Finset.mem_singleton_self _))
    (fun _ ↦ Finset.mem_toList.mp)
    (by
      apply nodup_append_disj (F₁ := c3.S1U) (F₂ := ({u} : Finset V))
      · exact toList_nodup
      · exact List.nodup_singleton _
      · exact fun _ ↦ toList_mem _
      · intro x hx
        rw [List.mem_singleton] at hx; subst hx
        exact Finset.mem_singleton_self _
      · rw [Finset.disjoint_singleton_right]
        exact fun h ↦ huS (c3.S1U_mem_S h))
    toList_nodup (by omega) (by omega)
  have hR1 : (interleave (c3.S1U.toList ++ [u]) SL₁.toList ++ [w]).IsChain
      (Color.adjXY G X Y .red) := by
    apply List.isChain_snoc' hP
    intro x hx
    rw [interleave_getLast?_succ hlenP,
      List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast?_singleton] at hx
    obtain rfl := Option.mem_some_iff.mp hx
    exact adjXY_red_YX hwu.symm huY hwX
  have hR : (interleave (c3.S1U.toList ++ [u]) SL₁.toList ++ [w] ++ [b₀]).IsChain
      (Color.adjXY G X Y .red) := by
    apply List.isChain_snoc' hR1
    intro x hx
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast?_singleton] at hx
    obtain rfl := Option.mem_some_iff.mp hx
    exact adjXY_red_XY (hC.2 w hw b₀ hb₀) hwX hb₀Y
  -- blue chain `b₀ :: Q` where `Q = interleave (SL ∖ SL₁) (S2U ∖ {b₀})`
  have hlenQ : (c3.SL \ SL₁).toList.length =
      (c3.S2U.erase b₀).toList.length := by
    rw [toList_len, toList_len, hSL₂c, hYBc]
  obtain ⟨hQ, hQnd, hQm⟩ := interleave_pack hXY (c := Color.blue)
    (S₁ := c3.SL \ SL₁) (S₂ := c3.S2U.erase b₀)
    (by
      rw [Finset.disjoint_left]
      exact fun a ha hb ↦ Finset.disjoint_left.mp hXY
        (c3.SL_X (Finset.sdiff_subset ha))
        (c3.S2U_Y ((Finset.mem_erase.mp hb).2)))
    (fun a ha b hb ↦
      ⟨Or.inl ⟨c3.SL_X (Finset.sdiff_subset ha),
        c3.S2U_Y ((Finset.mem_erase.mp hb).2)⟩,
       fun h ↦ hI.2 b ((Finset.mem_erase.mp hb).2) a
         (Finset.sdiff_subset ha) h.symm⟩)
    (fun _ ↦ Finset.mem_toList.mp) (fun _ ↦ Finset.mem_toList.mp)
    toList_nodup toList_nodup (by omega) (by omega)
  have hBl : (b₀ :: interleave (c3.SL \ SL₁).toList
      (c3.S2U.erase b₀).toList).IsChain (Color.adjXY G X Y .blue) := by
    apply List.isChain_cons.mpr
    refine ⟨?_, hQ⟩
    intro y hy
    by_cases hne : (c3.SL \ SL₁).toList = []
    · have h0 : (c3.SL \ SL₁).card = 0 := by
        rw [← toList_len]; exact List.length_eq_zero_iff.mpr hne
      have h0' : (c3.S2U.erase b₀).card = 0 := by
        rw [hYBc]; rw [hSL₂c] at h0; omega
      have e0 : (c3.S2U.erase b₀).toList = [] :=
        List.length_eq_zero_iff.mp (by rw [toList_len, h0'])
      simp only [hne, e0, interleave, List.head?] at hy
      exact (Option.not_mem_none _ hy).elim
    · rw [interleave_head? hne] at hy
      have hyS := Finset.sdiff_subset (toList_mem y (mem_of_mem_head? hy))
      exact adjXY_blue_YX (hI.2 b₀ hb₀ y hyS) hb₀Y (c3.SL_X hyS)
  -- nodup of `(P ++ [w]) ++ b₀ :: Q`
  have hnd : ((interleave (c3.S1U.toList ++ [u]) SL₁.toList ++ [w]) ++
      b₀ :: interleave (c3.SL \ SL₁).toList
        (c3.S2U.erase b₀).toList).Nodup := by
    apply nodup_append_disj
        (F₁ := c3.S1U ∪ ({u} : Finset V) ∪ SL₁ ∪ {w})
        (F₂ := ({b₀} : Finset V) ∪ ((c3.SL \ SL₁) ∪ c3.S2U.erase b₀))
    · apply nodup_append_disj
          (F₁ := c3.S1U ∪ ({u} : Finset V) ∪ SL₁) (F₂ := ({w} : Finset V))
      · exact hPnd
      · exact List.nodup_singleton _
      · intro x hx
        rcases hPm x hx with hx | hx
        · exact Finset.mem_union.mpr (Or.inl hx)
        · exact Finset.mem_union.mpr (Or.inr hx)
      · intro x hx
        rw [List.mem_singleton] at hx; subst hx
        exact Finset.mem_singleton_self _
      · rw [Finset.disjoint_singleton_right]
        intro hw'
        rcases Finset.mem_union.mp hw' with hw' | hw'
        · rcases Finset.mem_union.mp hw' with hw' | hw'
          · exact hwS (c3.S1U_mem_S hw')
          · rw [Finset.mem_singleton] at hw'; subst hw'
            exact Finset.disjoint_left.mp hXY hwX huY
        · exact hwS (c3.SL_mem_S (hSL₁sub hw'))
    · apply nodup_cons' (F := (c3.SL \ SL₁) ∪ c3.S2U.erase b₀)
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · exact Finset.disjoint_left.mp hXY (c3.SL_X (Finset.sdiff_subset h))
            hb₀Y
        · exact Finset.notMem_erase _ _ h
      · intro x hx
        rcases hQm x hx with hx | hx
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ hx
      · exact hQnd
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases hPm x hx with hx | hx
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inl hx)))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inr hx)))
      · rw [List.mem_singleton] at hx; subst hx
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
    · intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
      · rcases hQm x hx with hx | hx
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union_left _ hx))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union_right _ hx))
    · rw [Finset.disjoint_left]
      intro x hx hx2
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · rcases Finset.mem_union.mp hx with hx | hx
          · have hxY := c3.S1U_Y hx
            rcases Finset.mem_union.mp hx2 with hx2 | hx2
            · rw [Finset.mem_singleton] at hx2; subst hx2
              exact Finset.disjoint_left.mp (c3.disjoint_S1U_S2U hXY)
                hx hb₀
            · rcases Finset.mem_union.mp hx2 with hx2 | hx2
              · exact Finset.disjoint_left.mp hXY.symm hxY
                  (c3.SL_X (Finset.sdiff_subset hx2))
              · exact Finset.disjoint_left.mp (c3.disjoint_S1U_S2U hXY)
                  hx ((Finset.mem_erase.mp hx2).2)
          · rw [Finset.mem_singleton] at hx; subst hx
            rcases Finset.mem_union.mp hx2 with hx2 | hx2
            · rw [Finset.mem_singleton] at hx2; subst hx2
              exact huS (c3.S2U_mem_S hb₀)
            · rcases Finset.mem_union.mp hx2 with hx2 | hx2
              · exact huS (c3.SL_mem_S (Finset.sdiff_subset hx2))
              · exact huS (c3.S2U_mem_S ((Finset.mem_erase.mp hx2).2))
        · have hxX := c3.SL_X (hSL₁sub hx)
          rcases Finset.mem_union.mp hx2 with hx2 | hx2
          · rw [Finset.mem_singleton] at hx2; subst hx2
            exact Finset.disjoint_left.mp hXY hxX hb₀Y
          · rcases Finset.mem_union.mp hx2 with hx2 | hx2
            · exact (Finset.mem_sdiff.mp hx2).2 hx
            · exact Finset.disjoint_left.mp hXY hxX
                (c3.S2U_Y ((Finset.mem_erase.mp hx2).2))
      · rw [Finset.mem_singleton] at hx; subst hx
        rcases Finset.mem_union.mp hx2 with hx2 | hx2
        · rw [Finset.mem_singleton] at hx2; subst hx2
          exact hwS (c3.S2U_mem_S hb₀)
        · rcases Finset.mem_union.mp hx2 with hx2 | hx2
          · exact hwS (c3.SL_mem_S (Finset.sdiff_subset hx2))
          · exact hwS (c3.S2U_mem_S ((Finset.mem_erase.mp hx2).2))
  -- length: strictly longer than `c3`
  have hle := c3.hmax _ _ _ (Or.inl ⟨hR, hBl, hnd⟩ :
    IsBipathO G X Y (interleave (c3.S1U.toList ++ [u]) SL₁.toList ++ [w]) b₀
      (interleave (c3.SL \ SL₁).toList (c3.S2U.erase b₀).toList))
  have hlen' : bipathLen
      (interleave (c3.S1U.toList ++ [u]) SL₁.toList ++ [w]) b₀
      (interleave (c3.SL \ SL₁).toList (c3.S2U.erase b₀).toList) =
      c3.A.length + c3.B.length + 3 := by
    unfold bipathLen
    rw [List.length_append, interleave_length, interleave_length,
      List.length_append, List.length_cons, List.length_cons, List.length_nil,
      toList_len, toList_len, toList_len, toList_len,
      cS1, hSL₁c, hSL₂c, hYBc]
    have h1 := List.length_pos_of_ne_nil c3.hA
    have h2 := List.length_pos_of_ne_nil c3.hB
    omega
  rw [hlen'] at hle
  change _ ≤ c3.A.length + c3.B.length + 1 at hle
  omega

/-! ### Claim H2 -/

/-- **Claim H2.** Every `w ∈ L2` is red-adjacent to every `u ∈ sc2`.
Assuming a blue `w–u` edge, take `m ∈ S1U`, `SL₁ ⊆ SL` of size
`(r-1)/2` and set `SL₂ = SL ∖ SL₁`; the bipath
`A' = interleave (S1U ∖ {m}).toList SL₁.toList`, `z' = m`,
`B' = w :: u :: interleave SL₂.toList S2U.toList`
is a bipath on `S ∪ {w,u}`, strictly longer than the maximum. -/
theorem claimH2 (hXY : Disjoint X Y) (hI : c3.InternalFacts)
    (hC : c3.LeftoverC)
    (hG2 : ∀ w ∈ c3.sc2, ∀ l ∈ c3.SL, ¬ G.Adj w l) :
    ∀ w ∈ c3.L2, ∀ u ∈ c3.sc2, G.Adj w u := by
  intro w hw u hu
  by_contra hwu
  obtain ⟨hwX, hwS⟩ := (c3.mem_L2).mp hw
  obtain ⟨huY, huS, huz⟩ := (c3.mem_sc2).mp hu
  obtain ⟨hr, hsr⟩ := c3.parity_len hXY
  obtain ⟨cS1, cS2, cSL⟩ := c3.cards hXY
  -- pick `m ∈ S1U`
  set m := c3.A.head c3.hA with hmdef
  have hm : m ∈ c3.S1U := c3.head_mem_S1U
  have hmY := c3.S1U_Y hm
  -- `SL₁ ⊆ SL` with `(r-1)/2` elements
  obtain ⟨SL₁, hSL₁sub, hSL₁c⟩ := Finset.exists_subset_card_eq
    (s := c3.SL) (n := (c3.A.length - 1) / 2) (by
      rw [cSL]; have h2 := List.length_pos_of_ne_nil c3.hB; omega)
  -- `#(SL ∖ SL₁) = (s+1)/2`; `#(S1U ∖ {m}) = (r-1)/2`
  have hSL₂c : (c3.SL \ SL₁).card = (c3.B.length + 1) / 2 := by
    rw [Finset.card_sdiff_of_subset hSL₁sub, cSL, hSL₁c]
    have h1 := List.length_pos_of_ne_nil c3.hA
    have h2 := List.length_pos_of_ne_nil c3.hB
    omega
  have hXc : (c3.S1U.erase m).card = (c3.A.length - 1) / 2 := by
    rw [Finset.card_erase_of_mem hm, cS1]
    have h1 := List.length_pos_of_ne_nil c3.hA
    omega
  -- red chain `P ++ [m]` where `P = interleave (S1U ∖ {m}) SL₁`
  have hlenP : (c3.S1U.erase m).toList.length = SL₁.toList.length := by
    rw [toList_len, toList_len, hXc, hSL₁c]
  obtain ⟨hP, hPnd, hPm⟩ := interleave_pack hXY (c := Color.red)
    (S₁ := c3.S1U.erase m) (S₂ := SL₁)
    (by
      rw [Finset.disjoint_left]
      exact fun a ha hb ↦ Finset.disjoint_left.mp hXY.symm
        (c3.S1U_Y ((Finset.mem_erase.mp ha).2))
        (c3.SL_X (hSL₁sub hb)))
    (fun a ha b hb ↦ adjXY_red_YX
      (hI.1 a ((Finset.mem_erase.mp ha).2) b (hSL₁sub hb))
      (c3.S1U_Y ((Finset.mem_erase.mp ha).2)) (c3.SL_X (hSL₁sub hb)))
    (fun _ ↦ Finset.mem_toList.mp) (fun _ ↦ Finset.mem_toList.mp)
    toList_nodup toList_nodup (by omega) (by omega)
  have hR : (interleave (c3.S1U.erase m).toList SL₁.toList ++ [m]).IsChain
      (Color.adjXY G X Y .red) := by
    apply List.isChain_snoc' hP
    intro x hx
    rw [interleave_getLast?_eq hlenP] at hx
    by_cases hne : SL₁.toList = []
    · rw [hne] at hx
      simp only [List.getLast?] at hx
      exact (Option.not_mem_none _ hx).elim
    · have hxS := hSL₁sub (toList_mem x (mem_of_mem_getLast? hx))
      exact adjXY_red_XY (hI.1 m hm x hxS).symm (c3.SL_X hxS) hmY
  -- blue chain `m :: w :: u :: Q` where `Q = interleave (SL ∖ SL₁) S2U`
  have hlenQ : (c3.SL \ SL₁).toList.length = c3.S2U.toList.length := by
    rw [toList_len, toList_len, hSL₂c, cS2]
  have hSL₂ne : (c3.SL \ SL₁).toList ≠ [] := by
    intro e
    have e' : (c3.SL \ SL₁).toList.length = 0 := by rw [e]; rfl
    rw [toList_len, hSL₂c] at e'
    have h2 := List.length_pos_of_ne_nil c3.hB
    omega
  obtain ⟨hQ, hQnd, hQm⟩ := interleave_pack hXY (c := Color.blue)
    (S₁ := c3.SL \ SL₁) (S₂ := c3.S2U)
    (by
      rw [Finset.disjoint_left]
      exact fun a ha hb ↦ Finset.disjoint_left.mp hXY
        (c3.SL_X (Finset.sdiff_subset ha)) (c3.S2U_Y hb))
    (fun a ha b hb ↦ adjXY_blue_XY
      (fun h ↦ hI.2 b hb a (Finset.sdiff_subset ha) h.symm)
      (c3.SL_X (Finset.sdiff_subset ha)) (c3.S2U_Y hb))
    (fun _ ↦ Finset.mem_toList.mp) (fun _ ↦ Finset.mem_toList.mp)
    toList_nodup toList_nodup (by omega) (by omega)
  have hQc : (u :: interleave (c3.SL \ SL₁).toList c3.S2U.toList).IsChain
      (Color.adjXY G X Y .blue) := by
    apply List.isChain_cons.mpr
    refine ⟨?_, hQ⟩
    intro y hy
    rw [interleave_head? hSL₂ne] at hy
    have hyS := Finset.sdiff_subset (toList_mem y (mem_of_mem_head? hy))
    exact adjXY_blue_YX (hG2 u hu y hyS) huY (c3.SL_X hyS)
  have hQc' : (w :: u :: interleave (c3.SL \ SL₁).toList
      c3.S2U.toList).IsChain (Color.adjXY G X Y .blue) := by
    apply List.isChain_cons.mpr
    refine ⟨?_, hQc⟩
    intro y hy
    rw [List.head?_cons] at hy
    obtain rfl := Option.mem_some_iff.mp hy
    exact adjXY_blue_XY hwu hwX huY
  have hBl : (m :: w :: u :: interleave (c3.SL \ SL₁).toList
      c3.S2U.toList).IsChain (Color.adjXY G X Y .blue) := by
    apply List.isChain_cons.mpr
    refine ⟨?_, hQc'⟩
    intro y hy
    rw [List.head?_cons] at hy
    obtain rfl := Option.mem_some_iff.mp hy
    exact adjXY_blue_YX (fun h ↦ hC.1 w hw m hm h.symm) hmY hwX
  -- nodup of `P ++ m :: w :: u :: Q`
  have hnd : (interleave (c3.S1U.erase m).toList SL₁.toList ++
      m :: w :: u :: interleave (c3.SL \ SL₁).toList
        c3.S2U.toList).Nodup := by
    apply nodup_append_disj
        (F₁ := c3.S1U.erase m ∪ SL₁)
        (F₂ := ({m} : Finset V) ∪ ({w} ∪ ({u} ∪
          ((c3.SL \ SL₁) ∪ c3.S2U))))
    · exact hPnd
    · apply nodup_cons' (F := ({w} : Finset V) ∪ ({u} ∪
          ((c3.SL \ SL₁) ∪ c3.S2U)))
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · rw [Finset.mem_singleton] at h; subst h
          exact Finset.disjoint_left.mp hXY hwX hmY
        · rcases Finset.mem_union.mp h with h | h
          · rw [Finset.mem_singleton] at h; subst h
            exact huS (c3.S1U_mem_S hm)
          · rcases Finset.mem_union.mp h with h | h
            · exact Finset.disjoint_left.mp hXY.symm hmY
                (c3.SL_X (Finset.sdiff_subset h))
            · exact Finset.disjoint_left.mp (c3.disjoint_S1U_S2U hXY)
                hm h
      · intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
        · rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
              (Or.inl (Finset.mem_singleton_self _))))
          · rcases hQm x hx with hx | hx
            · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
                (Or.inr (Finset.mem_union_left _ hx))))
            · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
                (Or.inr (Finset.mem_union_right _ hx))))
      · apply nodup_cons' (F := ({u} : Finset V) ∪
            ((c3.SL \ SL₁) ∪ c3.S2U))
        · intro h
          rcases Finset.mem_union.mp h with h | h
          · rw [Finset.mem_singleton] at h; subst h
            exact Finset.disjoint_left.mp hXY hwX huY
          · rcases Finset.mem_union.mp h with h | h
            · exact hwS (c3.SL_mem_S (Finset.sdiff_subset h))
            · exact hwS (c3.S2U_mem_S h)
        · intro x hx
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
          · rcases hQm x hx with hx | hx
            · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union_left _ hx))
            · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union_right _ hx))
        · apply nodup_cons' (F := (c3.SL \ SL₁) ∪ c3.S2U)
          · intro h
            rcases Finset.mem_union.mp h with h | h
            · exact huS (c3.SL_mem_S (Finset.sdiff_subset h))
            · exact huS (c3.S2U_mem_S h)
          · intro x hx
            rcases hQm x hx with hx | hx
            · exact Finset.mem_union_left _ hx
            · exact Finset.mem_union_right _ hx
          · exact hQnd
    · intro x hx
      rcases hPm x hx with hx | hx
      · exact Finset.mem_union_left _ hx
      · exact Finset.mem_union_right _ hx
    · intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
      · rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
            (Or.inl (Finset.mem_singleton_self _))))
        · rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
              (Or.inr (Finset.mem_union.mpr
                (Or.inl (Finset.mem_singleton_self _))))))
          · rcases hQm x hx with hx | hx
            · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
                (Or.inr (Finset.mem_union.mpr
                  (Or.inr (Finset.mem_union_left _ hx))))))
            · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
                (Or.inr (Finset.mem_union.mpr
                  (Or.inr (Finset.mem_union_right _ hx))))))
    · rw [Finset.disjoint_left]
      intro x hx hx2
      rcases Finset.mem_union.mp hx with hx | hx
      · have hxS1 := (Finset.mem_erase.mp hx).2
        have hxY := c3.S1U_Y hxS1
        rcases Finset.mem_union.mp hx2 with hx2 | hx2
        · exact (Finset.mem_erase.mp hx).1 (Finset.mem_singleton.mp hx2)
        · rcases Finset.mem_union.mp hx2 with hx2 | hx2
          · rw [Finset.mem_singleton] at hx2; subst hx2
            exact Finset.disjoint_left.mp hXY.symm hxY hwX
          · rcases Finset.mem_union.mp hx2 with hx2 | hx2
            · rw [Finset.mem_singleton] at hx2; subst hx2
              exact huS (c3.S1U_mem_S hxS1)
            · rcases Finset.mem_union.mp hx2 with hx2 | hx2
              · exact Finset.disjoint_left.mp hXY.symm hxY
                  (c3.SL_X (Finset.sdiff_subset hx2))
              · exact Finset.disjoint_left.mp (c3.disjoint_S1U_S2U hXY)
                  hxS1 hx2
      · have hxX := c3.SL_X (hSL₁sub hx)
        rcases Finset.mem_union.mp hx2 with hx2 | hx2
        · rw [Finset.mem_singleton] at hx2; subst hx2
          exact Finset.disjoint_left.mp hXY hxX hmY
        · rcases Finset.mem_union.mp hx2 with hx2 | hx2
          · rw [Finset.mem_singleton] at hx2; subst hx2
            exact hwS (c3.SL_mem_S (hSL₁sub hx))
          · rcases Finset.mem_union.mp hx2 with hx2 | hx2
            · rw [Finset.mem_singleton] at hx2; subst hx2
              exact huS (c3.SL_mem_S (hSL₁sub hx))
            · rcases Finset.mem_union.mp hx2 with hx2 | hx2
              · exact (Finset.mem_sdiff.mp hx2).2 hx
              · exact Finset.disjoint_left.mp hXY hxX
                  (c3.S2U_Y hx2)
  -- length: strictly longer than `c3`
  have hle := c3.hmax _ _ _ (Or.inl ⟨hR, hBl, hnd⟩ :
    IsBipathO G X Y (interleave (c3.S1U.erase m).toList SL₁.toList) m
      (w :: u :: interleave (c3.SL \ SL₁).toList c3.S2U.toList))
  have hlen' : bipathLen
      (interleave (c3.S1U.erase m).toList SL₁.toList) m
      (w :: u :: interleave (c3.SL \ SL₁).toList c3.S2U.toList) =
      c3.A.length + c3.B.length + 3 := by
    unfold bipathLen
    rw [interleave_length, List.length_cons, List.length_cons,
      interleave_length, toList_len, toList_len, toList_len, toList_len,
      hXc, hSL₁c, hSL₂c, cS2]
    have h1 := List.length_pos_of_ne_nil c3.hA
    have h2 := List.length_pos_of_ne_nil c3.hB
    omega
  rw [hlen'] at hle
  change _ ≤ c3.A.length + c3.B.length + 1 at hle
  omega

end Case3Data

/-- **Theorem 3, case (iii), claims (G) and (H).** -/
theorem ghfacts (c3 : Case3Data G X Y) (hXY : Disjoint X Y)
    (hI : c3.InternalFacts) (hC : c3.LeftoverC) (hux2 : c3.HasUx2) :
    c3.GHfacts :=
  ⟨c3.claimG1 hXY hI, c3.claimG2 hXY hI,
    c3.claimH1 hXY hI hC (c3.claimG1 hXY hI),
    c3.claimH2 hXY hI hC (c3.claimG2 hXY hI)⟩

end JSP415
