import JSP415.GLIface
import JSP415.GLScratchA
import JSP415.GLScratchW

/-!
# GLScratchLC — Gyárfás–Lehel Thm 3: claims B′, C, C′
-/

open Finset
open scoped List

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

/-! ### List helpers -/

/-- `List.take` of a chain is a chain. -/
theorem isChain_take_of {R : V → V → Prop} {l : List V} (k : ℕ)
    (h : l.IsChain R) : (l.take k).IsChain R := by
  have h' : (l.take k ++ l.drop k).IsChain R := by rwa [List.take_append_drop]
  exact h'.left_of_append

/-- `List.drop` of a chain is a chain. -/
theorem isChain_drop_of {R : V → V → Prop} {l : List V} (k : ℕ)
    (h : l.IsChain R) : (l.drop k).IsChain R := by
  have h' : (l.take k ++ l.drop k).IsChain R := by rwa [List.take_append_drop]
  exact h'.right_of_append

/-- `head?` of a nonempty `take` equals `head?` of the list. -/
theorem head?_take {l : List V} {k : ℕ} (hk : 0 < k) (hkl : k ≤ l.length) :
    (l.take k).head? = l.head? := by
  have hne : l.take k ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_take]; omega
  have hne' : l ≠ [] := List.ne_nil_iff_length_pos.mpr (by omega)
  rw [List.head?_eq_some_head hne, List.head?_eq_some_head hne']
  congr 1
  rw [List.head_eq_getElem, List.getElem_take, List.head_eq_getElem]

/-- `getLast?` of a nonempty `take` is `l[k-1]`. -/
theorem getLast?_take {l : List V} {k : ℕ} (hk : 0 < k) (hkl : k ≤ l.length) :
    (l.take k).getLast? = some (l[k - 1]'(by omega)) := by
  have hne : l.take k ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_take]; omega
  rw [List.getLast?_eq_getLast hne]
  congr 1
  rw [List.getLast_eq_getElem, List.getElem_take]
  congr 1
  rw [List.length_take, Nat.min_eq_left hkl]

/-- `head?` of a nonempty `drop` is `l[k]`. -/
theorem head?_drop {l : List V} {k : ℕ} (hk : k < l.length) :
    (l.drop k).head? = some (l[k]'hk) := by
  have hne : l.drop k ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_drop]; omega
  rw [List.head?_eq_some_head hne]
  congr 1
  rw [List.head_eq_getElem]
  exact List.getElem_drop

/-- `getLast?` of a nonempty `drop` is the last element of `l`. -/
theorem getLast?_drop {l : List V} {k : ℕ} (hk : k < l.length) :
    (l.drop k).getLast? = some (l[l.length - 1]'(by omega)) := by
  have hne : l.drop k ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_drop]; omega
  rw [List.getLast?_eq_getLast hne]
  congr 1
  rw [List.getLast_eq_getElem, List.getElem_drop]
  congr 1
  rw [List.length_drop]; omega

/-- `Q.tail.reverse ++ [Q.head] = Q.reverse` for nonempty `Q`. -/
theorem tail_reverse_cons_head {Q : List V} (hQ : Q ≠ []) :
    Q.tail.reverse ++ [Q.head hQ] = Q.reverse := by
  conv_rhs => rw [← List.cons_head_tail hQ, List.reverse_cons]

/-- `Q.tail.reverse ++ Q.head :: R = Q.reverse ++ R` for nonempty `Q`. -/
theorem tail_rev_cons_head_app {Q R : List V} (hQ : Q ≠ []) :
    Q.tail.reverse ++ (Q.head hQ :: R) = Q.reverse ++ R := by
  conv_lhs => rw [show Q.head hQ :: R = [Q.head hQ] ++ R from rfl]
  rw [← List.append_assoc, tail_reverse_cons_head hQ]

/-- The "midpoint-insertion" vertex list unfolds to the rotated form. -/
theorem rot_vertex_eq {w z : V} {P Q R : List V} (hQ : Q ≠ []) :
    (w :: P.reverse ++ z :: Q.tail.reverse) ++ Q.head hQ :: R
      = w :: P.reverse ++ z :: (Q.reverse ++ R) := by
  simp only [List.append_assoc, List.cons_append]
  rw [tail_rev_cons_head_app hQ]

/-- The "midpoint-insertion" chain list unfolds to the rotated form. -/
theorem rot_chain_eq {w z : V} {P Q : List V} (hQ : Q ≠ []) :
    (w :: P.reverse ++ z :: Q.tail.reverse) ++ [Q.head hQ]
      = w :: P.reverse ++ z :: Q.reverse := by
  rw [rot_vertex_eq hQ (R := []), List.append_nil]

/-- The rotated vertex list is a permutation of `w :: (P ++ Q) ++ z :: R`. -/
theorem perm_rot_vertex {w z : V} {P Q R : List V} (hQ : Q ≠ []) :
    List.Perm
      ((w :: P.reverse ++ z :: Q.tail.reverse) ++ Q.head hQ :: R)
      (w :: (P ++ Q) ++ z :: R) := by
  rw [rot_vertex_eq hQ]
  calc w :: P.reverse ++ z :: (Q.reverse ++ R)
      ~ w :: z :: (P.reverse ++ (Q.reverse ++ R)) := List.perm_middle.cons w
    _ ~ w :: z :: (P ++ (Q ++ R)) := by
        apply List.Perm.cons; apply List.Perm.cons
        exact ((List.reverse_perm _).append_right _).trans
          (((List.reverse_perm _).append_right _).append_left _)
    _ ~ w :: (P ++ Q) ++ z :: R := by
        apply List.Perm.cons
        rw [← List.append_assoc]
        exact List.perm_middle.symm

/-- Vertex permutation for the rotation with a fresh midpoint `m`. -/
theorem perm_rot_vertex2 {z m : V} {P Q R : List V} :
    List.Perm ((P.reverse ++ z :: Q.reverse) ++ m :: R)
      ((P ++ Q) ++ z :: m :: R) := by
  rw [show (P.reverse ++ z :: Q.reverse) ++ m :: R
        = P.reverse ++ z :: (Q.reverse ++ (m :: R)) from by
        rw [List.append_assoc, List.cons_append]]
  calc P.reverse ++ z :: (Q.reverse ++ (m :: R))
      ~ z :: (P.reverse ++ (Q.reverse ++ (m :: R))) := List.perm_middle
    _ ~ z :: (P ++ (Q ++ (m :: R))) := by
        apply List.Perm.cons
        exact ((List.reverse_perm _).append_right _).trans
          (((List.reverse_perm _).append_right _).append_left _)
    _ ~ (P ++ Q) ++ z :: m :: R := by
        rw [← List.append_assoc]
        exact List.perm_middle.symm

/-! ### Side bookkeeping in `adjXY` chains -/

/-- In an `adjXY` chain whose first element lies in `Y`, elements at even
positions lie in `Y`. -/
theorem adjXY_mem_Y_of_even {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y)
    {p : ℕ} (hp : p < l.length) (hpar : p % 2 = 0)
    (h0 : l[0]'(by omega) ∈ Y) : l[p] ∈ Y :=
  (Color.adjXY.same_side h hXY (by omega) hp (Nat.zero_le p) (by omega)).2.mp h0

/-- In an `adjXY` chain whose first element lies in `Y`, elements at odd
positions lie in `X`. -/
theorem adjXY_mem_X_of_odd {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y)
    {p : ℕ} (hp : p < l.length) (hpar : p % 2 = 1)
    (h0 : l[0]'(by omega) ∈ Y) : l[p] ∈ X :=
  (Color.adjXY.opp_side h hXY (by omega) hp (Nat.zero_le p) (by omega)).2.mp h0

/-- In an `adjXY` chain whose first element lies in `X`, elements at even
positions lie in `X`. -/
theorem adjXY_mem_X_of_even {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y)
    {p : ℕ} (hp : p < l.length) (hpar : p % 2 = 0)
    (h0 : l[0]'(by omega) ∈ X) : l[p] ∈ X :=
  (Color.adjXY.same_side h hXY (by omega) hp (Nat.zero_le p) (by omega)).1.mp h0

/-- In an `adjXY` chain whose first element lies in `X`, elements at odd
positions lie in `Y`. -/
theorem adjXY_mem_Y_of_odd {c : Color} {l : List V}
    (h : l.IsChain (Color.adjXY G X Y c)) (hXY : Disjoint X Y)
    {p : ℕ} (hp : p < l.length) (hpar : p % 2 = 1)
    (h0 : l[0]'(by omega) ∈ X) : l[p] ∈ Y :=
  (Color.adjXY.opp_side h hXY (by omega) hp (Nat.zero_le p) (by omega)).1.mp h0

end JSP415
