import JSP415.BipLemmas

open Finset

namespace JSP415

open bip_ramsey_path

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {X Y : Finset V}

-- test: count elements of a chain that lie in X
theorem chain_countX (hXY : Disjoint X Y) {c : Color} {l : List V}
    (hch : l.IsChain (Color.adjXY G X Y c)) :
    (l.filter (· ∈ X)).length =
      (l.length + if l.head?.elim false (· ∈ X) then 1 else 0) / 2 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [List.filter_cons, List.length_cons, List.length_nil,
        List.head?_cons, Option.elim]
      by_cases ha : a ∈ X <;> simp [ha]
    | cons b s =>
      have hab : Color.adjXY G X Y c a b := by
        have := List.isChain_cons.mp hch
        exact this.1 b (List.head?_cons _ _)
      have htail : (b :: s).IsChain (Color.adjXY G X Y c) := (List.isChain_cons.mp hch).2
      have ihs := ih htail
      have hop : acrossXY X Y a b := hab.1
      simp only [List.filter_cons, List.length_cons, List.head?_cons, Option.elim]
      have hs : ((if (b :: s).head?.elim false (· ∈ X) then 1 else 0)) =
          if b ∈ X then 1 else 0 := by simp
      rw [hs] at ihs
      rcases hop with ⟨haX, hbY⟩ | ⟨haY, hbX⟩
      · have h1 : (b :: s).filter (· ∈ X) = s.filter (· ∈ X) :=
          List.filter_cons_of_neg (by simp [hXY.not_mem_of_mem_left hbY])
        have h2 : (a :: b :: s).filter (· ∈ X) = a :: (b :: s).filter (· ∈ X) :=
          List.filter_cons_of_pos haX
        rw [h1] at ihs; rw [h2]
        simp [haX, hXY.not_mem_of_mem_left hbY]
        omega
      · have h1 : (b :: s).filter (· ∈ X) = b :: s.filter (· ∈ X) :=
          List.filter_cons_of_pos hbX
        have h2 : (a :: b :: s).filter (· ∈ X) = (b :: s).filter (· ∈ X) :=
          List.filter_cons_of_neg (by simp [hXY.not_mem_of_mem_right haY])
        rw [h1] at ihs; rw [h2]
        simp [hbX, hXY.not_mem_of_mem_right haY]
        omega

end JSP415
