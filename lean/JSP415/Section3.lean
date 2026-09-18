import JSP415.Defs
import JSP415.Gerencser
import JSP415.BipLemmas

/-!
# Section 3 of PVW24: the inductive proof

Lemmas 3.1–3.3, Proposition 3.4, and the main Theorem 1.3.

Instead of the paper's `f(n,χ)` (least size of a same-colour monochromatic
path cover) we work directly with `HasCoverLe`/`HasCoverLt`/`AllCoverLt`:
`f(n,χ) ≤ b` iff `HasCoverLe G b`, and `f(m) < √m + C₁` for all `m < n` is
the strong-induction hypothesis `∀ m < n, AllCoverLt m (√m + C₁)`.
-/

open Finset

namespace JSP415

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PVW24 Lemma 3.1 (overlap lemma).**  If a large set `S` is covered by few
red paths and also by few blue paths, the induction hypothesis upgrades to a
strong bound at level `n`.

The hypothesis `S.Nonempty` is needed: the proof deletes `S` and applies the
induction hypothesis at `m = n - |S| < n`.  Without it the statement is false
already at `n = 0` (with `k = 0`, `S = ∅` and `C₁ < C₂ < 0` all hypotheses hold
while `HasCoverLe G C₂` fails, every cover having nonnegative cardinality). -/
theorem overlap_bound {n : ℕ} {C₁ C₂ : ℝ}
    (hind : ∀ m < n, AllCoverLt m (Real.sqrt m + C₁))
    (G : SimpleGraph (Fin n)) {k : ℕ}
    (PR : Fin k → VertPath (Fin n)) (hPR : ∀ i, (PR i).IsMonochromatic G .red)
    (QB : Fin k → VertPath (Fin n)) (hQB : ∀ i, (QB i).IsMonochromatic G .blue)
    (S : Finset (Fin n)) (hSne : S.Nonempty)
    (hS : ∀ s ∈ S, (∃ i, s ∈ PR i) ∧ (∃ i, s ∈ QB i))
    (hineq : Real.sqrt (n - S.card : ℝ) + C₁ + k ≤ Real.sqrt n + C₂) :
    HasCoverLe G (Real.sqrt n + C₂) := by
  classical
  -- Deleting `S` leaves `m = n - |S| < n` vertices.
  have hcardS : 0 < S.card := Finset.card_pos.mpr hSne
  have hSle : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hn : 0 < n := hcardS.trans_le hSle
  have hm : n - S.card < n := Nat.sub_lt hn hcardS
  have hcardW : Fintype.card ↥Sᶜ = n - S.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  -- Induction hypothesis on the induced colouring of `Sᶜ`.
  obtain ⟨c₀, P₀, ⟨hmono₀, hcov₀⟩, hlt₀⟩ :=
    hind (n - S.card) hm ↥Sᶜ hcardW (inducedColoring G Sᶜ)
  -- Normalise `hineq`: its `↑n - ↑#S` is `↑(n - #S)` since `#S ≤ n`.
  have hcast : ((n - S.card : ℕ) : ℝ) = (n : ℝ) - S.card := Nat.cast_sub hSle
  rw [← hcast] at hineq
  have hinj : Function.Injective (Subtype.val : ↥Sᶜ → Fin n) := Subtype.val_injective
  have hmapinj : Function.Injective fun p : VertPath ↥Sᶜ ↦ p.map Subtype.val hinj :=
    fun p q hpq ↦
      VertPath.ext (List.map_injective_iff.mpr hinj (congrArg VertPath.toList hpq))
  -- Push the `Sᶜ`-cover forward and adjoin the `k` given paths of colour `c₀`.
  cases c₀ with
  | red =>
    refine ⟨.red, P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪ univ.image PR,
      ⟨⟨?_, ?_⟩, ?_⟩⟩
    · intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
        exact (hmono₀ p hp).map hinj
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
        exact hPR i
    · intro v
      by_cases hvS : v ∈ S
      · obtain ⟨⟨i, hi⟩, -⟩ := hS v hvS
        exact ⟨PR i, Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), hi⟩
      · obtain ⟨p, hp, hvp⟩ := hcov₀ ⟨v, Finset.mem_compl.mpr hvS⟩
        exact ⟨p.map Subtype.val hinj, Finset.mem_union_left _
          (Finset.mem_map.mpr ⟨p, hp, rfl⟩),
          VertPath.mem_map.mpr ⟨⟨v, Finset.mem_compl.mpr hvS⟩, hvp, rfl⟩⟩
    · have him : (univ.image PR).card ≤ k := by
        calc (univ.image PR).card ≤ univ.card := Finset.card_image_le
        _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      have hcard : ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪
            univ.image PR).card : ℝ) ≤ P₀.card + k := by
        calc ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪
                univ.image PR).card : ℝ)
            ≤ ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩).card : ℝ) +
              ((univ.image PR).card : ℝ) := by
                exact_mod_cast Finset.card_union_le _ _
          _ ≤ P₀.card + k := by
              rw [Finset.card_map]
              have him' : ((univ.image PR).card : ℝ) ≤ k := by exact_mod_cast him
              linarith
      exact le_of_lt (lt_of_lt_of_le
        (lt_of_le_of_lt hcard (by linarith [hlt₀])) hineq)
  | blue =>
    refine ⟨.blue, P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪ univ.image QB,
      ⟨⟨?_, ?_⟩, ?_⟩⟩
    · intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
        exact (hmono₀ p hp).map hinj
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
        exact hQB i
    · intro v
      by_cases hvS : v ∈ S
      · obtain ⟨-, ⟨i, hi⟩⟩ := hS v hvS
        exact ⟨QB i, Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), hi⟩
      · obtain ⟨p, hp, hvp⟩ := hcov₀ ⟨v, Finset.mem_compl.mpr hvS⟩
        exact ⟨p.map Subtype.val hinj, Finset.mem_union_left _
          (Finset.mem_map.mpr ⟨p, hp, rfl⟩),
          VertPath.mem_map.mpr ⟨⟨v, Finset.mem_compl.mpr hvS⟩, hvp, rfl⟩⟩
    · have him : (univ.image QB).card ≤ k := by
        calc (univ.image QB).card ≤ univ.card := Finset.card_image_le
        _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      have hcard : ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪
            univ.image QB).card : ℝ) ≤ P₀.card + k := by
        calc ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩ ∪
                univ.image QB).card : ℝ)
            ≤ ((P₀.map ⟨fun p ↦ p.map Subtype.val hinj, hmapinj⟩).card : ℝ) +
              ((univ.image QB).card : ℝ) := by
                exact_mod_cast Finset.card_union_le _ _
          _ ≤ P₀.card + k := by
              rw [Finset.card_map]
              have him' : ((univ.image QB).card : ℝ) ≤ k := by exact_mod_cast him
              linarith
      exact le_of_lt (lt_of_lt_of_le
        (lt_of_le_of_lt hcard (by linarith [hlt₀])) hineq)

/-- **PVW24 Lemma 3.1, second part.**  The two-path special case: a set of
size `≥ 2Δ√n` covered by one red and one blue path already gives the bound,
where `Δ = C₁ − C₂ + 1`. -/
theorem overlap_bound_pair {n : ℕ} {C₁ C₂ : ℝ} (hC : C₂ ≤ C₁)
    (hind : ∀ m < n, AllCoverLt m (Real.sqrt m + C₁))
    (G : SimpleGraph (Fin n))
    (P : VertPath (Fin n)) (hP : P.IsMonochromatic G .red)
    (Q : VertPath (Fin n)) (hQ : Q.IsMonochromatic G .blue)
    (S : Finset (Fin n))
    (hS : ∀ s ∈ S, s ∈ P ∧ s ∈ Q)
    (hcard : 2 * (C₁ - C₂ + 1) * Real.sqrt n ≤ (S.card : ℝ)) :
    HasCoverLe G (Real.sqrt n + C₂) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0` is impossible: `P` is a nonempty list of `Fin 0` vertices.
    rcases P with ⟨l, hne, -⟩
    cases l with
    | nil => exact absurd rfl hne
    | cons v _ => exact absurd v.isLt (Nat.not_lt_zero _)
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn'
    have hΔ : 0 ≤ C₁ - C₂ + 1 := by linarith
    have hΔpos : (0 : ℝ) < C₁ - C₂ + 1 := by linarith
    have hSle : S.card ≤ n := by simpa using Finset.card_le_univ S
    -- `|S| ≥ 2Δ√n > 0`, so `S` is nonempty.
    have hSpos : (0 : ℝ) < (S.card : ℝ) :=
      lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) hΔpos) hsn) hcard
    have hSne : S.Nonempty :=
      Finset.card_pos.mp (by exact_mod_cast hSpos)
    -- Since `2Δ√n ≤ |S| ≤ n` we get `Δ ≤ √n`.
    have hΔle : C₁ - C₂ + 1 ≤ Real.sqrt n := by
      have h1 : 2 * (C₁ - C₂ + 1) * Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by
        refine hcard.trans ?_
        rw [Real.mul_self_sqrt hn'.le]
        exact_mod_cast hSle
      have h2 : 2 * (C₁ - C₂ + 1) ≤ Real.sqrt n :=
        le_of_mul_le_mul_right h1 hsn
      linarith
    -- `(√n - Δ)² = n - 2Δ√n + Δ² ≥ n - |S|`, hence `√(n - |S|) ≤ √n - Δ`.
    have hsqrt : Real.sqrt ((n - S.card : ℕ) : ℝ) ≤
        Real.sqrt n - (C₁ - C₂ + 1) := by
      rw [Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ Real.sqrt n - (C₁ - C₂ + 1))]
      rw [Nat.cast_sub hSle]
      have hsq : (Real.sqrt n - (C₁ - C₂ + 1)) ^ 2 =
          (n : ℝ) - 2 * (C₁ - C₂ + 1) * Real.sqrt n + (C₁ - C₂ + 1) ^ 2 := by
        have h2 := Real.sq_sqrt hn'.le
        ring_nf
        linarith
      rw [hsq]
      linarith [hcard, sq_nonneg (C₁ - C₂ + 1)]
    -- Apply `overlap_bound` with `k = 1`, the families `{P}` and `{Q}`.
    exact overlap_bound hind G (fun _ : Fin 1 ↦ P) (fun _ ↦ hP)
      (fun _ : Fin 1 ↦ Q) (fun _ ↦ hQ) S hSne
      (fun s hs ↦ ⟨⟨0, (hS s hs).1⟩, ⟨0, (hS s hs).2⟩⟩)
      (by rw [← Nat.cast_sub hSle, Nat.cast_one]; linarith [hsqrt])

/-- **PVW24 Lemma 3.2 (long-path structure).**  If `χ` admits no cover of size
`≤ √n + C₂`, there is a monochromatic path `P` of colour `γ` leaving out few
vertices, such that every outside vertex has at most `2Δ√n` `γ`-neighbours on
`P`, where `Δ = C₁ − C₂ + 1`. -/
theorem long_path_structure {n : ℕ} {C₁ C₂ : ℝ} (hC : C₂ ≤ C₁)
    (hn : 10 ^ 4 * (C₁ - C₂ + 1) ^ 4 < (n : ℝ))
    (hind : ∀ m < n, AllCoverLt m (Real.sqrt m + C₁))
    (G : SimpleGraph (Fin n)) (hG : ¬ HasCoverLe G (Real.sqrt n + C₂)) :
    ∃ c : Color, ∃ P : VertPath (Fin n), P.IsMonochromatic G c ∧
      ((n : ℝ) - P.toList.length ≤ Real.sqrt n + 10 * (C₁ - C₂ + 1) * n ^ ((1 : ℝ) / 4)) ∧
      ∀ y ∉ P.toList,
        (Set.ncard {x : Fin n | x ∈ P.toList ∧ Color.adj G c x y} : ℝ) ≤
          2 * (C₁ - C₂ + 1) * Real.sqrt n := by
  sorry

section TailPairing

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- Build a blue path `ya — a ⋯ b — yb` through an infix `a :: m ++ [b]` of a
blue chain `l`, where `ya, yb` are fresh vertices (off `l`, distinct) that are
blue-adjacent to the endpoints `a, b`.  This is the pair path of Lemma 3.3:
the interior is a segment of `P`, so it may share vertices with `P` — covers
need not be disjoint. -/
private theorem mk_pair_path {l : List (Fin n)}
    (hnodup : l.Nodup) {m : List (Fin n)} {ya yb a b : Fin n}
    (hinfix : (a :: m ++ [b]) <:+: l)
    (hm : (a :: m ++ [b]).IsChain (Color.adj G .blue))
    (hya : ya ∉ l) (hyb : yb ∉ l) (hyy : ya ≠ yb)
    (ha : Color.adj G .blue ya a) (hb : Color.adj G .blue b yb) :
    ∃ p : VertPath (Fin n), p.IsMonochromatic G .blue ∧ ya ∈ p.toList ∧
      yb ∈ p.toList := by
  have hsub := hinfix.sublist
  have hmn : (a :: m ++ [b]).Nodup := hnodup.sublist hsub
  refine ⟨⟨ya :: (a :: m ++ [b]) ++ [yb], by simp, ?_⟩, ?_, ?_, ?_⟩
  · -- Nodup: `ya`, `yb` are fresh and distinct, the interior is nodup.
    rw [List.nodup_append, List.nodup_cons]
    refine ⟨⟨?_, hmn⟩, List.nodup_singleton yb, ?_⟩
    · intro hmem
      exact hya (hsub.mem hmem)
    · intro x hx y hy
      rw [List.mem_singleton] at hy
      subst hy
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hyy
      · exact fun h => hyb (h ▸ hsub.mem hx)
  · -- IsChain: boundary edges `ya—a` and `b—yb` are blue.
    refine List.IsChain.append ?_ (List.isChain_singleton yb) ?_
    · refine hm.cons (fun y hy => ?_)
      have hd : (a :: m ++ [b]).head? = some a := by
        simp
      rw [hd, Option.mem_some] at hy
      subst y
      exact ha
    · intro x hx y hy
      rw [List.head?_cons, Option.mem_some] at hy
      have hx' : (ya :: (a :: m ++ [b])).getLast? = some b := by
        rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_concat]
      rw [hx', Option.mem_some] at hx
      subst x
      subst y
      exact hb
  · show ya ∈ ya :: (a :: m ++ [b]) ++ [yb]
    exact List.mem_append_left _ List.mem_cons_self
  · show yb ∈ ya :: (a :: m ++ [b]) ++ [yb]
    exact List.mem_append_right _ (List.mem_singleton_self yb)

/-- Two fresh vertices `y₁ y₂` with prescribed blue neighbours `u v` on a blue
chain `l` are joined by a single blue path through a segment of `l`. -/
private theorem pair_path {l : List (Fin n)}
    (hchain : l.IsChain (Color.adj G .blue)) (hnodup : l.Nodup)
    {y₁ y₂ u v : Fin n} (hy1 : y₁ ∉ l) (hy2 : y₂ ∉ l) (hyy : y₁ ≠ y₂)
    (hu : u ∈ l) (hv : v ∈ l)
    (h1 : Color.adj G .blue u y₁) (h2 : Color.adj G .blue v y₂) :
    ∃ p : VertPath (Fin n), p.IsMonochromatic G .blue ∧ y₁ ∈ p.toList ∧
      y₂ ∈ p.toList := by
  obtain ⟨as, bs, rfl, -⟩ := List.eq_append_cons_of_mem hu
  by_cases hv' : v ∈ as
  · -- `v` occurs before `u`: the segment is `v :: bs' ++ [u]`.
    obtain ⟨as', bs', rfl, -⟩ := List.eq_append_cons_of_mem hv'
    have hinfix : (v :: bs' ++ [u]) <:+: (as' ++ v :: bs') ++ u :: bs :=
      ⟨as', bs, by simp [List.append_assoc]⟩
    obtain ⟨p, hp, hp1, hp2⟩ := mk_pair_path G hnodup hinfix
      (hchain.infix hinfix) hy2 hy1 hyy.symm (Color.adj_symm G h2) h1
    exact ⟨p, hp, hp2, hp1⟩
  · have hvmem : v ∈ u :: bs := by
      have h := hv
      rw [List.mem_append] at h
      exact h.resolve_left hv'
    rw [List.mem_cons] at hvmem
    rcases hvmem with huv | hvb
    · -- `u = v`: the three-vertex path `y₁ u y₂`.
      have h2' : Color.adj G .blue u y₂ := huv ▸ h2
      refine ⟨⟨[y₁, u, y₂], by simp, ?_⟩, ?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
          List.nodup_singleton y₂⟩⟩
        · rw [List.mem_cons, List.mem_singleton]
          exact fun h => h.elim (fun h => hy1 (h ▸ hu)) hyy
        · rw [List.mem_singleton]
          exact fun h => hy2 (h ▸ hu)
      · exact List.isChain_cons_cons.mpr ⟨Color.adj_symm G h1,
          List.isChain_pair.mpr h2'⟩
      · show y₁ ∈ [y₁, u, y₂]
        simp
      · show y₂ ∈ [y₁, u, y₂]
        simp
    · -- `v` occurs after `u`: the segment is `u :: bs' ++ [v]`.
      obtain ⟨bs', ds, rfl, -⟩ := List.eq_append_cons_of_mem hvb
      have hinfix : (u :: bs' ++ [v]) <:+: as ++ u :: (bs' ++ v :: ds) :=
        ⟨as, ds, by simp [List.append_assoc]⟩
      exact mk_pair_path G hnodup hinfix (hchain.infix hinfix) hy1 hy2 hyy
        (Color.adj_symm G h1) h2

/-- Inductive pairing: any set `S` of vertices off `P`, each having a blue
neighbour on `P`, is covered by at most `⌈|S|/2⌉` blue paths (each covering
one or two vertices of `S`). -/
private theorem pair_family
    (P : VertPath (Fin n)) (hP : P.IsMonochromatic G .blue)
    (S : Finset (Fin n))
    (hS : ∀ y ∈ S, y ∉ P.toList ∧ ∃ x ∈ P.toList, Color.adj G .blue x y) :
    ∃ F : Finset (VertPath (Fin n)),
      (∀ p ∈ F, p.IsMonochromatic G .blue) ∧
      (∀ y ∈ S, ∃ p ∈ F, y ∈ p) ∧
      F.card ≤ (S.card + 1) / 2 := by
  classical
  revert hS
  refine Finset.strongInductionOn S (p := fun T =>
    (∀ y ∈ T, y ∉ P.toList ∧ ∃ x ∈ P.toList, Color.adj G .blue x y) →
    ∃ F : Finset (VertPath (Fin n)),
      (∀ p ∈ F, p.IsMonochromatic G .blue) ∧
      (∀ y ∈ T, ∃ p ∈ F, y ∈ p) ∧
      F.card ≤ (T.card + 1) / 2) (fun T ihT hT => ?_)
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, fun p hp => by simp at hp,
      fun y hy => by simp at hy, by simp⟩
  · obtain ⟨y₁, hy₁⟩ := hne
    obtain ⟨hy₁P, x₁, hx₁P, hax₁⟩ := hT y₁ hy₁
    rcases (T.erase y₁).eq_empty_or_nonempty with hE | hne'
    · -- `T = {y₁}`: one singleton path.
      have hT1 : T = {y₁} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨hy₁, fun y hy => ?_⟩
        by_contra h
        have hmem : y ∈ (∅ : Finset (Fin n)) := hE ▸ Finset.mem_erase.mpr ⟨h, hy⟩
        simp at hmem
      refine ⟨{VertPath.singleton y₁}, ?_, ?_, ?_⟩
      · intro p hp
        rw [Finset.mem_singleton] at hp
        rw [hp]
        exact List.isChain_singleton y₁
      · intro y hy
        rw [hT1, Finset.mem_singleton] at hy
        exact ⟨VertPath.singleton y₁, Finset.mem_singleton_self _,
          VertPath.mem_singleton.mpr hy⟩
      · have hcard : T.card = 1 := by rw [hT1, Finset.card_singleton]
        rw [Finset.card_singleton]
        omega
    · -- Pair `y₁` with `y₂` through a segment of `P`, then recurse.
      obtain ⟨y₂, hy₂⟩ := hne'
      have hy₂T : y₂ ∈ T := Finset.mem_of_mem_erase hy₂
      have hyy : y₁ ≠ y₂ := fun h => (Finset.mem_erase.mp hy₂).1 h.symm
      obtain ⟨hy₂P, x₂, hx₂P, hax₂⟩ := hT y₂ hy₂T
      obtain ⟨q, hqmono, hqy1, hqy2⟩ :=
        pair_path G hP P.nodup hy₁P hy₂P hyy hx₁P hx₂P hax₁ hax₂
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨y₁, hy₁⟩
      have hc1 : (T.erase y₁).card = T.card - 1 := Finset.card_erase_of_mem hy₁
      have hc2 : ((T.erase y₁).erase y₂).card = (T.erase y₁).card - 1 :=
        Finset.card_erase_of_mem hy₂
      have hsub : (T.erase y₁).erase y₂ ⊂ T :=
        lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hy₁)
      obtain ⟨F', hF'mono, hF'cov, hF'card⟩ :=
        ihT _ hsub (fun y hy => hT y
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)))
      refine ⟨insert q F', ?_, ?_, ?_⟩
      · intro p hp
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact hqmono
        · exact hF'mono p hp
      · intro y hy
        by_cases hyT : y ∈ (T.erase y₁).erase y₂
        · obtain ⟨p, hp, hpy⟩ := hF'cov y hyT
          exact ⟨p, Finset.mem_insert_of_mem hp, hpy⟩
        · have hy12 : y = y₁ ∨ y = y₂ := by
            by_contra h
            push Not at h
            exact hyT (Finset.mem_erase.mpr
              ⟨h.2, Finset.mem_erase.mpr ⟨h.1, hy⟩⟩)
          rcases hy12 with rfl | rfl
          · exact ⟨q, Finset.mem_insert_self _ _, hqy1⟩
          · exact ⟨q, Finset.mem_insert_self _ _, hqy2⟩
      · calc (insert q F').card ≤ F'.card + 1 := Finset.card_insert_le _ _
          _ ≤ (T.card + 1) / 2 := by omega

end TailPairing

/-- **PVW24 Lemma 3.3 (tail pairing).**  If `P` is a blue path, `Y = [n] ∖ V(P)`
and `Y₀ ⊆ Y` is the set of leftover vertices with no blue edge to `P`, then
`f(n,χ) < 2 + |Y|/2 + |Y₀|/2` (in fact `f ≤ 1 + ⌈|Y ∖ Y₀|/2⌉ + |Y₀|`). -/
theorem tail_pairing_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (P : VertPath (Fin n)) (hP : P.IsMonochromatic G .blue)
    (Y Y₀ : Finset (Fin n))
    (hY : ∀ y, y ∈ Y ↔ y ∉ P.toList)
    (hY0 : ∀ y, y ∈ Y₀ ↔ y ∉ P.toList ∧ ∀ x ∈ P.toList, ¬ Color.adj G .blue x y) :
    HasCoverLt G (2 + (Y.card : ℝ) / 2 + (Y₀.card : ℝ) / 2) := by
  classical
  have hY0sub : Y₀ ⊆ Y := fun y hy => (hY y).mpr ((hY0 y).mp hy).1
  -- Every `y ∈ Y ∖ Y₀` has a blue neighbour on `P`.
  have hS : ∀ y ∈ Y \ Y₀, y ∉ P.toList ∧
      ∃ x ∈ P.toList, Color.adj G .blue x y := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    have hyP : y ∉ P.toList := (hY y).mp hy.1
    refine ⟨hyP, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hy.2 ((hY0 y).mpr ⟨hyP, hcon⟩)
  obtain ⟨F, hFmono, hFcov, hFcard⟩ := pair_family G P hP (Y \ Y₀) hS
  -- The cover: `P`, the pair paths for `Y ∖ Y₀`, and singletons for `Y₀`.
  refine ⟨.blue, insert P (F ∪ Y₀.map VertPath.singletonEmbedding),
    ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · exact hP
    · rw [Finset.mem_union] at hq
      rcases hq with hq | hq
      · exact hFmono q hq
      · obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hq
        exact List.isChain_singleton y
  · intro v
    by_cases hvP : v ∈ P.toList
    · exact ⟨P, Finset.mem_insert_self _ _, hvP⟩
    · have hvY : v ∈ Y := (hY v).mpr hvP
      by_cases hv0 : v ∈ Y₀
      · refine ⟨VertPath.singletonEmbedding v,
          Finset.mem_insert_of_mem (Finset.mem_union_right _
            (Finset.mem_map.mpr ⟨v, hv0, rfl⟩)), ?_⟩
        exact VertPath.mem_singleton.mpr rfl
      · have hv1 : v ∈ Y \ Y₀ := Finset.mem_sdiff.mpr ⟨hvY, hv0⟩
        obtain ⟨q, hq, hvq⟩ := hFcov v hv1
        exact ⟨q, Finset.mem_insert_of_mem (Finset.mem_union_left _ hq), hvq⟩
  · -- `|cover| ≤ 1 + ⌈|Y₁|/2⌉ + |Y₀| < 2 + |Y|/2 + |Y₀|/2`.
    have hY1 : ((Y \ Y₀).card : ℝ) + Y₀.card = Y.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hY0sub
    have hc : (insert P (F ∪ Y₀.map VertPath.singletonEmbedding)).card ≤
        ((Y \ Y₀).card + 1) / 2 + 1 + Y₀.card := by
      calc (insert P (F ∪ Y₀.map VertPath.singletonEmbedding)).card
          ≤ (F ∪ Y₀.map VertPath.singletonEmbedding).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ F.card + Y₀.card + 1 := by
            have h1 := Finset.card_union_le F
              (Y₀.map VertPath.singletonEmbedding)
            rw [Finset.card_map] at h1
            omega
        _ ≤ ((Y \ Y₀).card + 1) / 2 + 1 + Y₀.card := by omega
    have h1 : ((((Y \ Y₀).card + 1) / 2 : ℕ) : ℝ) ≤ (((Y \ Y₀).card : ℝ) + 1) / 2 := by
      have h := Nat.cast_div_le (m := (Y \ Y₀).card + 1) (n := 2) (α := ℝ)
      push_cast at h
      exact h
    have h2 : ((insert P (F ∪ Y₀.map VertPath.singletonEmbedding)).card : ℝ) ≤
        ((((Y \ Y₀).card + 1) / 2 : ℕ) : ℝ) + 1 + Y₀.card := by
      have h3 : ((insert P (F ∪ Y₀.map VertPath.singletonEmbedding)).card : ℝ) ≤
          ((((Y \ Y₀).card + 1) / 2 + 1 + Y₀.card : ℕ) : ℝ) := by
        exact_mod_cast hc
      rwa [Nat.cast_add, Nat.cast_add, Nat.cast_one] at h3
    linarith

/-- **PVW24 Proposition 3.4 (weak bound).**  For all `n`,
`f(n) < √n + 20⁴`. -/
theorem weak_sqrt_bound (n : ℕ) :
    AllCoverLt n (Real.sqrt n + 20 ^ 4) := by
  sorry

/-- **PVW24 Theorem 1.3 — the Erdős–Gyárfás conjecture.**  For all
`n > 20^{40}`, every 2-edge-coloured `K_n` has a vertex cover by at most `√n`
monochromatic paths, all of the same colour. -/
theorem monochromatic_path_cover {n : ℕ} (hn : 20 ^ 40 < n)
    (G : SimpleGraph (Fin n)) :
    ∃ c : Color, ∃ P : Finset (VertPath (Fin n)),
      IsSameColorCover G c P ∧ (P.card : ℝ) ≤ Real.sqrt n := by
  sorry

end JSP415
