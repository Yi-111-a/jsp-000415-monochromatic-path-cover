# JSP-000415 Solver Findings

## Verifier
`scripts/harness.sh` → HARNESS_LOG.md. Score = sorry/admit count (target 0)
then `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.

## Baseline (commit 345675d / 5eb159c)
- lake build: GREEN (with sorry warnings)
- sorries: 12 = Gerencser 2 + BipLemmas 4 + Section3 6
- axioms: [propext, sorryAx, Classical.choice, Quot.sound] → RED

## Active branches
- agent 14cb2d68: Gerencser.lean (gerencser_gyarfas + exists_mono_path_half).
  Strategy: strong induction on card V; remove v; case analysis on colours of
  v-p_last, v-q_last, p_last-q_last. No disjointness needed (overlap harmless).
- agent 9c054b25: bip_ramsey_path (Gyarfas-Lehel Lemma 2.1).

## API notes (learned)
- `decidable_of_iff (a) (h : a ↔ b)`: a = decidable side FIRST.
- `Finset.mem_map` must be `.mp`'d before rcases.
- `List.IsChain` (v4.34, was `List.Chain'`): `isChain_map`,
  `isChain_map_of_isChain`, `IsChain.append`, `.dropLast`, `.infix`.
- `G.neighborFinset` needs `Mathlib.Combinatorics.SimpleGraph.Finite`.
- Narrow imports (not `import Mathlib`) → file builds in ~10s not ~6min.

## Ruled out / dead ends
- `Finset.Covers` does not exist (use explicit ∀v ∃p∈P, v∈p).
- `HasCoverLe.comap` needs Surjective (injective-only version is false).

## Round 2 (commit 931421c, tag checkpoint/2026-09-19-gerencser)
- Gerencser GREEN: gerencser_gyarfas + exists_mono_path_half proved, axioms clean.
- STATEMENT FIX: +[Nonempty V] on both — VertPath requires nonempty lists so
  the empty-graph instance was literally false. Faithful to paper (n>=1).
- sorries: 10 = BipLemmas 4 + Section3 6.
- Active: agent 9c054b25 (bip_ramsey_path), agent 17533615 (overlap_bound+pair).
- API notes from agent: Finset.not_mem_erase MISSING (use mem_erase.mp);
  List.nodup_append is core version; Option.mem_some has reversed eq;
  Finset.Nonempty.strong_induction at Data/Finset/Card.lean:895.
- NOTE: overlap_bound likely needs S.Nonempty (S=empty makes it false) —
  flagged to agent; overlap_bound_pair derives it from hcard (Delta>=1).

## Round 3 (commit af99954)
- overlap_bound + overlap_bound_pair GREEN. overlap_bound gained S.Nonempty
  (S=empty literally false: IH says nothing at level n). Docstring documents it.
- sorries: 8 = BipLemmas 4 + Section3 4 (long_path_structure,
  tail_pairing_bound, weak_sqrt_bound, monochromatic_path_cover).
- Active: agent 9c054b25 (bip_ramsey_path — running long, hard lemma),
  agent 9697a95d (tail_pairing_bound).

## Strategy notes for remaining lemmas

### tail_pairing_bound (Lemma 3.3) — assigned
Pair Y1 = Y\Y0; each pair gets ONE blue path through P's interior
(segment between blue neighbours x1,x2 — List infix of P.toList).
Cover = {P} + pair-paths + Y0-singletons. Count 1+ceil(|Y1|/2)+|Y0| < 2+|Y|/2+|Y0|/2.

### path_cover_two_mul (Lemma 2.2)
Paper proof: take a MAXIMUM path alternating X,Y starting in X; degree
condition (each y has >= (|X|+|Y|)/2 nbrs in X) forces it to cover all Y.
Formalize via Finset.exists_max_image / argmax on path length.

### few_paths_of_min_degree (Lemma 2.3)
Greedy: iteratively extract maximal paths covering remaining Y; each path
uses >= ~2 new X-vertices per Y-vertex... (paper: induction with min-degree
maintained). |X| >= |Y|+2m and deg(y) >= |X|-m.

### refined_path_cover (Lemma 2.4)
Case analysis X1=Y1=empty vs ratio condition; pairs vertices of Y with
distinct full-nbr X-vertices (X0 full-nbr to all Y lets paths be length-2
through Y0...). Paper proof needed from content.txt lines ~230-267.

### long_path_structure (Lemma 3.2)
Uses: exists_mono_path_half (DONE, Gerencser), bip_ramsey_path,
few_paths_of_min_degree, overlap_bound. Build longest red path R in
bipartite H between V(Q) and W; bound |V(Q)∩R| via overlap_bound_pair;
apply bip_ramsey with k=2*ceil(2*Delta*sqrt n), l=n-1-k; longest blue
path P in Kn then has |Y| <= 5*Delta*sqrt n; predecessor-of-blue-nbrs
form red clique -> bound <= 2*Delta*sqrt n blue nbrs per y; then
Lemma 2.3 gives <= sqrt(n/|Y|) red paths covering Y and most of X;
overlap_bound -> derive |Y| < sqrt n + 10*Delta*n^{1/4}.

### weak_sqrt_bound (Prop 3.4)
Induction on n (AllCoverLt). Base n <= C via singletons.
Step: assume not HasCoverLt (√n+C) → ¬HasCoverLe (√n+C+1/2?) careful:
f(n)>√n+C-1 vs HasCoverLt: ¬∃cover card < √n+C means every same-colour
cover has card >= √n+C. Apply long_path_structure C1=C2=C (needs
hind: ∀m<n AllCoverLt (√m+C) = IH itself!). Then Lemma 3.3 + Lemma 2.3
on red graph X,Y as in paper lines 457-472.

### monochromatic_path_cover (Thm 1.3)
n > 20^40 = C^10 with C=20^4. Contradiction from ¬HasCoverLe √n:
Prop 3.4 gives hind; Lemma 3.2 (C1=C,C2=0) → long blue P, |Y| <= (1+α)√n;
Lemma 3.3 rules out small Y0/Y; then bipartite red graph + Lemma 2.4
→ cover size <= ceil(|X|/(|Y|+1)) <= √n. Paper lines 477-515.

## Round 4 (commit 473ff12 + 5bbba9e cleanup)
- tail_pairing_bound GREEN (statement unchanged, axioms clean).
  Proof: mk_pair_path/pair_path/pair_family helpers (~240 lines).
- sorries: 7 = BipLemmas 4 + Section3 3 (long_path_structure,
  weak_sqrt_bound, monochromatic_path_cover).
- bip agent (9c054b25) running ~5h — hard lemma, still writing.
- Launched agent 54d7b8ae on long_path_structure (Lemma 3.2).
- Gotchas logged by agents: `::` binds tighter than `++`;
  List.<+ is scoped (use IsInfix.sublist); Finset.not_mem_empty missing;
  push_neg deprecated; ((x+1)/2:ℝ) parses as real div — cast ℕ first;
  Nat.cast_div_le for (a/b:ℕ):ℝ ≤ a/b; Option.mem_some reversed eq.
- Agent downloaded gl.pdf/gl.txt (Gyarfas-Lehel paper) — cleaned from repo.
