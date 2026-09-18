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
