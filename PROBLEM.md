# JSP-000415 — Can every edge-colored complete graph have its vertices covered by few paths whose edges all share one color?

- **id:** JSP-000415
- **title:** Can every edge-colored complete graph have its vertices covered by few paths whose edges all share one color?
- **area:** Graph theory / Ramsey theory
- **status:** Solved
- **Lean:** No
- **Eligible / Claim:** No / Unavailable

## Statement (exact, from the resolving paper)

The catalog one-liner is loose. The precise statement is **Theorem 1.3** of
[PVW24] (Pokrovskiy–Versteegen–Williams, arXiv:2409.03623v2):

> **Theorem 1.3.** For all $n > 20^{40}$, the vertex set of every
> $2$-edge-coloured complete graph on $n$ vertices can be covered by $\sqrt{n}$
> monochromatic paths, all of the same colour.

Conventions (Section 2 of the paper):

- The colouring is a **red–blue** colouring of $E(K_n)$ (exactly two colours).
- A *path* is a sequence of distinct vertices with consecutive terms adjacent;
  paths of **length 0** (a single vertex) are allowed; paths in a cover need
  **not** be disjoint.
- "$\sqrt{n}$ paths" means a family $\mathcal{P}$ with
  $|\mathcal{P}| \le \sqrt{n}$ (real comparison; since $|\mathcal{P}|\in\mathbb{N}$
  this is $|\mathcal{P}| \le \lfloor\sqrt n\rfloor$).
- "All of the same colour": every path in $\mathcal{P}$ is red, **or** every path
  in $\mathcal{P}$ is blue — the cover is monochromatic in one colour, not merely
  pathwise monochromatic.
- Only the regime $n > 20^{40}$ is claimed (the paper writes the threshold as
  $C^{10}$ with $C = 20^{4}$).

This resolves the 1995 Erdős–Gyárfás conjecture for large $n$: [ErGy95] proved
the same with $2\sqrt n$ in place of $\sqrt n$, and the partition of $V(K_n)$
into $A \sqcup B$, $|B|=\lfloor\sqrt n\rfloor-1$, all edges inside $A$ blue and
all other edges red, shows $\lfloor\sqrt n\rfloor$ same-colour paths are
necessary, so the bound is tight.

## Dependency chain inside the paper

| Result | Statement | Used by |
|---|---|---|
| Thm 1.1 (Gerencsér–Gyárfás 1967) | every 2-coloured $K_n$ is covered by two monochromatic paths (colours may differ) | Lem 3.2 |
| Lem 2.1 (Gyárfás–Lehel 1973) | for distinct $k,\ell$, every red–blue $K_{\lceil(k+\ell)/2\rceil,\lceil(k+\ell)/2\rceil}$ has a red path on $k+1$ or a blue path on $\ell+1$ vertices | Lem 3.2 |
| Lem 2.2 | bipartite $X\cup Y$, every $y\in Y$ has degree $\ge(|X|+|Y|)/2$ ⇒ path covering $2|Y|$ vertices | Lem 2.3 |
| Lem 2.3 | $|X|\ge|Y|+2m$, $Y$-degrees $\ge|X|-m$ ⇒ $\le\lfloor|X|/|Y|\rfloor$ paths covering $Y$ and all but $|Y|+2m$ of $X$ | Lem 3.2, Prop 3.4 |
| Lem 2.4 | bipartite with $X_0,X_1,Y_0,Y_1$ degree structure ⇒ $\lceil|X|/(|Y|+1)\rceil$ paths cover everything | Thm 1.3 |
| Lem 3.1 | overlap lemma: large set covered by few red **and** few blue paths + induction hypothesis ⇒ bound | Lem 3.2 |
| Lem 3.2 | if $f(n,\chi)>\sqrt n+C_2$: long monochromatic path $P$; every outside vertex has few same-colour neighbours on $P$ | Prop 3.4, Thm 1.3 |
| Lem 3.3 | $f(n,\chi)\le 1+\lceil|Y\setminus Y_0|/2\rceil+|Y_0|<2+|Y|/2+|Y_0|/2$ | Prop 3.4, Thm 1.3 |
| Prop 3.4 | $f(n)<\sqrt n+20^{4}$ for all $n$ (strong induction) | Thm 1.3 |
| **Thm 1.3** | $f(n)\le\sqrt n$ for $n>20^{40}$ | headline |

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000415
- Awards home: https://github.com/TheJustinSunPrize/awards

## Primary papers

- [ErGy95] P. Erdős, A. Gyárfás. Vertex covering with monochromatic paths — Math. Pannon. 6 (1995), 7–10.
- [GeGy67] L. Gerencsér, A. Gyárfás. On Ramsey-type problems — Ann. Univ. Sci. Budapest (1967), 167–170.
- [GyLe73] A. Gyárfás, J. Lehel. A Ramsey-type problem in directed and bipartite graphs — Period. Math. Hungar. 3 (1973), 299–304.
- [PVW24] A. Pokrovskiy, L. Versteegen, E. Williams. A proof of a conjecture of Erdős and Gyárfás on monochromatic path covers — arXiv:2409.03623 (v2, 2025). **Main formalization source.**

## Success criteria

- `lake build` succeeds in `lean/`
- `sorry` and `admit` counts are zero
- `#print axioms` on the headline theorem shows only `[propext, Classical.choice, Quot.sound]`
- final commit SHA and build evidence recorded
