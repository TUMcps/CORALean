# Reachability Analysis of ARMAX Models

L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the 62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.

**Source:** https://arxiv.org/pdf/2309.11944 (arXiv:2309.11944v2, 28 Sep 2023, the authors' version, 8 pages, read in full; text extracted with `pypdf`). Venue and pages from TUM's publication portal (doi:10.1109/CDC49753.2023.10383972); the CDC typeset version was not reachable. CORA cites it in `@linearARX/reach.m` as `[1, Proposition 3]`, `[1, Theorem 2]`, `[1, Theorem 3]`, `[1, Algorithm 1]`, `[1, Algorithm 2]` and Eqs. (9a), (9b), (14a), (16), which match this numbering.  
**Inventory:** confirmed (Definitions 1-5, Propositions 1-3, Theorems 1-3, Lemmas 1-3 and Algorithms 1-2, each with its own counter; equations (1)-(16), of which (12) is the one numbered display stated as a claim outside a result; Tables I-II)

Reachable sets of ARMAX models — the input-output models system identification produces —
without going through a state-space model. Three methods: evaluating the recursion with
exact addition on a dependency-preserving set representation (`Prop. 3`), a reformulation in
which every input occurs once (`Thm. 1`) and an algorithm over it for any representation
(`Alg. 1`), and an algorithm whose cost is linear in the horizon (`Alg. 2`). CORA's
`linearARX/reach` implements all three (`exactAddition`, `tvpGeneral`, `tvpEfficient`).
Everything numbered is formalized, over plain sets and exactly. Two statements fail as
printed: (13) takes the window of `p` outputs to be the Cartesian product of their reachable
sets, which it is not (`Eq. 12`), and `Thm. 3` holds for `k_init = p` only — started later,
`Alg. 2` drops reachable outputs. CORA always starts at `k_init = p`.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Linear discrete-time SS model) x(k+1) = Ax(k) + Bu(k) + w(k), y(k) = Cx(k) + Du(k) + v(k). | [`SsReachEq.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/SsReachEq.lean) — the model as the hypothesis of its runs, with matrices over ℝ | `correct` |
| `Prop. 1` | The reachable outputs of the SS model are Y(k) = CA^k X(0) ⊕ ⊕_{i=1}^k CA^{i-1}(BU(k-i) ⊕ W(k-i)) ⊕ DU(k) ⊕ V(k). | [`SsReachEq.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/SsReachEq.lean) — equality, every input and disturbance set nonempty (so that the signals past k exist) | `correct` |
| `Def. 2` | (Zonotope) Z = {c + Σ λᵢgᵢ \| λᵢ ∈ [-1, 1]} = ⟨c, G⟩. | n/a — restated from Kühn 1998; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Def. 3` | (Symbolic zonotope) A zonotope whose generators carry integer labels l(i), so that two sets sharing a label share the factor λ_{l(i)}. | n/a — restated from Combastel and Zolghadri 2020 [15] | `restated` |
| `Def. 4` | (Addition of labeled matrices) Columns with identical labels are summed, the others concatenated. | n/a — restated from Combastel and Zolghadri 2020 [15, Def. 4.10] | `restated` |
| `Def. 5` | (ARMAX model) y(k) = Σ_{i=1}^p Āᵢ y(k-i) + Σ_{i=0}^p B̄ᵢ ũ(k-i), ũ = (u, w, v) the combined input and disturbance. | [`LinearARX.lean`](../../src/CORALean/ContDynamics/LinearARX/LinearARX.lean) — CORA's `linearARX`; its input is the combined ũ | `correct` |
| `Prop. 2` | (From SS to ARMAX) With a deadbeat observer gain M, (A + MC)^k = 0 for k ≥ p, the SS model is an ARMAX model with Āᵢ = -C(A + MC)^{i-1}M, B̄₀ = D_ũ, B̄ᵢ = C(A + MC)^{i-1}(B_ũ + MD_ũ), D_ũ = [D 0 I], B_ũ = [B I 0]. | [`OfObserver.lean`](../../src/CORALean/ContDynamics/LinearARX/Operations/OfObserver.lean), [`OfObserverStep.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/OfObserverStep.lean) — every SS run satisfies the ARMAX recursion from k = p on, for any combined input matrices B_ũ, D_ũ and (A + MC)^p = 0; the paper cites the proof (Phan et al. 1993), proved here | `correct` |
| `Prop. 3` | (Reachability with dependency-preserving sets) Evaluating (4) with exact addition ⊞ on Ũ(i) = U(i) × W(i) × V(i), Y(k) = ⊞ ĀᵢY(k-i) ⊞ ⊞ B̄ᵢŨ(k-i) (6), gives the reachable set exactly. | [`ReachOutExact.lean`](../../src/CORALean/ContDynamics/LinearARX/Definitions/ReachOutExact.lean), [`ReachOutExactEqSimulate.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/ReachOutExactEqSimulate.lean) — (6) under ⊞, a function of the one shared input signal, is `simulate`; Y(k) is its image over the admissible signals | `correct` |
| `Thm. 1` | (Alternative ARMAX formulation) ỹ(k:k₊) = Ã(k)ỹ_init + Σ_{i=0}^{k₊} B̃ᵢ(k)ũ(k₊-i) (7), k₊ = k + p - 1, with Ã(k) = Ā_ext^k (9a), B̃ᵢ(k) = Σ_{j=0}^{k-1} Ā_ext^j B̄_ext,i-j (9b), Ā_ext, B̄_ext,i as in (10). | [`StackEqTvp.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/StackEqTvp.lean), [`Aext.lean`](../../src/CORALean/ContDynamics/LinearARX/Operations/Aext.lean), [`Bext.lean`](../../src/CORALean/ContDynamics/LinearARX/Operations/Bext.lean), [`Btilde.lean`](../../src/CORALean/ContDynamics/LinearARX/Operations/Btilde.lean) — on every run; Ā_ext is the state matrix of the conversion to `LinearSysDT`, so (11) is `toLinearSysDT_step` | `correct` |
| `Eq. 12` | Ỹ(k:k₊) = Ã(k)ỹ_init ⊕ ⊕_{i=0}^{k₊} B̃ᵢ(k)Ũ(k₊-i), where (13) Ỹ(k:k₊) = Y(k) × Y(k+1) × ⋯ × Y(k₊). | [`ReachWindowExact.lean`](../../src/CORALean/ContDynamics/LinearARX/Definitions/ReachWindowExact.lean), [`ReachWindowExactEq.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/ReachWindowExactEq.lean), [`ReachOutExactEqImageBlock.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/ReachOutExactEqImageBlock.lean), [`ReachWindowExactNeProd.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/ReachWindowExactNeProd.lean) — the equality for the set of reachable windows, each block of which projects onto Y(k+j) exactly; the counterexample to the product **Counterexample:** `LinearARX.reachWindowExact_ne_prod` **Counterexample:** `LinearARX.reachWindowExact_ne_prod` | `fixed` — the reachable windows are not Y(k) × ⋯ × Y(k₊): with y(k) = ũ(k) + ũ(k-1), p = 2, ũ ∈ [-1, 1], (2, -2) is in Y(2) × Y(3) and not a window; (12) holds for the windows themselves, and each Y(k+j) is their projection; see Findings |
| `Lemma 1` | Ã(k + Δk) = Ā_ext^{Δk} Ã(k) (14a), and B̃ᵢ(k + Δk) = Ā_ext^{Δk} B̃_{i-Δk}(k) for i ≥ p + Δk (14b). | [`BtildeAddOfLe.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/BtildeAddOfLe.lean) | `correct` |
| `Lemma 2` | For i < k and Δk ≥ 0, B̃ᵢ(k + Δk) = B̃ᵢ(k) (15). | [`BtildeAddOfLt.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/BtildeAddOfLt.lean) | `correct` |
| `Lemma 3` | B̃ᵢ₊₁(k) = Ā_ext B̃ᵢ(k) + B̄_ext,i+1 - Ā_ext^k B̄_ext,i+1-k (16). | [`BtildeSuccIndex.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/BtildeSuccIndex.lean) — for every integer i | `correct` |
| `Alg. 1` | (Reachability analysis with arbitrary sets) S ← Ã ỹ_init ⊕ ⊕_{i=p}^{k₊} B̃ᵢŨ(k₊-i); per pass Ỹ(k:k₊) ← S ⊕ ⊕_{i=0}^{p-1} B̃ᵢŨ(k₊-i), k ← k + p, B̃_p, …, B̃_{2p-1} refreshed while k < 3p, S ← Ā_ext^p S ⊕ ⊕_{i=p}^{2p-1} B̃ᵢŨ(k₊-i). | [`Alg1.lean`](../../src/CORALean/ContDynamics/LinearARX/Operations/Alg1.lean), [`Alg1State.lean`](../../src/CORALean/ContDynamics/LinearARX/Operations/Alg1State.lean) — over plain sets, ⊕ the pointwise sum; lines 4 and 11 compute by (16), which gives (9b)'s matrices (`Lemma 3`), so both read (9b) | `correct` |
| `Thm. 2` | (Reachability with arbitrary sets) For k_init ≥ p, Alg. 1 returns the reachable sets at k_init, k_init + 1, …, p + k_h. | [`Alg1EqReachWindowExact.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/Alg1EqReachWindowExact.lean) — pass m returns exactly the reachable windows at k_init + mp (p > 0, every Ũ(i) nonempty), and so each Y(k) by `Eq. 12`'s projection | `correct` |
| `Alg. 2` | (Efficient reachability analysis) For Ũ(i) = Ũ_c + ũ_v(i): S_c, T_c1 and s_v initialised from (9b)/(16); per pass Ỹ(k:k₊) ← (s_v + Σ_{i=0}^{p-1} B̃ᵢũ_v(k₊-i)) ⊕ S_c ⊕ T_c1, k ← k + p, B̃_p, …, B̃_{2p-1} refreshed while k < 3p, T_c2 ← ⊕_{i=k-p}^{k₊-p} B̃ᵢŨ_c in the first pass, S_c ← S_c ⊕ T_c2, T_c1, T_c2, s_v moved on by Ā_ext^p. | [`Alg2.lean`](../../src/CORALean/ContDynamics/LinearARX/Operations/Alg2.lean), [`Alg2State.lean`](../../src/CORALean/ContDynamics/LinearARX/Operations/Alg2State.lean), [`Alg2NeReachWindowExact.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/Alg2NeReachWindowExact.lean) — as printed, over plain sets | `underspecified` — line 18 needs B̃ᵢ(k_init + p) at i = k_init, …, k_init + p - 1, and lines 14-15 refresh only i < 2p: correct for k_init = p, stale for k_init > p; see Findings |
| `Thm. 3` | (Efficient reachability analysis) If Ũ(i) = Ũ_c + ũ_v(i), Alg. 2 returns the reachable sets at k_init, …, p + k_h for k_init ≥ p. | [`Alg2EqReachWindowExact.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/Alg2EqReachWindowExact.lean), [`Alg2NeReachWindowExact.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/Alg2NeReachWindowExact.lean) — exactly the reachable windows at k_init = p (p > 0, Ũ_c nonempty); the counterexample at k_init = p + 1 **Counterexample:** `LinearARX.alg2_ne_reachWindowExact` **Counterexample:** `LinearARX.alg2_ne_reachWindowExact` | `fixed` — false for k_init > p: y(k) = y(k-1) + ũ(k), p = 1, ũ ∈ [-1, 1], k_init = 2 returns [-2, 2] at k = 3, where y(3) = 3 is reachable; true at k_init = p; see Findings |
| `Table I` | Proposition 3 and Theorem 2 take O(f_k²) time in the horizon factor, Theorem 3 O(f_k); all three O(f_n³) in the dimension factor and O(p³) in the order (Sec. IV). | n/a — computational complexity of the symbolic-zonotope implementations, a subject CORALean does not cover | `not-covered` |
| `Sec. V` | The pedestrian model's ARMAX reachable sets against SS and ARMAX without dependencies (Fig. 1), and computation times (Table II). | n/a — experiments | `not-a-claim` |

## Findings

**`Eq. 12` — the window is not the product of its outputs.** (13) defines
Ỹ(k:k₊) = Y(k) × ⋯ × Y(k₊) and (12) equates it with Ã(k)ỹ_init ⊕ ⊕ B̃ᵢ(k)Ũ(k₊-i), the set of
windows the runs reach. One input enters several outputs of a window, so the two differ: for
y(k) = ũ(k) + ũ(k-1), p = 2, ũ ∈ [-1, 1] and ỹ_init = 0, y(2) = 2 and y(3) = -2 are each
reachable, but y(2) = 2 forces ũ(2) = 1, so y(3) ≥ 0. (12) holds for the set of windows, and
what `Thm. 2` and `Thm. 3` then use — that block j of it is Y(k+j) — holds exactly: CORA's
`reach` projects each block out (`project`), which is right.
[`ReachWindowExactNeProd.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/ReachWindowExactNeProd.lean),
[`ReachOutExactEqImageBlock.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/ReachOutExactEqImageBlock.lean)

**`Thm. 3`, `Alg. 2` — a later start reads stale parameters.** In the first pass line 18 sets
T_c2 = ⊕_{i=k_init}^{k_init+p-1} B̃ᵢ Ũ_c, and the proof needs B̃ᵢ(k_init + p) there. The stored
B̃ᵢ are B̃ᵢ(k_init) from line 4, except i < 2p, which lines 14-15 recompute. For k_init = p every
index is below 2p and the theorem holds; for k_init > p the indices from 2p on are stale, and
B̃ᵢ(k_init) ≠ B̃ᵢ(k_init + p) there (the latter has the extra term Ā_ext^{k_init} B̄_ext,0 at
i = k_init). With y(k) = y(k-1) + ũ(k), p = 1, Ũ_c = [-1, 1], ũ_v = 0, ỹ_init = 0 and
k_init = 2, the second pass returns [-2, 2] for y(3) = ũ(1) + ũ(2) + ũ(3), whose reachable set
is [-3, 3]: the term B̃₂(3)Ũ_c = Ũ_c is read as B̃₂(2)Ũ_c = {0}. The algorithm then
under-approximates. Computing line 18's parameters at k (by (9b)) repairs it; CORA's
`aux_typEfficient` starts at k = p and initialises T_c2 at k = 2p, so it is not affected.
`Thm. 2`'s `Alg. 1` reads only i < 2p and is correct for every k_init ≥ p.
[`Alg2NeReachWindowExact.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/Alg2NeReachWindowExact.lean),
[`Alg2EqReachWindowExact.lean`](../../src/CORALean/ContDynamics/LinearARX/Theorems/Alg2EqReachWindowExact.lean)
