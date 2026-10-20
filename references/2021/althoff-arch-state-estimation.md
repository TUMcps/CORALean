# Guaranteed State Estimation in CORA 2021

M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21), EPiC Series in Computing, vol. 80, pp. 161-175, 2021.

**Source:** https://easychair.org/publications/open/hMPK (the EPiC PDF, 15 pages, pp. 161-175, read in full; text extracted with `pypdf`).  
**Inventory:** confirmed (the numbered items are Algorithm 1, equations (1)-(7), Figures 1-3 and Tables 1-6; Sec. 2 also defines the estimation and reachability sets in prose, Sec. 3 the cost functions, Sec. 4 the tank benchmark)

The tool paper of CORA's set-based observers (`observe` on `linearSysDT` and `nonlinearSysDT`).
It surveys three kinds — strip-based, set-propagation and interval observers — for a linear
discrete-time system, lists the eighteen implemented in CORA (Table 1) and compares them on a
tank benchmark. Its own mathematics is short: the three observer schemes, eqs. (2)-(4), eq. (6)
and Alg. 1, each restated from a cited paper with the paper's own guarantee. All three are
formalized at every gain, as CORA runs them: the strip-based observer was already
(`observeStripBased`, from [Le et al. 2013](../2013/le-automatica-zonotopic-estimation.md)), the
set-propagation observer of eq. (6) is new here (`observePropagation`, CORA's `FRad-C`, `PRad-E`,
`Nom-G`), and Alg. 1 is CORA's interval observer (`observeInterval`, `Hinf-G`).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 1` | Zonotopes take linear maps in cubic and Minkowski sums in linear time, and constrained zonotopes intersect strips exactly ([5, Tab. 1]). | n/a — restated from Althoff, Frehse and Girard's 2021 survey of set propagation, which has no page here | `restated` |
| `Eq. 1` | The system `x_{k+1} = A x_k + B u_k + w_k`, `y_k = C x_k + v_k`, `w_k ∈ W`, `v_k ∈ V`. | n/a — the model (`LinearSysDT`, its input in state coordinates, and an output matrix) | `not-a-claim` |
| `Sec. 2` | The estimation problem: `S_k`, the states reachable from `S_{k-1}` and consistent with the measurement `y_k`; the reachable set `R_k` without the consistency check, a special case. | n/a — the problem statement | `not-a-claim` |
| `Eq. 2` | The states possible from the `j`-th output form the strip `Ŝ_j = {x \| \|C_j x - y_{k,j}\| ≤ σ_j}`, `[-σ, σ] = box(V)` ([1, Property 2]). | n/a — restated from Alamo, Bravo and Camacho 2005, which has no page here; the strip-based observer below takes the strip condition as its hypothesis | `restated` |
| `Eq. 3` | "The entire measurement set `Ŝ` is computed by over-approximatively intersecting all strips: `Ŝ ⊆ Ŝ_1 ∩ … ∩ Ŝ_m`." | [`IntersectStripOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntersectStripOuter.lean), [`IntersectStripSeqOuter.lean`](../../src/CORALean/ContSet/ContSet/Theorems/IntersectStripSeqOuter.lean) — as CORA does it, the strips met with the predicted set, all at once or one by one, over-approximated: the result contains the exact intersection, `⊇` | `underspecified` — the inclusion is printed reversed; an over-approximation is `Ŝ ⊇ ∩ Ŝ_j` |
| `Eq. 4` | Correction: `S_k ⊇ S_p ∩ Ŝ`, after the prediction `S_p = A S_{k-1} ⊕ B u_{k-1} ⊕ W`; the strip-based observer then encloses the true state. | [`ObserveStep.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveStep.lean), [`ObserveStepOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ObserveStepOuter.lean), [`ObserveStripBased.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveStripBased.lean), [`ObserveStripBasedOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ObserveStripBasedOuter.lean) — one step and the observer over time, at every gain and order: every run from `S_0` whose outputs meet the strips stays in the sets | `correct` |
| `Alg. 1` | The interval observer of [58, Alg. 1]: `x̂_0 ← center(X_0)`, `D_0 ← W ⊕ (-L)V`, `S_{x,0} ← X_0`, `S_{wv,0} ← 0`; per step `[e̲_k, e̅_k] = box(S_{x,k}) ⊕ S_{wv,k}`, `[x̲_k, x̅_k] = x̂_k + [e̲_k, e̅_k]`, then the Luenberger update of `x̂`, `S_{x,k+1} = (A - LC) S_{x,k}`, `S_{wv,k+1} = S_{wv,k} ⊕ box(D_k)`, `D_{k+1} = (A - LC) D_k`. | [`ObserveIntervalState.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Definitions/ObserveIntervalState.lean), [`ObserveIntervalState.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveIntervalState.lean), [`ObserveInterval.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveInterval.lean), [`ObserveIntervalOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObserveIntervalOuter.lean), [`ObserveIntervalCora.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Counterexamples/Real/ObserveIntervalCora.lean) — the listing line by line, as CORA's `priv_observe_interval` runs it; the box holds the true state at every step when `S_{x,0}` holds the initial error `x_0 - x̂_0`, and as printed it need not: `X_0 = {1}` gives the box `{2}` | `underspecified` — line 2 seeds the error set with `X_0`; it must be `X_0 - x̂_0` |
| `Sec. 2.3` | No interval observer performs better than Alg. 1 ([58]). | n/a — restated from Tang, Wang, Wang, Raïssi and Shen 2019, which has no page here | `restated` |
| `Eq. 5` | The Luenberger update `x̂_{k+1} = A x̂_k + B u_k + w_k + L(y_k - C x̂_k - v_k)`, which reproduces the true solution. | n/a — the update eq. (6) evaluates on sets; its consequence is eq. (6) | `not-a-claim` |
| `Eq. 6` | `S_{k+1} = (A - LC) S_k ⊕ B u_k ⊕ L y_k ⊕ (-L)V ⊕ W` "returns a guaranteed bound if `x̂_0 ∈ S_0` and `V` as well as `W` contain the origin", for any, also time-varying, `L` ([22, Sec. 4.1]). | [`ObservePropagation.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObservePropagation.lean), [`ObservePropagationOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObservePropagationOuter.lean) — the recursion with a gain chosen from the current set at every step, and a reduction, as CORA runs `FRad-C`, `PRad-E` and `Nom-G`; every run with `x_0 ∈ S_0` stays in the sets | `underspecified` — the condition is on the true initial state, `x_0 ∈ S_0`, not the estimate's; the origin is not needed |
| `Sec. 2.4` | Strip-based estimates are delayed by the measurement; a parametrization of the strip-based and the propagation-based observer gives the same result ([62, Sec. 5]). | n/a — restated; tracked as `Thm. 7` on [Wang, Puig and Cembrano 2018](../2018/wang-automatica-descriptor-observer.md) | `restated` |
| `Sec. 3` | The cost functions the zonotope observers minimize: the volume ([1, Sec. 6.2]), the `F_P`-radius `‖G‖_{F,P} = √trace(Gᵀ P G)` ([22, Def. 2]), the P-radius `max_{z ∈ Z} ‖z - c‖²_P` ([37, Sec. 2]). | n/a — restated; tracked as `Sec. 2` on [Le et al. 2013](../2013/le-automatica-zonotopic-estimation.md), the P-radius; the volume is Alamo et al.'s 2005 (`Sec. 6.1` on [Alamo et al. 2005](../2005/alamo-automatica-guaranteed-estimation.md)) and the `F_P`-radius Combastel's 2015 (`Def. 2` on [Combastel 2015](../2015/combastel-automatica-zonotopes-kalman.md)) | `restated` |
| `Table 1` | The eighteen observers implemented in CORA, their set representation, real-time readiness, dynamics and source. | n/a — a list of methods | `not-a-claim` |
| `Fig. 1` | A listing running `FRad-C` on the example of [1, Sec. 7.1], and the state bounds it plots. | n/a — a worked example | `not-a-claim` |
| `Sec. 4` | The tank benchmark: Torricelli's law per tank, its explicit-Euler discretization, the parameters, Table 2's inflow and measurement indices. | n/a — a benchmark model; the discretization for `i > 1` is printed `x_{k+1,i} = x_{k+1,i} + …`, for `x_{k,i}` on the right | `not-a-claim` |
| `Eq. 7` | The relative root-mean-square radius `υ_{i,l}` of observer `l` in dimension `i`. | n/a — an experimental metric | `not-a-claim` |
| `Table 2` | The tanks with inflow and with a measured level. | n/a — experimental setup | `not-a-claim` |
| `Table 3` | Relative rms radii and times, linearized 6-tank system. | n/a — experiments | `not-a-claim` |
| `Table 4` | Relative rms radii and times, nonlinear 6-tank system. | n/a — experiments | `not-a-claim` |
| `Table 5` | Scalability, linear systems up to 30 tanks. | n/a — experiments | `not-a-claim` |
| `Table 6` | Scalability, nonlinear systems up to 30 tanks. | n/a — experiments | `not-a-claim` |

## Findings

**`Eq. 3`'s inclusion is reversed.** The sentence says the measurement set is computed "by
over-approximatively intersecting all strips", and the formula reads `Ŝ ⊆ Ŝ_1 ∩ … ∩ Ŝ_m`. Taken
as printed it admits `Ŝ = ∅`, and then eq. (4) admits `S_k = ∅`, which holds no state: the
guarantee needs `Ŝ ⊇ Ŝ_1 ∩ … ∩ Ŝ_m`. CORA never forms `Ŝ` on its own; it meets the predicted set
with the strips and over-approximates that (`intersectStrip_outer`, `intersectStripSeq_outer`),
which is eqs. (3)-(4) in the right direction.

**`Alg. 1` seeds the error set with the initial set.** The estimate starts at the center,
`x̂_0 ← center(X_0)`, and the box is `x̂_k + box(S_{x,k}) ⊕ S_{wv,k}`, so `S_{x,k}` bounds the error
`x_k - x̂_k`, which starts at `x_0 - x̂_0 ∈ X_0 - x̂_0`. Line 2 sets `S_{x,0} ← X_0` instead: at
`k = 0` the box is `x̂_0 + box(X_0)`, the initial box moved by its own center, and for
`X_0 = {1}` it is `{2}`, which misses `x_0 = 1`. Only an `X_0` centered at the origin is unaffected.
CORA's `priv_observe_interval` (`Hinf-G`) does the same, and is recorded in
[`linearSysDT` `executeObserver`](../coverage/contDynamics/linearSysDT.md) with the counterexample
`LinearSysDT.observeInterval_cora_counterexample`; `observeInterval_outer` proves the enclosure
under `x_0 - x̂_0 ∈ S_{x,0}`.

**`Eq. 6`'s condition is on the wrong state.** The text derives the guarantee from the true
solution `x_{k+1} = A x_k + B u_k + w_k` being a point of the set-based update, which needs the
true initial state in `S_0`; it states the condition as `x̂_0 ∈ S_0`, the estimate, which says
nothing about `x_0` (`S_0 = {0}`, `x̂_0 = 0`, `x_0 = 1`, `A = 1`, `L = 0`, `V = W = {0}` keeps
`S_k = {0}` while `x_k = 1`). The further condition that `V` and `W` contain the origin is not
used: the true state is `(A - LC) x_k + B u_k + L y_k + (-L) v_k + w_k`, a point of each summand
whatever `V` and `W` are. `observePropagation_outer` assumes `x_0 ∈ S_0` and nothing on `V`, `W`.
