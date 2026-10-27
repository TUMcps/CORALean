# A distributed set-membership approach based on zonotopes for interconnected systems

```bibtex
@inproceedings{wang2018distributed,
  author = {Wang, Y. and Alamo, T. and Puig, V. and Cembrano, G.},
  title = {A distributed set-membership approach based on zonotopes for interconnected systems},
  booktitle = {2018 IEEE Conference on Decision and Control (CDC)},
  year = {2018}
}
```

**Source:** http://www.iri.upc.edu/files/scidoc/2162-A-Distributed-Set-membership-Approach-based-on-Zonotopes-for-Interconnected-Systems.pdf (the authors' copy on IRI's repository, 6 pages numbered 668-673, read in full; text extracted with `pypdf`, the displays of Prop. 1 and Thm. 1 checked against the page images). The IEEE Xplore version (doi:10.1109/CDC.2018.8619038) was not reachable.  
**Inventory:** confirmed (against the paper: Definitions 1-2, Assumptions 1-2, Lemma 1, Propositions 1-2 and Theorem 1, each with its own counter; Equations 1-23, of which the rows below are the displays outside a numbered result, the others being parts of the results they belong to; the algorithm of Sec. IV-C has no number, Sec. V is the example)

The estimator behind CORA's `PRad-C` gain (`priv_observe_gain_PRadC`, whose LMI is the one "also
presented in [1] on p. 671", Eq. 14b with `Γ`, `Υ` diagonal and the objective `-tr(P)` of Eq. 23). It covers the state-bounding zonotope of an agent in an interconnected system, built from its neighbours'
zonotopes with one coefficient vector per neighbour (Prop. 1), its centralized form (Prop. 2) and
the LMI that makes its P-radius contract (Thm. 1), the loop of Sec. IV-C. Every gain encloses the
state; the LMI only says how well. The theorems are proved at an arbitrary correction matrix and
an arbitrary outer order reduction. The contraction is proved, as the paper states it, for the
centralized zonotope of Prop. 2; the distributed zonotopes of Prop. 1 are not covered by it (see
Findings).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | A zonotope `Z = ⟨c, H⟩ = {c + Hz, ‖z‖_∞ ≤ 1}`, `c` its center and `H` its segment matrix, `Z = c ⊕ H Bʳ` (Eq. 1). | n/a — restated; tracked as `Def. 1` on [Reachability of Uncertain Linear Systems Using Zonotopes](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 2` | `⟨c₁, H₁⟩ ⊕ ⟨c₂, H₂⟩ = ⟨c₁ + c₂, [H₁ H₂]⟩` (2a), `L⟨c, H⟩ = ⟨Lc, LH⟩` (2b). | n/a — restated; tracked as `Sec. 2` on [Reachability of Uncertain Linear Systems Using Zonotopes](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Def. 2` | The P-radius of `Z = ⟨p, H⟩` for `P ≻ 0` is `V(Z) = max_{‖z‖_∞ ≤ 1} ‖Hz‖²_P = max zᵀHᵀPHz` (Eq. 3). | n/a — restated; tracked as `Sec. 2` on [Zonotopic guaranteed state estimation for uncertain systems](../2013/le-automatica-zonotopic-estimation.md) | `restated` |
| `Lemma 1` | (From Alamo, Bravo, Redondo and Camacho 2008) For `Z = c ⊕ H Bʳ` with `rank H = n ≤ r` and the SVD `H = UΣVᵀ`, `Z ⊆ Z_p = c ⊕ UD Bⁿ` with `D` diagonal, `D_ii = ‖σ_i V_i‖₁`. | n/a — restated from T. Alamo, J. M. Bravo, M. J. Redondo and E. F. Camacho, "A set-membership state estimation algorithm based on DC programming" (Automatica, 44(1):216-224, 2008), which has no page here; the loop below takes any outer reduction | `restated` |
| `Eq. 4` | The interconnected system: `l` agents `x_i(k+1) = Σ_{j ∈ N_i} A_ij x_j(k) + B_i u_i(k) + w_i(k)`, `y_i(k) = C_i x_i(k) + v_i(k)`, `N_i` the agents related to `i`, `i` among them. | n/a — the paper's setting | `not-a-claim` |
| `Assumption 1` | `w_i(k) ∈ ⟨0, D_{w_i}⟩`, `v_i(k) ∈ ⟨0, D_{v_i}⟩` for all `k`, `D_{w_i} ∈ ℝ^{m_{w_i} × m_{w_i}}`, `D_{v_i} ∈ ℝ^{m_{v_i} × m_{v_i}}`. | n/a — the paper's setting; `w_i` enters the `n_i`-dimensional state, so `m_{w_i} = n_i` and `D_{w_i}` is square, and `v_i` enters the output, `m_{v_i} = p_i`: the formalization takes `D_{w_i} ∈ ℝ^{n_i × n_w}`, `D_{v_i} ∈ ℝ^{p_i × n_v}` for any generator counts | `not-a-claim` |
| `Assumption 2` | `x_i(0) ∈ X_i(0) = ⟨c_i(0), H_i(0)⟩`. | n/a — the paper's setting | `not-a-claim` |
| `Prop. 1` | (Distributed state-bounding zonotope) If `x_i(k-1) ∈ X_i(k-1) = ⟨c_i(k-1), H_i(k-1)⟩` for `i = 1, …, l`, then for every correction matrix `Λ_i ∈ ℝ^{n_i × p_i}`, `x_i(k) ∈ X_i(k) = ⟨c_i(k), H_i(k)⟩` (Eq. 6), `c_i(k) = (I - Λ_iC_i)(Σ_{j ∈ N_i} A_ij c_j(k-1) + B_i u_i(k-1)) + Λ_i y_i(k)`, `H_i(k) = [(I - Λ_iC_i) cat_{j ∈ N_i} {A_ij H_j(k-1)}  (I - Λ_iC_i) D_{w_i}  Λ_i D_{v_i}]` (Eq. 7). | [`CorrectedStepDistributed.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/CorrectedStepDistributed.lean), [`CorrectedStepDistributedOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/CorrectedStepDistributedOuter.lean) — the neighbours enumerated as `Fin q`, each with its own coefficient vector, the blocks `A_ij H_j` laid side by side by `finSigmaFinEquiv`. **As printed:** the printed `D_{w_i} ∈ ℝ^{m_{w_i} × m_{w_i}}` is the case `m_{w_i} = n_i` of the `n_i × n_w` matrix the theorem takes, since `w_i` is added to the `n_i`-dimensional state, so the printed statement is an instance of the proved one | `correct` |
| `Eq. 12` | The agents stacked: `x(k+1) = A x(k) + B u(k) + w(k)`, `y(k) = C x(k) + v(k)`, `A = (A_ij)`, `B`, `C`, `D_w`, `D_v` block diagonal. | n/a — a change of notation, the agents stacked; the loop and `Prop. 2` below are stated on it | `not-a-claim` |
| `Prop. 2` | (Centralized state-bounding zonotope) If `x(k-1) ∈ X(k-1) = ⟨c(k-1), H(k-1)⟩`, then for every `Λ ∈ ℝ^{n × p}`, `x(k) ∈ X(k) = ⟨c(k), H(k)⟩` (Eq. 13), `c(k) = (I - ΛC)(A c(k-1) + B u(k-1)) + Λ y(k)`, `H(k) = [(I - ΛC) A H(k-1)  (I - ΛC) D_w  Λ D_v]`; proof omitted as similar to `Prop. 1`. | [`CorrectedStep.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/CorrectedStep.lean), [`CorrectedStepOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/CorrectedStepOuter.lean) — the case `T = I`, `N = 0` of `Zonotope.intersectDescriptor`, without that case's block of `n_v` zero generators | `correct` |
| `Thm. 1` | Given `X(k) = ⟨c(k), H(k)⟩` of Eq. 13, `γ ∈ (0, 1)` and `ε > 0`: if there are `P ∈ S^n_{≻0}`, `Y ∈ ℝ^{n × p}` and diagonal `Γ ∈ S^{m_w}_{≽0}`, `Υ ∈ S^{m_v}_{≽0}` with `tr(Γ) + tr(Υ) < ε` (Eq. 14a) and `[γP ⋆ ⋆ ⋆; (P - YC)A  P ⋆ ⋆; 0  D_wᵀ(P - YC)ᵀ  Γ ⋆; 0  D_vᵀYᵀ  0  Υ] ≻ 0` (Eq. 14b), then `V(X(k)) ≤ γ V(X(k-1)) + ε` for all `k ∈ ℕ₊` (Eq. 15), "which leads to `V(X(∞)) ≤ ε / (1 - γ)` when `k → +∞`". | [`CorrectedStepPRadiusLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/CorrectedStepPRadiusLe.lean), [`RadiusUltimateBoundOfContraction.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/RadiusUltimateBoundOfContraction.lean) — Eq. 15 at `Λ = P⁻¹Y` (the gain the paper takes from `Y = PΛ` after Eq. 23) for `γ ≥ 0`, Eq. 14b in the paper's block order, the proof's Schur complement read at `(θ, -d, ϖ, σ)`; and the clause `k → ∞` for the limit where the radii converge and `V(X(k)) ≤ γᵏ V(X(0)) + ε / (1 - γ)`, eventually `≤ ε / (1 - γ) + δ`, where they need not | `underspecified` — `V(X(∞))` presupposes that the radii converge; the bound is proved for the limit when there is one and for the limit superior; see Findings |
| `Eq. 21` | The block-diagonal structure `P = diag(P_1, …, P_l)`, `Y = diag(Y_1, …, Y_l)` to obtain a group of gains `Λ_i`. | n/a — the choice among feasible gains; every `Λ_i` is covered by `Prop. 1` and `Prop. 2` | `not-a-claim` |
| `Eq. 22` | `V(X(∞)) ≤ ε / (1 - γ)` gives `(x(∞) - c(∞))ᵀP(x(∞) - c(∞)) ≤ ε / (1 - γ)`, "which is an ellipsoid"; to shrink it, maximize a norm of `P`, e.g. `tr(P)`. | n/a — the ellipsoid reading of `Eq. 15`, which motivates the objective of `Eq. 23`; every point of the zonotope lies in it by the maximum of `Def. 2` | `not-a-claim` |
| `Eq. 23` | The offline gains from `maximize tr(P)` subject to Eq. 14, `Λ = P⁻¹Y`. | n/a — the choice among feasible gains; CORA's `priv_observe_gain_PRadC` solves it by a bisection on `γ` with the objective `-tr(P)` | `not-a-claim` |
| `Sec. IV-C` | The distributed set-membership state estimation algorithm. Offline: solve `Eq. 23` with the structure of `Eq. 21` for `Λ_i`. Online, for every agent: send `⟨c_i(k-1), H_i(k-1)⟩` to the neighbours, receive theirs, measure `y_i(k)`, update `⟨c_i(k), H_i(k)⟩` by `Eq. 6` with `Λ_i`, and reduce the order by the over-bounding parallelotope of `Lemma 1`. | [`DistributedObserveSound.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/DistributedObserveSound.lean) — `x_i(k) ∈ X_i(k)` at every `k` for any correction matrices and any reduction that encloses its argument | `correct` |
| `Sec. V` | Two interconnected subsystems (`l = 2`, `n = 3 + 2`): the optimal gains `Λ_1`, `Λ_2` and the centralized `Λ_c` at `γ = 0.8`, state bounds, `tr(P)`, MSE and bound measure for both approaches (Figs. 1-2, Table I). | n/a — an experiment | `not-a-claim` |

## Findings

**`Thm. 1` — `V(X(∞))`.** The theorem ends with `V(X(∞)) ≤ ε / (1 - γ)` "when `k → +∞`".
`V(X(∞))` is the radius at infinity, which exists only if the radii converge, and `Eq. 15`
does not make them. The proof stops at `Eq. 15`, and the clause is stated without one.
[`RadiusUltimateBoundOfContraction.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/RadiusUltimateBoundOfContraction.lean)
proves the bound for the limit when it exists, `L ≤ γL + ε`, and for every `k`,
`V(X(k)) ≤ γᵏ V(X(0)) + ε / (1 - γ)`, which holds without a limit; the same step as
[Wang, Puig and Cembrano 2018](../2018/wang-automatica-descriptor-observer.md)'s `Prop. 1`.

**`Thm. 1` — the proof's notation.** The proof writes `‖H(k-1)θ‖²_W` and `P` for the same weight
(Eqs. 16-17), and `Y = RΛ` where `Y = PΛ` is meant (Eq. 18, `R` being the stacked matrix of the
same display). Neither changes the argument: the formalization follows it with `P` and `Y = PΛ`.
The disturbance and noise sizes, `D_{w_i} ∈ ℝ^{m_{w_i} × m_{w_i}}`, are square only because `w_i`
is added to the state; the results do not need it.

**`Thm. 1` and the distributed zonotopes.** `Thm. 1` bounds the P-radius of the centralized
zonotope of `Prop. 2`, whose generators share one coefficient vector. The algorithm of Sec. IV-C
runs the distributed zonotopes of `Prop. 1`, where agent `i` has its own copy of every neighbour's
coefficients (`cat`, not a sum); the LMI is a statement about one common coefficient vector, so it does not by
itself bound the radii of those copies. The paper's text moves from the one to the other
("the distributed approach uses less information and is able to get similar results") without
showing that `Eq. 15` carries over, and so does the page: `Thm. 1` is proved for `Prop. 2`'s
zonotope, and `Sec. IV-C` for the enclosure, which is what `Prop. 1` gives at every gain.
