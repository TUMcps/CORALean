# Discovering governing equations from data by sparse identification of nonlinear dynamical systems

```bibtex
@article{brunton2016discovering,
  author = {Brunton, S. L. and Proctor, J. L. and Kutz, J. N.},
  title = {Discovering governing equations from data by sparse identification of nonlinear dynamical systems},
  journal = {Proceedings of the National Academy of Sciences},
  year = {2016}
}
```

**Source:** https://arxiv.org/pdf/1509.03580 (arXiv v1, September 2015, "Discovering governing equations from data: Sparse identification of nonlinear dynamical systems", 26 pages, read in full; text extracted with `pypdf`). The PNAS paper of 2016 is a shorter revision of this preprint and is not open access; its numbering differs from the one used here, which is the preprint's, and nothing in the revision was read. CORA cites the paper in `contDynamics/@nonlinearSys/identify.m` and `@nonlinearSysDT/identify.m` and their private `priv_identifySparse.m` (algorithm `'sparse'`, "SINDy").  
**Inventory:** confirmed (equations (1)-(28), Sections 1-5, Code 1, the only algorithm, which is MATLAB code, Examples 1a, 1b, 2, 3 and the bifurcation examples, Figures 1-13 and Tables 1-7, no numbered theorems)

Sparse identification of nonlinear dynamics (SINDy) fits `ẋ = f(x)` as `Ẋ = Θ(X) Ξ` over a library
`Θ` of candidate functions, with `Ξ` sparse: by the LASSO (`Eq. 2`) or, as the paper prefers for
speed, by sequential thresholded least squares (`Code 1`: least squares, set the coefficients below
`λ` to zero, regress onto the rest, repeat). Formalized: the regression and the model read off `Ξ`
(`Eq. 7`-`Eq. 9`, `Eq. 13`), its equivalence with DMD for a linear library (`Eq. 14`), `Code 1` with
the regression an argument (a solver, as MATLAB's backslash). It provably guarantees: for
`λ > 0` the nonzero coefficients only shrink, the iteration reaches a fixed point within `p · n + 1`
passes, a fixed point holds only coefficients at least `λ` and is the regression onto them, and
exact data of a sparse `Ξ*` is recovered. Convergence results of later papers and the choice of
the library, the derivatives and `λ` are not in the paper's claims and not here.

CORA's `'sparse'` is not `Code 1`: it runs MATLAB's `lasso` (`Eq. 2`, a solver) on every row of
`ẋ`, takes the first column of its coefficient path, and refits the surviving terms by the dynamic
mode decomposition of [Proctor et al.](proctor-siads-dmd-control.md) (`priv_identifySparse.m`,
`aux_refineDynamicModeDecomposition`). The paper names LASSO as the alternative to `Code 1`, so this
is a choice among the paper's, not a deviation.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | `y = Θ ξ` for data `y ∈ ℝᵐ`, a library `Θ ∈ ℝᵐˣᵖ` and a coefficient vector `ξ ∈ ℝᵖ`. | n/a — a definition | `not-a-claim` |
| `Eq. 2` | The LASSO, `ξ = argmin_{ξ'} ‖Θ ξ' - y‖² + λ ‖ξ'‖₁`. | n/a — an optimization problem, solved by MATLAB's `lasso` in CORA: a subject CORALean does not cover (solver-dependent) | `not-a-claim` |
| `Eq. 3` | The system `ẋ = f(x)`. | n/a — a modelling assumption | `not-a-claim` |
| `Eq. 4` | The data matrices `X`, `Ẋ`, one snapshot per row. | [`SindyData.lean`](../../src/CORALean/Global/SindyData.lean) — `sindyRows` | `correct` |
| `Eq. 5` | The library `Θ(X) = [1 X XP2 XP3 … sin(X) cos(X) …]`, candidate functions of the columns of `X`. | [`SindyData.lean`](../../src/CORALean/Global/SindyData.lean) — `sindyTheta`: any library `θ` applied to every snapshot | `correct` |
| `Eq. 6` | The quadratic terms `XP2`. | n/a — an example of a library | `not-a-claim` |
| `Eq. 7` | `Ẋ = Θ(X) Ξ`, `Ξ = [ξ₁ … ξ_n]` sparse. | [`SindyData.lean`](../../src/CORALean/Global/SindyData.lean) — `sindy_data_iff`: `Ẋ = Θ(X) Ξ` iff `ẋ(t_k) = f(x(t_k))` at every snapshot | `correct` |
| `Eq. 8` | `ẋ_k = f_k(x) = Θ(xᵀ) ξ_k`. | [`SindyData.lean`](../../src/CORALean/Global/SindyData.lean) — `sindyModel_apply` | `correct` |
| `Eq. 9` | The model `ẋ = f(x) = Ξᵀ (Θ(xᵀ))ᵀ`. | [`SindyData.lean`](../../src/CORALean/Global/SindyData.lean) — `sindyModel`, `sindy_data_iff` | `correct` |
| `Eq. 10` | With noisy derivatives, `Ẋ = Θ(X) Ξ + η Z`, `Z` Gaussian. | n/a — a noise model | `not-a-claim` |
| `Alg. 1` | `Code 1`, sequential thresholded least squares: `Xi = Theta \ dXdt`, then `for k = 1:10`: `smallinds = abs(Xi) < lambda`, `Xi(smallinds) = 0`, and for each column `Xi(biginds, ind) = Theta(:, biginds) \ dXdt(:, ind)`. | [`SindyThreshold.lean`](../../src/CORALean/Global/SindyThreshold.lean) — `sindyStep`, `sindy` (one `let` per printed line, `K` passes, `sindy 10` the printed code; `solve ind S` is `Theta(:, biginds) \ dXdt(:, ind)`, an argument), `sindyBig_step_subset`: for `λ > 0` a pass only removes entries; [`SindyFixedPoint.lean`](../../src/CORALean/Global/SindyFixedPoint.lean) — `sindy_fixed_spec`: at a fixed point every entry is zero or at least `λ`, and the nonzero ones are the regression onto the survivors. `sindy_fixed_normalEq`: if the regression solves its normal equations so does the fixed point, on its support; `sindy_recovers`: exact data of a sparse `Ξ*` with entries at least `λ` is recovered after any number of passes | `correct` |
| `Sec. 3.1` | The algorithm "is computationally efficient, and it rapidly converges to a sparse solution in a small number of iterations"; the procedure "is continued until the non-zero coefficients converge". | [`SindyThreshold.lean`](../../src/CORALean/Global/SindyThreshold.lean) — `sindy_fixed`: for `λ > 0` and any regression, `K ≥ p · n + 1` passes (`p` terms, `n` columns) reach a fixed point | `underspecified` — "a small number" is not a quantity; `p · n + 1` is what holds for every regression, and the printed `10` suffices only when it is at least that. For `λ ≤ 0` nothing is thresholded; the efficiency claim is not a result |
| `Sec. 3.2` | Cross-validation and the Pareto front for choosing `λ`. | n/a — a heuristic for a parameter | `not-a-claim` |
| `Eq. 11` | The discrete-time system `x_{k+1} = f(x_k)`. | n/a — a modelling assumption | `not-a-claim` |
| `Eq. 12` | The data matrices `X₁^{m-1}`, `X₂^m` of snapshots and their successors. | n/a — a definition | `not-a-claim` |
| `Eq. 13` | `X₂ = Θ(X₁) Ξ`, "and the function `f` is the same as in Eq. (9)". | [`SindyData.lean`](../../src/CORALean/Global/SindyData.lean) — `sindy_data_iff` with `y = x_{k+1}` | `correct` |
| `Eq. 14` | For `Θ(x) = x`: `X₂ = X₁ Ξ ⟹ X₂ᵀ = Ξᵀ X₁ᵀ`, "equivalent to the DMD", which seeks a regression onto linear dynamics `Ξᵀ`. | [`SindyData.lean`](../../src/CORALean/Global/SindyData.lean) — `sindy_linear_transpose`: `X₂ = X₁ Ξ` iff `X₂ᵀ = Ξᵀ X₁ᵀ`, with the same squared error for every `Ξ`, so the least-squares `Ξᵀ` are those of DMD (`dmdCandidate_leastSquares` of [Proctor et al.](proctor-siads-dmd-control.md), `Eq. 7`) | `correct` |
| `Sec. 3.3.2` | High-dimensional systems: a low-rank POD basis `Xᵀ = Ψ Σ V*`, `x ≈ Ψ_r a` (`Eq. 15`, `Eq. 16`) and sparse identification of the Galerkin dynamics `ȧ = f_P(a)` (`Eq. 17`). | n/a — dimensionality reduction by POD, a subject CORALean does not cover: CORA's `identify` has no such step | `not-covered` |
| `Sec. 3.3.3` | Bifurcation parameters and external forcing: append `μ̇ = 0` (`Eq. 18`) or `ṫ = 1` (`Eq. 19`) and identify `f(x; μ)`, `f(x, u(t), t)` "readily". | n/a — a modelling extension of the library; CORA's `phi(x, u)` takes the input into the library | `not-a-claim` |
| `Sec. 4` | Examples 1a/1b (damped oscillators, `Eq. 20`, `Eq. 21`), 2 (the Lorenz system, `Eq. 22`, with noisy derivatives), 3 (the cylinder wake, `Eq. 23`, `Eq. 24`), and the logistic map and Hopf normal form (`Eq. 25`-`Eq. 28`): the right-hand sides and coefficients are recovered, "to within 0.03%" for Lorenz, with Tables 1-7. | n/a — numerical experiments on simulated data | `not-a-claim` |
| `Sec. 5` | Discussion: no assumptions on the form of the governing equations; open problems (symmetries, the choice of the function space). | n/a — a discussion | `not-a-claim` |

## Findings

**`Sec. 3.1` — what "converges rapidly" amounts to.** The paper says the thresholding is repeated
"until the non-zero coefficients converge" and that this takes "a small number of iterations";
`Code 1` runs ten. With `λ > 0` a coefficient that has been set to zero stays zero, so the set of
surviving coefficients only shrinks and, whatever the regression, the iterate is a fixed point after
at most `p · n + 1` passes for `p` library terms and `n` state components (`sindy_fixed`). That is
the guarantee; ten passes reach the fixed point whenever `p · n + 1 ≤ 10` and, for a larger library,
not by this argument. At the fixed point every coefficient is zero or at least `λ` in magnitude, and
the nonzero ones are the regression onto the surviving terms, a least-squares fit onto its support
(`sindy_fixed_normalEq`, for a regression that solves its normal equations). It is not claimed to
be the best fit over all supports, nor that the support is the true one except for exact data of a
sparse `Ξ*` (`sindy_recovers`). The regression `Theta(:, biginds) \ dXdt(:, ind)` is an argument,
as MATLAB's backslash returns the minimum-norm or a basic solution when the surviving columns are
dependent, and nothing here depends on which.
[`SindyThreshold.lean`](../../src/CORALean/Global/SindyThreshold.lean),
[`SindyFixedPoint.lean`](../../src/CORALean/Global/SindyFixedPoint.lean)
