# Dynamic mode decomposition with control

J. L. Proctor, S. L. Brunton and J. N. Kutz. "Dynamic mode decomposition with control". SIAM Journal on Applied Dynamical Systems, 15(1):142-161, 2016 (arXiv:1409.6358).

**Source:** https://arxiv.org/pdf/1409.6358 (arXiv v1, "DRAFT: last updated September 24, 2014", 10 pages, read in full; text extracted with `pypdf`). The SIAM version of 2016 is a revision of this draft and is not open access: its equation numbers may differ from the ones used here, which are the draft's, and nothing in the later revision was read. CORA cites the paper in `contDynamics/@linearSys/identify.m`, `@linearSysDT/identify.m`, `@nonlinearSys/identify.m`, `@nonlinearSysDT/identify.m` and the private `priv_identifyDMD.m` and `priv_identifySparse.m` of those classes (algorithm `'dmd'`, and the refit of `'sparse'`).  
**Inventory:** confirmed (equations (1)-(45), Sections I-VI, Examples 1-3, Figures 1-4; the paper has no numbered theorems or algorithms: the algorithm of Sec. III-D is given by its six steps)

Dynamic mode decomposition (DMD) fits `x_{k+1} = A x_k` to snapshots by `A = X' X†`, computed through
the truncated SVD of `X`; the paper adds the control input, `x_{k+1} = A x_k + B u_k`, and fits `A`
with `B` known (Sec. III-B, `Eq. 18`) or the stacked `[A B]` by the SVD of the stacked snapshots
`Ω = [X; Υ]` with a second SVD of `X'` for the reduced-order model (Sec. III-C, III-D). Formalized:
the data identities, the pseudo-inverse form, every SVD formula at the **full rank** (no
truncation) with the two guarantees it gives, that the candidate reproduces data the system
produced and that it is a least-squares fit; the reduced-order model and the dynamic modes
(eigenvectors of `Ā`), the six-step algorithm with the SVDs as arguments, and Example 1. Not
covered is what the paper recommends and CORA's rank loop does: truncation at a rank below the full
one, where `Ā` is neither a pseudo-inverse solution nor a fit; the rank search is `dmdSelect`
(`DmdSelect.lean`). Two printed statements fail: `Eq. 3` (matrices swapped) and the zero-eigenvalue
mode of `Eq. 13` and `Eq. 24`.

CORA's `'dmd'` is `Eq. 26`/`Eq. 28` with the regressor `[x; 1; u]` (`dmdRegressor`): the constant `1`
carries an offset `c` the paper does not have, one SVD of the stacked data (no output SVD, no
reduced-order model), and `Ā` at every rank up to the number of nonzero singular values.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | `x_{k+1} = A x_k`, `x ∈ ℝⁿ`, `A ∈ ℝⁿˣⁿ`. | n/a — a modelling assumption | `not-a-claim` |
| `Eq. 2` | The snapshot matrices `X = [x₁ … x_{m-1}]` and `X' = [x₂ … x_m]`, "i.e. `X' = AX`". | n/a — a definition | `not-a-claim` |
| `Eq. 3` | `X = A X'`. | [`DmdcCounterexamples.lean`](../../src/CORALean/Global/DmdcCounterexamples.lean) — `dmd_eq3_counterexample`: `X' = A X` and `X ≠ A X'` for `n = 1` | `fixed` — printed with `X` and `X'` swapped; the recursion gives `X' = A X`, as the text above (2) and the use in (4) say; see Findings |
| `Eq. 4` | `A = X' X†`, `†` the Moore-Penrose pseudo-inverse. | [`DmdPinv.lean`](../../src/CORALean/Global/DmdPinv.lean) — `IsPinv` (the four Penrose conditions), `IsPinv.unique`, `isPinv_svd`: `W S⁻¹ Vᵀ` is the pseudo-inverse of `X = V S Wᵀ`; `dmdCandidate_eq_mul_pinv`: `dmdCandidate X' V s W r = X' X†` at full rank `r` | `correct` |
| `Eq. 5` | The SVD `X = UΣV* = [Ũ Ũ_rem] [Σ̃ 0; 0 Σ_rem] [Ṽ*; Ṽ*_rem]`. | n/a — a definition; the SVD is an argument throughout, as in `dmdCandidate` | `not-a-claim` |
| `Eq. 6` | `X ≈ Ũ Σ̃ Ṽ*`, truncated at `r`. | n/a — a definition of the truncation; `dmdCandidate` zeroes the triples past `r` | `not-a-claim` |
| `Sec. II-B` | The Eckart-Young theorem [11] gives a rigorous and popular way to choose the truncation `r`. | n/a — restated from Eckart and Young [11] | `restated` |
| `Eq. 7` | `A ≈ Ā = X' Ṽ Σ̃⁻¹ Ũ*`. | [`DmdCandidateFit.lean`](../../src/CORALean/Global/DmdCandidateFit.lean) — `dmdCandidate_mul_eq`: at full rank `Ā X = X'` for data `X' = A X`; [`DmdCandidateLeastSquares.lean`](../../src/CORALean/Global/DmdCandidateLeastSquares.lean) — `dmdCandidate_leastSquares`: `Ā` minimizes `‖X' - A X‖`; [`DmdPinv.lean`](../../src/CORALean/Global/DmdPinv.lean) — `Ā = X' X†` | `underspecified` — "≈" is not quantified for the truncated `Ā`; the exact data and full rank case is formalized, a truncation below the rank is neither a fit nor a pseudo-inverse solution and not covered |
| `Eq. 8` | The model `x_{k+1} = Ā x_k`. | n/a — a modelling choice | `not-a-claim` |
| `Eq. 9-12` | The reduced-order model on `x = Ũ x̃`: `x̃_{k+1} = Ũ* Ā Ũ x̃_k = Ũ* X' Ṽ Σ̃⁻¹ x̃_k = Ã x̃_k`, `Ã = Ũ* X' Ṽ Σ̃⁻¹`. | [`DmdReduced.lean`](../../src/CORALean/Global/DmdReduced.lean) — `dmdCandidate_reduced`: `Ũᵀ Ā Ũ = Ũᵀ X' Ṽ Σ̃⁻¹` for `ŨᵀŨ = I` | `correct` |
| `Eq. 13` | The dynamic mode of an eigenpair `Ã w = λ w` is `φ = X' Ṽ Σ̃⁻¹ w` (Exact DMD) if `λ ≠ 0`, and `φ = Ũ w` if `λ = 0`; "the eigenvectors of `Ā` are called dynamic modes". | [`DmdReduced.lean`](../../src/CORALean/Global/DmdReduced.lean) — `dmd_mode_matrix`, `dmd_mode_vec`: `Ā φ = λ φ` for `φ = X' Ṽ Σ̃⁻¹ w`, and `φ ≠ 0` for `λ ≠ 0`; [`DmdcCounterexamples.lean`](../../src/CORALean/Global/DmdcCounterexamples.lean) — `dmd_zeroMode_counterexample`: `Ũ w` is not an eigenvector of `Ā` for `λ = 0` | `fixed` — for `λ = 0` the mode `Ũ w` is in general no eigenvector of `Ā` (it is a projected mode, as in Tu et al.); `X' Ṽ Σ̃⁻¹ w` is one whenever nonzero; real eigenpairs only; see Findings |
| `Remark` | The eigenvalues of `Ã` and `Ā` are equivalent [34], the eigenvectors related by a linear transformation. | n/a — restated from Schmid [34] | `restated` |
| `Eq. 14` | The system with control, `x_{k+1} = A x_k + B u_k`. | n/a — a modelling assumption | `not-a-claim` |
| `Eq. 15` | The input snapshots `Υ = [u₁ … u_{m-1}]`. | n/a — a definition | `not-a-claim` |
| `Eq. 16` | `X' = A X + B Υ`. | [`DmdcData.lean`](../../src/CORALean/Global/DmdcData.lean) — `dmdc_data_matrix`: the recursion at every snapshot is `X' = A X + B Υ` | `correct` |
| `Eq. 17` | `X' - B Υ = A X`. | [`DmdcData.lean`](../../src/CORALean/Global/DmdcData.lean) — `dmdc_data_sub` | `correct` |
| `Eq. 18` | `B` known: `A ≈ Ā = (X' - B Υ) Ṽ Σ̃⁻¹ Ũ*`. | [`DmdcFit.lean`](../../src/CORALean/Global/DmdcFit.lean) — `dmdcKnownB_fit`: at full rank `Ā X = X' - B Υ` for data of the system; `dmdcKnownB_leastSquares`: `Ā` minimizes `‖X' - B Υ - A X‖`; `dmdCandidate_eq_of_square`: a square `Ũ` gives `Ā = A` | `underspecified` — as `Eq. 7`: "≈", and the truncated `Ā`, are not quantified; exact data and full rank are formalized |
| `Sec. III-B` | "Note, if the control snapshots are `u_j = 0` the derivation is equivalent to DMD"; "if external control has been applied to the system, standard DMD would produce incorrect dynamic information". | [`DmdcFit.lean`](../../src/CORALean/Global/DmdcFit.lean) — `dmdcKnownB_zero_input`: `Υ = 0` is `Eq. 7`; [`DmdcExample1.lean`](../../src/CORALean/Global/DmdcExample1.lean) — `dmdcEx1_dmd_wrong`: on the data of Example 1 the only DMD fit is the stable closed loop, not the unstable `A` | `underspecified` — "incorrect" is not a quantity; formalized as the paper's own example |
| `Eq. 19` | The model `x_{k+1} = Ā x_k + B u_k`. | n/a — a modelling choice | `not-a-claim` |
| `Eq. 20-23` | The reduced model with known `B`: `x̃_{k+1} = Ũ* Ā Ũ x̃_k + Ũ* B u_k = Ã x̃_k + B̃ u_k`, `Ã = Ũ* (X' - B Υ) Ṽ Σ̃⁻¹`. | [`DmdReduced.lean`](../../src/CORALean/Global/DmdReduced.lean) — `dmdCandidate_reduced` at `X' - B Υ`; [`DmdcReduced.lean`](../../src/CORALean/Global/DmdcReduced.lean) — `dmdc_reduced_step`: `Ũᵀ (Ā Ũ x̃ + B u) = (Ũᵀ Ā Ũ) x̃ + (Ũᵀ B) u` | `correct` |
| `Eq. 24` | The dynamic modes with known `B`: `φ = (X' - B Υ) Ṽ Σ̃⁻¹ w`, `Ũ w` for `λ = 0`. | [`DmdReduced.lean`](../../src/CORALean/Global/DmdReduced.lean) — `dmd_mode_vec` at `X' - B Υ` | `fixed` — the `λ = 0` case of `Eq. 13` again; see Findings |
| `Eq. 25` | `X' = [A B] [X; Υ] = G Ω`. | [`DmdcData.lean`](../../src/CORALean/Global/DmdcData.lean) — `dmdc_data_stack`: the recursion at every snapshot is `X' = [A B] Ω`, `dmdcStack_mulVec`, `dmdcBlocks_dmdcStack` | `correct` |
| `Sec. III-C` | The truncation value `p` of `Ω` should be larger than that of `X'` (`p > r`); the left singular vectors `Ũ` of `Ω` define the input space, not the state space. | n/a — a recommendation and an explanation | `not-a-claim` |
| `Eq. 26` | `G ≈ Ḡ = X' Ṽ Σ̃⁻¹ Ũ*` for the SVD `Ω ≈ Ũ Σ̃ Ṽ*`. | [`DmdcFit.lean`](../../src/CORALean/Global/DmdcFit.lean) — `dmdcUnknownB_fit`: at full rank `Ā x_k + B̄ u_k = x_{k+1}` for data of the system; `dmdcUnknownB_leastSquares`: `Ḡ` minimizes `‖X' - G Ω‖` | `underspecified` — as `Eq. 7`; the truncation `p` is not covered |
| `Eq. 27` | `[A, B] ≈ [Ā, B̄]`. | n/a — an approximation statement; its content is `Eq. 26` and `Eq. 28` | `not-a-claim` |
| `Eq. 28` | `[Ā, B̄] = [X' Ṽ Σ̃⁻¹ Ũ₁*, X' Ṽ Σ̃⁻¹ Ũ₂*]`, `Ũ = [Ũ₁*, Ũ₂*]ᵀ`. | [`DmdcFit.lean`](../../src/CORALean/Global/DmdcFit.lean) — `dmdcBlocks_candidate`: the state and input blocks of `Ḡ` are `X' Ṽ Σ̃⁻¹` times the state and input rows of `Ũ`, transposed, at every truncation | `correct` |
| `Eq. 29` | `Ã = Û* Ā Û = Û* X' Ṽ Σ̃⁻¹ Ũ₁* Û`, `Û` the left singular vectors of `X'`. | [`DmdcReduced.lean`](../../src/CORALean/Global/DmdcReduced.lean) — `dmdc_reducedA_eq` | `correct` |
| `Eq. 30` | `B̃ = Û* B̄ = Û* X' Ṽ Σ̃⁻¹ Ũ₂*`. | [`DmdcReduced.lean`](../../src/CORALean/Global/DmdcReduced.lean) — `dmdc_reducedB_eq` | `correct` |
| `Eq. 31` | The reduced-order model `x̃_{k+1} = Ã x̃_k + B̃ u_k`. | [`DmdcReduced.lean`](../../src/CORALean/Global/DmdcReduced.lean) — `dmdc_reduced_step`: projecting a step of the full model by `Ûᵀ` is a step of the reduced one, for `x = Û x̃` | `correct` |
| `Eq. 32` | The dynamic modes `φ = X' Ṽ Σ̃⁻¹ Ũ₁* Û w` of `Ã w = λ w`. | [`DmdcReduced.lean`](../../src/CORALean/Global/DmdcReduced.lean) — `dmdc_mode_proj_vec`: `Ā φ = λ φ`, and `φ ≠ 0` for `λ ≠ 0` | `underspecified` — an eigenvector of `Ā` only if `Û` spans the columns of `X'` (the output SVD untruncated); real eigenpairs |
| `Sec. III-D` | The algorithm: (1) stack `X`, `Υ` into `Ω`; (2) SVD of `Ω`, truncation `p`; (3) SVD of `X'`, truncation `r`; (4) `Ã`, `B̃`; (5) eigendecomposition of `Ã`; (6) the modes `Φ`. | [`DmdcAlgorithm.lean`](../../src/CORALean/Global/DmdcAlgorithm.lean) — `dmdcAlgorithm`, one `let` per step, the SVDs and eigenvectors arguments; `dmdcAlgorithm_eq`: its outputs are `Ûᵀ Ā Û`, `Ûᵀ B̄`, `Ā Û W` | `correct` |
| `Eq. 33` | Step 4: `Ã = Û* X' Ṽ Σ̃⁻¹ Ũ₁* Û`. | [`DmdcAlgorithm.lean`](../../src/CORALean/Global/DmdcAlgorithm.lean) — `dmdcAlgorithm` | `correct` |
| `Eq. 34` | Step 4: `B̃ = Û* X' Ṽ Σ̃⁻¹ Ũ₂*`. | [`DmdcAlgorithm.lean`](../../src/CORALean/Global/DmdcAlgorithm.lean) — `dmdcAlgorithm` | `correct` |
| `Eq. 35` | Step 5: `Ã W = W Λ`. | n/a — the definition of the eigendecomposition, an argument of `dmdcAlgorithm` | `not-a-claim` |
| `Eq. 36` | Step 6: `Φ = X' Ṽ Σ̃⁻¹ Ũ₁* Û W`. | [`DmdcAlgorithm.lean`](../../src/CORALean/Global/DmdcAlgorithm.lean) — `dmdcAlgorithm_modes`; [`DmdcReduced.lean`](../../src/CORALean/Global/DmdcReduced.lean) — `dmdc_mode_proj`: `Ā Φ = Φ Λ` | `underspecified` — as `Eq. 32` |
| `Example 1` | Sec. IV-A: the unstable system `x_{k+1} = [1.5 0; 0 0.1] x_k + [1; 0] u_k` with `u_k = -x_{1,k}` from `x₀ = [4, 7]ᵀ`; the snapshots (38)-(40) and the SVD (41)-(43) are printed. | [`DmdcExample1.lean`](../../src/CORALean/Global/DmdcExample1.lean) — `dmdcEx1_data`: the printed snapshots obey `X' = A X + B Υ`; `dmdcEx1_unique`: `X` has full row rank | `correct` — the rounded singular values and vectors are not restated |
| `Eq. 44` | The computed `Ā` recovers `diag(1.5, 0.1)`. | [`DmdcExample1.lean`](../../src/CORALean/Global/DmdcExample1.lean) — `dmdcEx1_recovers`: the only fit of `X' - B Υ = A' X` is `A`; the full-rank candidate is that fit by `dmdCandidate_eq_of_square` | `correct` |
| `Example 2` | Sec. IV-B: a random stable 5-dimensional system with 2 inputs and 100 measurements; the frequency responses of the model and DMDc agree. | n/a — a numerical experiment | `not-a-claim` |
| `Example 3` | Sec. IV-C: a sparse system in the 2-D Fourier domain, 128 × 128, with spatial actuation; the eigenvalues are found more accurately than by DMD. | n/a — a numerical experiment | `not-a-claim` |
| `Eq. 45` | The stacked data matrix of DMDc with an impulse response, `Ω = [0 x₁ … x_{m_c}; u₀ 0 … 0]`. | n/a — a definition, in the comparison with ERA | `not-a-claim` |
| `Sec. V` | The relation to ERA and OKID: data, `A`, `B`, `C` matrices. | n/a — a comparison with other methods | `not-a-claim` |

## Findings

**`Eq. 3` — the matrices swapped.** The paper writes the snapshot relation as `X = A X'`, while
the sentence before it, `X' = AX` (Eq. 2), and the solution `A = X' X†` of (4) both have
`X' = A X`. The two differ already for `n = 1`: with `A = 2`, `X = 1`, `X' = 2` the recursion holds
and `X = A X'` reads `1 = 4`. The same slip is not repeated for the input (`Eq. 16`).
[`DmdcCounterexamples.lean`](../../src/CORALean/Global/DmdcCounterexamples.lean)

**`Eq. 13`, `Eq. 24` — the mode for the eigenvalue zero.** The paper says that for `λ = 0` the
dynamic mode is `Ũ w` (the Exact-DMD formula `X' Ṽ Σ̃⁻¹ w` having been given for `λ ≠ 0`), and calls
the eigenvectors of `Ā` dynamic modes. `Ũ w` is in general no eigenvector of `Ā = X' Ṽ Σ̃⁻¹ Ũ*`:
for `X = [1, 0]ᵀ`, `X' = [0, 1]ᵀ` the reduced `Ã` is `0`, `w = 1` is an eigenvector for `0`,
and `Ā Ũ w = [0, 1]ᵀ ≠ 0`. What is true for every eigenpair is `Ā (X' Ṽ Σ̃⁻¹ w) = λ (X' Ṽ Σ̃⁻¹ w)`
(`dmd_mode_vec`), for `λ = 0` too, and the vector is nonzero when `λ ≠ 0`; `Ũ w` is the *projected*
DMD mode of Tu et al., which is not claimed to be an eigenvector of `Ā`. `Eq. 24` repeats the
statement with `X' - B Υ`.
[`DmdReduced.lean`](../../src/CORALean/Global/DmdReduced.lean),
[`DmdcCounterexamples.lean`](../../src/CORALean/Global/DmdcCounterexamples.lean)
