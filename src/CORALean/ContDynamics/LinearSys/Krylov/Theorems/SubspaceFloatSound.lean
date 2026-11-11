module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.SubspaceFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ArnoldiFloatHessenberg
public import CORALean.Global.StepOf
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorBoundFloatOuter

@[expose] public section

/-!
# An accepted order bounds the Krylov error, for every matrix

If `Krylov.subspaceFloat` accepts its order `k = m + 1` ([1, Thm. 3]'s test, extended to every
matrix), then for every `s ∈ [0, t_f]`
`‖e^{sA}c - ν V_k e^{sT_k}e₁‖₂ ≤ tol` for the stored basis `V_k` and Hessenberg matrix `T_k`:
`Krylov.error_le_errorBoundFloat` with the discs of `A` for `μ_A`, the computed column residuals
for `ε`, and the Hessenberg shape of the stored matrix (`arnoldiFloat_hessenberg`). No
nonexpansiveness of `A` is assumed; the first order tried is tested like the others.

## Inputs
* `p` – Newton steps per norm
* `q` – squarings of the exponential
* `εb` – breakdown threshold
* `A` – matrix
* `c` – start vector
* `k₀` – first order tried
* `step` – growth of the order per try
* `tf` – final time
* `tol` – tolerance
* `fuel` – number of tries

## Hypotheses
* `hq` – at least one squaring
* `ht` – final time nonnegative

## Conclusion
* an accepted order has error at most the tolerance over the whole horizon

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An accepted order of the stored state bounds the error. -/
private theorem aux_core (p q : ℕ) (hq : 1 ≤ q) (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (ν : 𝕋)
    (tf tol : 𝕋) (ht : 0 ≤ toReal tf) (k : ℕ) (st : (ℕ → Vector 𝕋 n) × (ℕ → ℕ → 𝕋))
    (hess : ∀ i j, j + 1 < i → toReal (st.2 i j) = 0)
    (hok : (decide (1 ≤ k) && Krylov.orderOkFloat p q (Krylov.quadBoundUp A)
        (fun j => Krylov.residualNormFloat p A st.1 st.2 j) c ν st.1 st.2 k tf tol) =
      true) : -- --- CONCL ---
    1 ≤ k ∧ ∀ m, k = m + 1 → ∀ s ∈ Set.Icc (0 : ℝ) (toReal tf),
      ‖exp (s • toRealMat A) *ᵥ (fun r => toReal (c r)) -
          toReal ν • ((Matrix.of fun (r : Fin n) (j : Fin (m + 1)) => toReal (st.1 j)[r]) *ᵥ
            (exp (s • Matrix.of fun (i j : Fin (m + 1)) => toReal (st.2 i j)) *ᵥ
              Pi.single 0 1))‖₂ ≤ toReal tol := by -- --- PROOF ---
  rw [Bool.and_eq_true] at hok
  obtain ⟨hk1, hok⟩ := hok
  refine ⟨of_decide_eq_true hk1, fun m hm s hs => ?_⟩
  subst hm
  unfold Krylov.orderOkFloat at hok
  rw [Bool.and_eq_true] at hok
  obtain ⟨hcap, hle⟩ := hok
  have hb := Krylov.error_le_errorBoundFloat p q A c ν st.1 st.2 m tf (Krylov.quadBoundUp A)
    (fun j => Krylov.residualNormFloat p A st.1 st.2 j) hq (fun i j hij => hess i j hij)
    (fun x => Krylov.quad_le_quadBoundUp A x)
    (fun j _ => Krylov.residual_le_residualNormFloat p A st.1 st.2 j) ht hcap s hs
  exact hb.trans (toReal_le_of_le hle)

/-- The search returns an accepted order only with its error under the tolerance. -/
private theorem aux_search (p q : ℕ) (hq : 1 ≤ q) (εb : 𝕋) (A : Mat 𝕋 n n) (c : Vec 𝕋 n)
    (step : ℕ) (tf tol : 𝕋) (ht : 0 ≤ toReal tf) (fuel : ℕ) : -- --- CONCL ---
    ∀ (k : ℕ) (ν : 𝕋),
      let r := Krylov.step_orderSearch p q εb A c ν (Krylov.quadBoundUp A) step tf tol fuel k
      r.ok = true → 1 ≤ r.order ∧ ∀ m, r.order = m + 1 → ∀ s ∈ Set.Icc (0 : ℝ) (toReal tf),
        ‖exp (s • toRealMat A) *ᵥ (fun i => toReal (c i)) -
            toReal r.ν • ((Matrix.of fun (i : Fin n) (j : Fin (m + 1)) => toReal (r.V j)[i]) *ᵥ
              (exp (s • Matrix.of fun (i j : Fin (m + 1)) => toReal (r.H i j)) *ᵥ
                Pi.single 0 1))‖₂ ≤ toReal tol := by -- --- PROOF ---
  -- the search stops at an accepted order, which `aux_core` bounds, or recurses
  induction fuel with
  | zero =>
    intro k ν
    simp only [Krylov.step_orderSearch]
    intro hok
    exact aux_core p q hq A c ν tf tol ht k _ (Krylov.arnoldiFloat_hessenberg p εb A c ν k) hok
  | succ fuel ih =>
    intro k ν
    rw [Krylov.step_orderSearch]
    dsimp only
    split_ifs with hcond
    · intro hok
      exact aux_core p q hq A c ν tf tol ht k _ (Krylov.arnoldiFloat_hessenberg p εb A c ν k) hok
    · exact ih _ ν


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.subspaceFloat_error_le (p q : ℕ) (hq : 1 ≤ q) (εb : 𝕋) (A : Mat 𝕋 n n)
    (c : Vec 𝕋 n) (k₀ step : ℕ) (tf tol : 𝕋) (ht : 0 ≤ toReal tf) (fuel : ℕ) : -- --- CONCL ---
    let r := Krylov.subspaceFloat p q εb A c k₀ step tf tol fuel
    r.ok = true → 1 ≤ r.order ∧ ∀ m, r.order = m + 1 → ∀ s ∈ Set.Icc (0 : ℝ) (toReal tf),
      ‖exp (s • toRealMat A) *ᵥ (fun i => toReal (c i)) -
          toReal r.ν • ((Matrix.of fun (i : Fin n) (j : Fin (m + 1)) => toReal (r.V j)[i]) *ᵥ
            (exp (s • Matrix.of fun (i j : Fin (m + 1)) => toReal (r.H i j)) *ᵥ
              Pi.single 0 1))‖₂ ≤ toReal tol := by -- --- PROOF ---
  exact aux_search p q hq εb A c step tf tol ht fuel _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
