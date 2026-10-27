module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPoly
public import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrPolySearchEqSome
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SubsetAtUnitBox

@[expose] public section

/-!
# The region `linReachPoly` certifies is a computed set

The `R` of the step `linReachPoly` returns is not only what the factor box names under
`point`: it is the whole of candidate `k`'s `Rinit.dependent ⊞ (Rdiff + RallError)`,
because both summands have run `dependent` and so have no independent block for `point`
to miss — `subsetAt_unitBox`. That is what lets a caller discharge the step's
confinement against a set it can compute, as `confinement_of_subset` asks.

## Inputs
* `sys` – system
* `U` – input polynomial zonotope
* `A` – state Jacobian
* `B` – input Jacobian
* `xs` – state expansion point
* `us` – input expansion point
* `H` – Hessian family
* `E` – third-derivative bounds
* `Δt` – step size
* `η` – Taylor terms
* `errorOrder` – order for the error
* `intermediateOrder` – intermediate order
* `Rinit` – start polynomial zonotope
* `abstrerr` – previous abstraction error
* `fuel` – bound for the search
* `step` – returned step

## Hypotheses
* `h` – search returned the step

## Conclusion
* the step keeps the linearization and certifies a whole candidate region
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every candidate's differences have run `dependent`, so no independent block. -/
private theorem aux_abstrErrPolyCandidates_q (A : Mat ℝ n n) (xs : Vec ℝ n) (us : Vec ℝ m)
    (H : Fin n → Mat ℝ (n + m) (n + m)) (E : Fin n → Fin (n + m) → Mat ℝ (n + m) (n + m))
    (Δt : ℝ) (η errorOrder intermediateOrder : ℕ) (U : PolyZonotope (Vec ℝ m))
    (Rinit Rdiff VerrorStat : PolyZonotope (Vec ℝ n)) (abstrerr : Vec ℝ n)
    (k : ℕ) : -- --- CONCL ---
    (NonlinearSys.step_abstrErrPolyCandidates A xs us H E Δt η errorOrder intermediateOrder U Rinit
      Rdiff VerrorStat abstrerr k).1.q = 0 := by -- --- PROOF ---
  induction k generalizing abstrerr with
  | zero => rfl
  | succ k ih => exact ih _


-- =======================================  MAIN THEOREM  ======================================= --

/-- A `some` from `linReachPoly` is certified on all of candidate `k`'s region
`Rinit.dependent ⊞ (Rdiff + RallError)`, at the linearization it was handed. -/
theorem NonlinearSys.linReachPoly_region {sys : NonlinearSys n m} {U : PolyZonotope (Vec ℝ m)}
    {A : Mat ℝ n n} {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m}
    {H : Fin n → Mat ℝ (n + m) (n + m)} {E : Fin n → Fin (n + m) → Mat ℝ (n + m) (n + m)}
    {Δt : ℝ} {η errorOrder intermediateOrder : ℕ} {Rinit : PolyZonotope (Vec ℝ n)}
    {abstrerr : Vec ℝ n} {fuel : ℕ} {step : sys.LinStep (S := 𝒫𝒵) U}
    (h : sys.linReachPoly U A B xs us H E Δt η errorOrder intermediateOrder Rinit abstrerr fuel
      = some step) : -- --- CONCL ---
    step.A = A ∧ step.B = B ∧ step.xs = xs ∧ step.us = us ∧ ∃ k, step.R = (Rinit.dependent.plus
      (NonlinearSys.step_abstrErrPolyCandidates A xs us H E Δt η errorOrder intermediateOrder U
        Rinit
        (((NonlinearSys.linearize A).deltaReach (S := 𝒫𝒵) Δt η Rinit).plus
          ((NonlinearSys.linearize A).inputSolution (S := 𝒫𝒵) Δt η
            (linInput (S := 𝒫𝒵) sys.f A B xs us U (PolyZonotope.ofPoint 0))))
        (precompStatError (fun i => (2 : ℝ)⁻¹ • (H i).submatrix (Fin.castAdd m) (Fin.castAdd m))
          xs Rinit.dependent) abstrerr k).1).construct := by -- --- PROOF ---
  unfold NonlinearSys.linReachPoly at h
  -- the step is candidate `k`'s, over the factor box of a set with no independent block
  obtain ⟨k, -, hA, hB, hxs, hus, hR, -⟩ := NonlinearSys.abstrErrPolySearch_eq_some h
  refine ⟨hA, hB, hxs, hus, k, ?_⟩
  rw [hR]
  exact PolyZonotope.subsetAt_unitBox _
    (by simp only [PolyZonotope.plus, PolyZonotope.dependent, aux_abstrErrPolyCandidates_q])

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
