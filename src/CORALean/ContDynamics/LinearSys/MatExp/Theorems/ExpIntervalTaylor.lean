module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
public import CORALean.ContSet.Interval.Real.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# `MatExp.expIntervalTaylor` encloses the Taylor truncation of every member

Induction on `η`: `Finset.sum_range_succ` peels the top term off the left,
matching `expIntervalTaylor`'s recursion on the right term by term, and
`plus_outer`/`smul_outer`/`matPow_outer` cover the two pieces.

## Inputs
* `A` – interval matrix
* `M` – member matrix
* `η` – Taylor order

## Hypotheses
* `hM` – member lies in the interval matrix

## Conclusion
* the member's Taylor truncation lies in the interval truncation
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expTaylor_mem_expIntervalTaylor (A : Interval (Mat ℝ n n))
    {M : Mat ℝ n n} (hM : M ∈ A.construct) (η : ℕ) :
    MatExp.expTaylor M η ∈ (MatExp.expIntervalTaylor A η).construct := by -- --- PROOF ---
  induction η with
  | zero =>
    show (∑ i ∈ Finset.range 1, ((Nat.factorial i : ℝ)⁻¹) • M ^ i)
        ∈ (Interval.smul ((Nat.factorial 0 : ℝ)⁻¹) (Interval.matPow A 0)).construct
    rw [Finset.sum_range_one]
    exact Interval.smul_outer _ _ (Interval.matPow_outer A hM 0)
  | succ k ih =>
    show (∑ i ∈ Finset.range (k + 1 + 1), ((Nat.factorial i : ℝ)⁻¹) • M ^ i)
        ∈ (Interval.plus
             (Interval.smul ((Nat.factorial (k + 1) : ℝ)⁻¹) (Interval.matPow A (k + 1)))
             (MatExp.expIntervalTaylor A k)).construct
    rw [Finset.sum_range_succ, add_comm (∑ i ∈ Finset.range (k + 1),
      ((Nat.factorial i : ℝ)⁻¹) • M ^ i) (((Nat.factorial (k + 1) : ℝ)⁻¹) • M ^ (k + 1))]
    exact Interval.plus_outer _ _
      (Set.add_mem_add (Interval.smul_outer _ _ (Interval.matPow_outer A hM (k + 1))) ih)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
