module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.InvFactorialBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# `MatExp.expIntervalTaylor` encloses the Taylor truncation, over a float

Induction on `η`, exactly as `Real.MatExp.expTaylor_mem_expIntervalTaylor`
does: `Finset.sum_range_succ` peels the top term off the left, matching the
recursion term by term, and `matPlus_outer`/`smul_outer`/`matPow_outer` cover
the two pieces — `smul_outer` at `invFactorialBounds`'s two facts rather than
one exact coefficient.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expTaylor_mem_expIntervalTaylor (A : Interval (Mat 𝕋 n n))
    {M : Mat ℝ n n} (hM : M ∈ A.construct) (η : ℕ) :
    Real.MatExp.expTaylor M η ∈ (MatExp.expIntervalTaylor A η).construct := by -- --- PROOF ---
  induction η with
  | zero =>
    show (∑ i ∈ Finset.range 1, ((Nat.factorial i : ℝ)⁻¹) • M ^ i)
        ∈ (Interval.smul (MatExp.invFactorialBounds 0).inf (MatExp.invFactorialBounds 0).sup
            (Interval.matPow A 0)).construct
    rw [Finset.sum_range_one]
    exact Interval.smul_outer (MatExp.invFactorialBounds_mem 0).1
      (MatExp.invFactorialBounds_mem 0).2 (Interval.matPow A 0) (Interval.matPow_outer A hM 0)
  | succ k ih =>
    -- peel the top term, matching `expIntervalTaylor`'s own right recursion
    show (∑ i ∈ Finset.range (k + 1 + 1), ((Nat.factorial i : ℝ)⁻¹) • M ^ i)
        ∈ (Interval.matPlus
             (Interval.smul (MatExp.invFactorialBounds (k + 1)).inf
               (MatExp.invFactorialBounds (k + 1)).sup (Interval.matPow A (k + 1)))
             (MatExp.expIntervalTaylor A k)).materialiseMat.construct
    rw [Interval.materialiseMat_eq, Finset.sum_range_succ, add_comm (∑ i ∈ Finset.range (k + 1),
      ((Nat.factorial i : ℝ)⁻¹) • M ^ i) (((Nat.factorial (k + 1) : ℝ)⁻¹) • M ^ (k + 1))]
    exact Interval.matPlus_outer _ _
      (Interval.smul_outer (MatExp.invFactorialBounds_mem (k + 1)).1
        (MatExp.invFactorialBounds_mem (k + 1)).2 (Interval.matPow A (k + 1))
        (Interval.matPow_outer A hM (k + 1)))
      ih

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
