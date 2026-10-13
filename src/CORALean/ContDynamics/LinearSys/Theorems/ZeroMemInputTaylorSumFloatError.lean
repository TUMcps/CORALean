module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumFloat
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.ZeroMemMtimesIntervalMatError
public import CORALean.ContSet.Zonotope.Float.Theorems.ZeroMemPlusError

@[expose] public section

/-!
# `inputTaylorSumFloat` keeps the origin in its error box

Every product `[Tᵢ] U` keeps `0` (`[Tᵢ]` holds the exact `Tᵢ`,
`smul_pow_mem_intervalInputTerm`), and every float sum does. What
`plus_subset_add_box` and `mtimesIntervalMat_subset_add_box` ask of their
operands when the float sum is bounded from above.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every partial float Taylor sum keeps `0` in its error box, given `U` does, at `r ≥ 0`. -/
theorem LinearSys.zero_mem_inputTaylorSumFloat_error (sys : LinearSys 𝕋 n) {r : 𝕋}
    (hr : 0 ≤ toReal r) {U : Zonotope (Vec 𝕋 n)} (hU : (0 : Vec ℝ n) ∈ U.E.construct) :
    ∀ i, (0 : Vec ℝ n) ∈ (sys.inputTaylorSumFloat r U i).E.construct := by -- --- PROOF ---
  have hterm : ∀ i, (0 : Vec ℝ n) ∈
    (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
      (MatExp.intervalInputTerm (Interval.point sys.A) r i) U).E.construct := fun i => by
    show (0 : Vec ℝ n) ∈ ((Zonotope.mtimesIntervalMat _ U).materialise).E.construct
    rw [Zonotope.materialise_eq]
    exact Zonotope.zero_mem_mtimesIntervalMat_error
      (MatExp.smul_pow_mem_intervalInputTerm _ hr (Interval.mem_point sys.A) i) hU
  -- order `0` is one product, each further order one more float sum
  intro i
  induction i with
  | zero => exact hterm 0
  | succ i ih =>
    show (0 : Vec ℝ n) ∈ ((Zonotope.plus _ _).materialise).E.construct
    rw [Zonotope.materialise_eq]
    exact Zonotope.zero_mem_plus_error ih (hterm (i + 1))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
