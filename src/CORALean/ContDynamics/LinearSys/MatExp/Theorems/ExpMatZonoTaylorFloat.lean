import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTaylorFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.InvFactorialBoundsFloat
import CORALean.ContSet.Zonotope.Float.Theorems.MatPowOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MatPlusOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MatSmulOuter

/-!
# The Taylor truncation lies in the float matrix zonotope's Taylor truncation

`Real.MatExp.expTaylor_mem_expMatZonoTaylor` in floats: the same induction, each order
`smul_outer` at `invFactorialBounds_mem` over `matPow_outer`, joined by `plus_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One order of the series: the member's power, scaled. -/
theorem MatExp.aux_term_mem_expMatZonoTerm (M : Zonotope (Mat 𝕋 n n)) {A : Mat ℝ n n}
    (hA : A ∈ M.construct) (i : ℕ) :
    ((Nat.factorial i : ℝ)⁻¹) • A ^ i ∈ (MatExp.expMatZonoTerm M i).construct :=
  Zonotope.matSmul_outer (MatExp.invFactorialBounds_mem i).1 (MatExp.invFactorialBounds_mem i).2
    (M.matPow i) (Zonotope.matPow_outer M hA i)


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expTaylor_mem_expMatZonoTaylor (M : Zonotope (Mat 𝕋 n n)) {A : Mat ℝ n n}
    (hA : A ∈ M.construct) (η : ℕ) :
    Real.MatExp.expTaylor A η ∈ (MatExp.expMatZonoTaylor M η).construct := by -- --- PROOF ---
  induction η with
  | zero =>
      have h : Real.MatExp.expTaylor A 0 = ((Nat.factorial 0 : ℝ)⁻¹) • A ^ 0 :=
        Finset.sum_range_one _
      rw [h]
      exact MatExp.aux_term_mem_expMatZonoTerm M hA 0
  -- the last order split off both the sum and the zonotope, then added back
  | succ k ih =>
      have h : Real.MatExp.expTaylor A (k + 1)
          = ((Nat.factorial (k + 1) : ℝ)⁻¹) • A ^ (k + 1) + Real.MatExp.expTaylor A k := by
        show ∑ i ∈ Finset.range (k + 1 + 1), ((Nat.factorial i : ℝ)⁻¹) • A ^ i = _
        rw [Finset.sum_range_succ]
        exact add_comm _ _
      rw [h]
      show _ ∈ (Zonotope.matPlus (MatExp.expMatZonoTerm M (k + 1))
        (MatExp.expMatZonoTaylor M k)).materialiseMat.construct
      rw [Zonotope.materialiseMat_eq]
      exact Zonotope.matPlus_outer _ _
        (Set.add_mem_add (MatExp.aux_term_mem_expMatZonoTerm M hA (k + 1)) ih)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
