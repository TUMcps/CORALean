import CORALean.ContSet.Interval.Float.Operations.Asinh

/-!
# `Interval.asinh` contains the image under `asinh`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.asinh_outer [SoundFloatArithmetic 𝕋] (p k : ℕ) (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, 0 ≤ toReal (I.inf i) → 2 * toReal (I.inf i) + 1 ≤ 2 ^ p / 2) :
    (fun x i => Real.arsinh (x i)) '' I.construct ⊆ (I.asinh p k).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  exact ⟨le_trans (asinhDown_le p k _ (hI i)) (Real.arsinh_le_arsinh.2 hx'.1),
    le_trans (Real.arsinh_le_arsinh.2 hx'.2) (le_asinhUp p k _)⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
