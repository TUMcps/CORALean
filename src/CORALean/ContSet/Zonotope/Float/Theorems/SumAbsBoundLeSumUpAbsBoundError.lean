import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError
import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.Zonotope.Real.Operations.AbsBound

/-!
# The nominal part's coordinate reaches, summed, never exceed the float sum

`Real.Zonotope.absBound` is a function of the representation, not of the set, so the
comparison is at the nominal zonotope: `|cⱼ| + Σₗ|Gⱼₗ|` is under `absBoundError`'s first two
terms, its error-box term nonnegative, and an upward sum stays above the exact one.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Σⱼ absBound(nominal Z)ⱼ ≤ sumUp absBoundError`. -/
theorem Zonotope.sum_absBound_le_sumUp_absBoundError (Z : Zonotope 𝕋 n) :
    ∑ j, Real.Zonotope.absBound (nominal Z) j
      ≤ toReal (sumUp fun j => Zonotope.absBoundError Z j) := by -- --- PROOF ---
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
  rw [Real.Zonotope.absBound, Zonotope.nominal_c, Zonotope.nominal_G, Zonotope.absBoundError]
  have hc : |toRealVec Z.c j| = toReal (absolute (Z.c j)) := (toReal_absolute _).symm
  have hG : ∑ l, |toReal (Z.G l j)| ≤ toReal (radius (fun i j => Z.G j i) j) :=
    sum_abs_le_radius (d := fun i j => Z.G j i) j
  have hE : 0 ≤ toReal (maximum (absolute (Z.E.inf j)) (absolute (Z.E.sup j))) := by
    rw [toReal_maximum, toReal_absolute]
    exact le_max_of_le_left (abs_nonneg _)
  refine le_trans ?_ (add_le_addUp _ _)
  refine le_trans ?_ (le_add_of_nonneg_right hE)
  refine le_trans ?_ (add_le_addUp _ _)
  rw [hc]
  exact add_le_add le_rfl hG

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
