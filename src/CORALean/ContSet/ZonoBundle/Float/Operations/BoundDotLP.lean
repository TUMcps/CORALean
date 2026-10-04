import CORALean.ContSet.Conversion.Float.ZonoBundle_to_ConZonotope
import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound
import CORALean.ContSet.ZonoBundle.Float.Operations.SupportBound

/-!
# A float bundle's bound by CORA's linear program

CORA's `supportFunc_` of a `zonoBundle` stacks every member's generators and
solves one linear program over the intersection. `conZonotopeAll` is that
program's feasible set, enclosed, and `ConZonotope.boundDot` bounds it by a
dual certificate the exact simplex proposes and rounded arithmetic checks. The
least of that and `boundDot`'s member minimum is returned, `minimum` being
exact, so the result is never worse than the members' own bounds and is the
program's value up to rounding where the simplex's weights are optimal. An
upper bound only.

Needs `0 < zB.k`, as `boundDot` does.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least of the members' bounds and the certified bound of the whole
bundle's constrained zonotope. -/
def ZonoBundle.boundDotLP (zB : ZonoBundle 𝕋 n) (hk : 0 < zB.k) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    FloatBound 𝕋 zB.construct c where
  val := minimum (zB.boundDot hk a hc).val ((zB.conZonotopeAll hk).boundDot a hc).val
  le x hx := by
    rw [toReal_minimum]
    exact le_min ((zB.boundDot hk a hc).le x hx)
      (((zB.conZonotopeAll hk).boundDot a hc).le x (zB.conZonotopeAll_contains hk hx))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
