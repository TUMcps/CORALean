import CORALean.ContSet.Taylm.Float.Operations.Sqrt
import CORALean.ContSet.Taylm.Float.Theorems.TaylorOuter
import CORALean.ContSet.Taylm.Float.Theorems.SqrtCoefMem
import CORALean.ContSet.Taylm.Float.Theorems.SqrtBoundGe

/-!
# `Taylm.sqrt` encloses `√ ∘ f`

Where the centre and the bottom of the range are positive. `Taylm.taylor_outer` at `√`: the
coefficients `Taylm.sqrtCoef_mem` at the centre, the derivative bound `Taylm.sqrtBound_ge` at
the smaller of the centre and the bottom of the range.

[1, Def. 3 (sqrt)]: the result is a Taylor model of `sqrt ∘ f`.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sqrt_outer (q : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hpos : 0 < toReal (minimum T.constCoef T.bounds.1)) :
    (T.sqrt q).Encloses fun t => Real.sqrt (f t) := by -- --- PROOF ---
  have hmin : toReal (minimum T.constCoef T.bounds.1) =
      min (toReal T.constCoef) (toReal T.bounds.1) := toReal_minimum _ _
  have hc : 0 < toReal T.constCoef :=
    lt_of_lt_of_le (hmin ▸ hpos) (min_le_left _ _)
  refine Taylm.taylor_outer h Real.sqrt T.constCoef _ _ _ _
    (fun k _ => Taylm.sqrtCoef_mem q T.constCoef hc k)
    (fun ξ hξ => Real.contDiffAt_sqrt (ne_of_gt (lt_of_lt_of_le (hmin ▸ hpos) hξ.1)))
    (fun ξ hξ => Taylm.sqrtBound_ge q _ hpos _ (hmin ▸ hξ.1)) le_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
