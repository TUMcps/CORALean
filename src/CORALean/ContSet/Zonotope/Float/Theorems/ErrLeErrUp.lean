import CORALean.ContSet.Zonotope.Float.Operations.ErrUp
import CORALean.ContSet.Zonotope.Float.Theorems.AbsLeAbsBoundError
import CORALean.Global.ErrLeNormOfAbsLe

/-!
# `errUp` bounds `err`

Every set inside `Z`'s `construct` has its [1] eq. (11) `err` under `Z.errUp`: each point's
coordinate is under `absBoundError` (`abs_le_absBoundError`), `err_le_norm₂_of_forall_abs_le`
turns that into a bound on `err` by the Euclidean norm of the magnitudes, and `norm₂_le_normUp`
bounds that norm from above: a Euclidean bound, which `Zonotope.errOp`, in the sup norm,
could not give.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `err S ≤ Z.errUp` for every `S` inside `Z`'s `construct`. -/
theorem Zonotope.err_le_errUp (Z : Zonotope (Vec 𝕋 n)) {S : Set (Vec ℝ n)}
    (hS : S ⊆ Zonotope.construct Z) : err S ≤ toReal Z.errUp := by -- --- PROOF ---
  have hnorm := norm₂_le_normUp (v := fun j => toReal (Z.absBoundError j))
    (m := fun j => Z.absBoundError j) 64 fun j => le_rfl
  refine le_trans (err_le_norm₂_of_forall_abs_le (m := fun j => toReal (Z.absBoundError j))
    fun y hy i => ?_) hnorm
  exact (Zonotope.abs_le_absBoundError (hS hy) i).trans (le_abs_self _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
