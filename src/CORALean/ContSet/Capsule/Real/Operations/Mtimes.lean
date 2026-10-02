import CORALean.ContSet.Capsule.Real.Capsule
import Mathlib.Data.Matrix.Mul

/-!
# `Capsule.mtimes`

CORA's `@capsule/mtimes.m` maps the centre and the generator, `M c` and `M g`, and rescales the
radius. The image of a Euclidean ball under `M` is an ellipsoid, not a ball, so the result is an
enclosure, and the radius has to be multiplied by a bound on the operator norm of `M` (its largest
singular value). Here the bound is the Frobenius norm, `sqrt (∑ᵢⱼ Mᵢⱼ²)`, which is at least the
largest singular value and needs no eigenvalue computation.

CORA scales by `max(eig(M Mᵀ))`, the *square* of the largest singular value, which is too small
whenever that value is under `1`; see `Capsule.mtimes_cora_counterexample` and FINDINGS.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Centre and generator multiplied by `M`, the radius by the Frobenius norm of `M`, an upper
bound of its operator norm. -/
noncomputable def Capsule.mtimes (M : Mat ℝ m n) (C : Capsule n) : Capsule m :=
  let σ := Real.sqrt (∑ i, ∑ j, M i j ^ 2)
  ⟨M.mulVec C.c, M.mulVec C.g, C.r * σ⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
