import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat

/-!
# `MatExp.intervalConstCorrectionMatrix`, the constant input's correction `F̃` over a float box

[1, Prop. 3.4]'s `F̃`, as `Real.MatExp.intervalConstCorrectionMatrix` builds it: orders `1`
through `η` from `intervalConstCorrTerm`, each spanning the interval between it and zero,
and everything past `η` in the remainder bound at `r • A` scaled by `r`. This is the float
`G` (`Real.MatExp.constCorrectionMatrix`) that `curvatureEnclosure` needs, enclosed outward
as an interval matrix: the float layer has no point matrix to hold it in.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F̃` of [1] over a whole box: `Σᵢ [min(Tᵢ, 0), max(Tᵢ, 0)] ⊕ [-r E, r E]`, orders `1`
through `η`, for a nonnegative `r`. -/
def MatExp.intervalConstCorrectionMatrix (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (η : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let E := MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul r r A)) η  -- E(r)
  let rE := mulUp r E                                                              -- r E(r)
  let T : Vector (Interval (Mat 𝕋 n n)) η :=                                         -- T₁ … T_η
    Vector.ofFn fun i => MatExp.intervalConstCorrTerm A r i
  (⟨fun j k => subDown (sumDown fun i : Fin η => minimum (T[i].inf j k) zero) rE,
    fun j k => addUp (sumUp fun i : Fin η => maximum (T[i].sup j k) zero) rE⟩ :
      Interval (Mat 𝕋 n n)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
