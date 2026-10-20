module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat

@[expose] public section

/-!
# `MatExp.intervalCorrectionMatrix`, the correction `F` over a float box

[1, Sec. 3.3.1]'s `F`, as `Real.MatExp.intervalCorrectionMatrix` builds it:
orders `2` through `η` from `intervalCorrTerm`, each spanning the interval
between it and zero, everything past `η` in the remainder bound at `r • A` —
the bound the exponential and the input remainder of the same step are taken
at. The orders are stored once, not per entry, so a read costs a lookup.

## Inputs
* `A` – float interval matrix
* `r` – float step length
* `η` – Taylor order

## Output
* float interval matrix of the correction over the box

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of [1] over a whole box: `Σᵢ [min(Tᵢ, 0), max(Tᵢ, 0)] ⊕ [-E, E]`,
orders `2` through `η`, for a nonnegative `r`. -/
def MatExp.intervalCorrectionMatrix (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (η : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let E := MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul r r A)) η  -- E(r)
  let T : Vector (Interval (Mat 𝕋 n n)) (η - 1) :=                                  -- T₂ … T_η
    Vector.ofFn fun i => MatExp.intervalCorrTerm A r (i + 2)
  (⟨fun j k => subDown (sumDown fun i : Fin (η - 1) => minimum (T[i].inf j k) zero) E,
    fun j k => addUp (sumUp fun i : Fin (η - 1) => maximum (T[i].sup j k) zero) E⟩ :
      Interval (Mat 𝕋 n n)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
