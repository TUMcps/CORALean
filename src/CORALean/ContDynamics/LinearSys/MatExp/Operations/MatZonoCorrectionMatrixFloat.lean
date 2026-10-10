import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.MatZonoCorrTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat

/-!
# `MatExp.matZonoCorrectionMatrix`, the correction `F` at a float matrix zonotope

`Real.MatExp.matZonoCorrectionMatrix` rounded, CORA's `priv_tie` of `@linParamSys`
with `obj.A` a `matZonotope`: orders `2` through `η` from `matZonoCorrTerm`, each the
box of a matrix-zonotope power spanning the interval between it and zero, and
everything past `η` in the remainder bound at `r` times the box the zonotope
encloses, as `intervalCorrectionMatrix` takes it at a box. The orders are stored
once, not per entry, so a read costs a lookup.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of `priv_tie` at a matrix zonotope: `Σᵢ [min(Tᵢ, 0), max(Tᵢ, 0)] ⊕ [-E, E]`,
orders `2` through `η`, for a nonnegative `r`. -/
def MatExp.matZonoCorrectionMatrix (M : GZonotope (Mat 𝕋 n n)) (r : 𝕋) (η : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let E := MatExp.expRemainderBound                                  -- E(r), at the box
    (MatExp.normUpperBound (Interval.smul r r M.interval)) η
  let T : Vector (Interval (Mat 𝕋 n n)) (η - 1) :=                  -- T₂ … T_η
    Vector.ofFn fun i => MatExp.matZonoCorrTerm M r (i + 2)
  (⟨fun j k => subDown (sumDown fun i : Fin (η - 1) => minimum (T[i].inf j k) zero) E,
    fun j k => addUp (sumUp fun i : Fin (η - 1) => maximum (T[i].sup j k) zero) E⟩ :
      Interval (Mat 𝕋 n n)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
