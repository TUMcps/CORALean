module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowTightFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `MatExp.intervalCorrectionMatrixTight`, CORA's `F` over a float box, at CORA's coefficient

`Real.MatExp.correctionMatrixEntrywise` over a float box, the `F` of [1]: orders `2` through `η`
from `intervalCorrTermTight`, as `intervalCorrectionMatrix` has them, and the tail in the entry's
own bound `W` where `intervalCorrectionMatrix` takes one scalar bound. The coefficient is
`corrCoeffLowTight`, CORA's to within rounding, where `intervalCorrectionMatrixEntrywise` and its
constant counterpart take `corrCoeffLow`.

## Inputs
* `A` – float interval matrix
* `r` – float step length
* `η` – Taylor order
* `W` – float bound on the entrywise remainder

## Output
* float interval matrix of the correction over the box

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `corrCoeff i · r^i/i! · Aⁱ` over the whole box `A`, for a nonnegative `r`. -/
@[step_of MatExp.intervalCorrectionMatrixTight]
def MatExp.step_intervalCorrTermTight (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (i : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let cLo := mulDown (MatExp.corrCoeffLowTight i) (MatExp.taylorCoeffBounds r i).sup  -- κ · r^i/i!
  (Interval.smul cLo zero (Interval.matPow A i)).materialiseMat               -- [κ r^i/i!, 0] Aⁱ


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of CORA over a whole box: `Σᵢ [min(Tᵢ, 0), max(Tᵢ, 0)] ⊕ [-W, W]`, orders `2`
through `η`, for a nonnegative `r`. -/
def MatExp.intervalCorrectionMatrixTight (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (η : ℕ)
    (W : Mat 𝕋 n n) : Interval (Mat 𝕋 n n) :=
  let T : Vector (Interval (Mat 𝕋 n n)) (η - 1) :=                                  -- T₂ … T_η
    Vector.ofFn fun i => MatExp.step_intervalCorrTermTight A r (i + 2)
  (⟨fun j k => subDown (sumDown fun i : Fin (η - 1) => minimum (T[i].inf j k) zero) (W j k),
    fun j k => addUp (sumUp fun i : Fin (η - 1) => maximum (T[i].sup j k) zero) (W j k)⟩ :
      Interval (Mat 𝕋 n n)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
