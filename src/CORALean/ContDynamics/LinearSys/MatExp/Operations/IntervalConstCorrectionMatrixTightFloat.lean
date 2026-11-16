module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowTightFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `MatExp.intervalConstCorrectionMatrixTight`, CORA's `G` over a float box, at CORA's coefficient

`Real.MatExp.constCorrectionMatrixEntrywise` over a float box, the `G` of [1]: orders `1` through
`η` from `intervalConstCorrTermTight`, as `intervalConstCorrectionMatrix` has them, and the tail in
`r` times the entry's own bound `W`. The coefficient is `corrCoeffLowTight`, CORA's to within
rounding, where `intervalCorrectionMatrixEntrywise` and its constant counterpart take
`corrCoeffLow`.

## Inputs
* `A` – float interval matrix
* `r` – float step length
* `η` – Taylor order
* `W` – float bound on the entrywise remainder

## Output
* float interval matrix of the integrated correction over the box

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

/-- `corrCoeff (i+2) · r^{i+2}/(i+2)! · A^{i+1}` over the whole box `A`, for a nonnegative
`r`. -/
@[step_of MatExp.intervalConstCorrectionMatrixTight]
def MatExp.step_intervalConstCorrTermTight (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (i : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let c := MatExp.taylorCoeffBounds r (i + 2)                          -- r^{i+2}/(i+2)! ≤ c.sup
  let cLo := mulDown (MatExp.corrCoeffLowTight (i + 2)) c.sup                 -- κ r^{i+2}/(i+2)!
  (Interval.smul cLo zero (Interval.matPow A (i + 1))).materialiseMat  -- [cLo, 0] A^{i+1}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `G` of CORA over a whole box: `Σᵢ [min(Tᵢ, 0), max(Tᵢ, 0)] ⊕ [-rW, rW]`, orders `1`
through `η`, for a nonnegative `r`. -/
def MatExp.intervalConstCorrectionMatrixTight (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (η : ℕ)
    (W : Mat 𝕋 n n) : Interval (Mat 𝕋 n n) :=
  let T : Vector (Interval (Mat 𝕋 n n)) η :=                                         -- T₁ … T_η
    Vector.ofFn fun i => MatExp.step_intervalConstCorrTermTight A r i
  (⟨fun j k => subDown (sumDown fun i : Fin η => minimum (T[i].inf j k) zero) (mulUp r (W j k)),
    fun j k => addUp (sumUp fun i : Fin η => maximum (T[i].sup j k) zero) (mulUp r (W j k))⟩ :
      Interval (Mat 𝕋 n n)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
