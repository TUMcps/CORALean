module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrTermFloat

@[expose] public section

/-!
# `MatExp.intervalCorrectionMatrixEntrywise`, CORA's `F` over a float box

`Real.MatExp.correctionMatrixEntrywise` over a float box, the `F` of [1]: orders `2` through `η`
from `intervalCorrTerm`, as `intervalCorrectionMatrix` has them, and the tail in the entry's own
bound `W` of `expRemainderEntrywise` where `intervalCorrectionMatrix` takes one scalar bound.

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

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of CORA over a whole box: `Σᵢ [min(Tᵢ, 0), max(Tᵢ, 0)] ⊕ [-W, W]`, orders `2`
through `η`, for a nonnegative `r`. -/
def MatExp.intervalCorrectionMatrixEntrywise (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (η : ℕ)
    (W : Mat 𝕋 n n) : Interval (Mat 𝕋 n n) :=
  let T : Vector (Interval (Mat 𝕋 n n)) (η - 1) :=                                  -- T₂ … T_η
    Vector.ofFn fun i => MatExp.intervalCorrTerm A r (i + 2)
  (⟨fun j k => subDown (sumDown fun i : Fin (η - 1) => minimum (T[i].inf j k) zero) (W j k),
    fun j k => addUp (sumUp fun i : Fin (η - 1) => maximum (T[i].sup j k) zero) (W j k)⟩ :
      Interval (Mat 𝕋 n n)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
