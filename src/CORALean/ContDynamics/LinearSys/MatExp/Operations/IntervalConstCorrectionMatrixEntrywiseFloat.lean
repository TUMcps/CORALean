module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrTermFloat

@[expose] public section

/-!
# `MatExp.intervalConstCorrectionMatrixEntrywise`, CORA's `G` over a float box

`Real.MatExp.constCorrectionMatrixEntrywise` over a float box, the `G` of [1]: orders `1` through
`η` from `intervalConstCorrTerm`, as `intervalConstCorrectionMatrix` has them, and the tail in `r`
times the entry's own bound `W` of `expRemainderEntrywise`.

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

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `G` of CORA over a whole box: `Σᵢ [min(Tᵢ, 0), max(Tᵢ, 0)] ⊕ [-rW, rW]`, orders `1`
through `η`, for a nonnegative `r`. -/
def MatExp.intervalConstCorrectionMatrixEntrywise (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (η : ℕ)
    (W : Mat 𝕋 n n) : Interval (Mat 𝕋 n n) :=
  let T : Vector (Interval (Mat 𝕋 n n)) η :=                                         -- T₁ … T_η
    Vector.ofFn fun i => MatExp.intervalConstCorrTerm A r i
  (⟨fun j k => subDown (sumDown fun i : Fin η => minimum (T[i].inf j k) zero) (mulUp r (W j k)),
    fun j k => addUp (sumUp fun i : Fin η => maximum (T[i].sup j k) zero) (mulUp r (W j k))⟩ :
      Interval (Mat 𝕋 n n)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
