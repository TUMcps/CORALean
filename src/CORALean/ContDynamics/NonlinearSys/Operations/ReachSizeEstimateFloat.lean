import CORALean.ContDynamics.NonlinearSys.Operations.InterpGainFloat
import CORALean.Global.Float.Log
import CORALean.Global.Float.ToRat
import CORALean.Global.Float.PowUp

/-!
# Eq. (57): the estimated size after a finite horizon, in floats

`reachSizeEstimate` in `𝕋`. The real exponents of eq. (53) go through `exp (y log x)` at the
precisions `prec` (the squarings of `expUp`) and `bis` (the bisection steps of `logUp`); `⌊λ⌋` is
read off `ToRat`. Tuning only: the value picks a step size, an order or a gain and no soundness
statement reads it, so every rounding is upward and no theorem is owed. What a run guarantees
holds for whatever this returns. See [1].

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Eq. (57): the size `R(t)` is estimated to reach after the finite horizon,
walked in `λ = ζ_δ^{-λ'}` steps. -/
def reachSizeEstimateFloat [SoundFloatArithmetic 𝕋] [ToRat 𝕋] (prec bis : ℕ)
    (ζδ ζZ ζA φ1 r₀ rabs : 𝕋) (scalings : ℕ) : 𝕋 :=
  let rpow := fun (x y : 𝕋) => expUp prec (mulUp y (logUp prec bis x))  -- x ^ y for x > 0
  let lam := powUp (divUp one ζδ) scalings                       -- λ = ζ_δ^{-λ'}
  let N := ⌊ToRat.toRat lam⌋₊                                    -- ⌊λ⌋ whole steps
  let b := subUp lam (nsmulUp N one)                             -- the last incomplete step
  let base := addUp one (addUp ζZ ζZ)                            -- 1 + 2 ζ_Z
  let ζAZ := addUp (sumUp fun (j : Fin N) =>                     -- 53. ζ_{A,Z}(λ)
      let e := addUp b (nsmulUp (j + 1) one)                     -- b + j, j = 1, …, N
      mulUp (rpow base e) (rpow ζA (divUp (subUp e one) lam)))
    (mulUp b (rpow base b))
  let growth := mulUp (mulUp r₀ (rpow base lam)) ζA              -- 57. the start set, propagated
  let gain := (List.range scalings).foldl                        -- 57. ∏ φ(j+1)
    (fun p j => mulUp p (interpGainFloat ζδ φ1 j)) one
  addUp growth (mulUp (mulUp (divUp rabs lam) ζAZ) gain)         -- 57. errors, accumulated

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
