import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContSet.Interval.Real.Instances

/-!
# What a constant input contributes at every time of one step, as a set

The constant half of [1, Alg. 3]'s split `U = ũ ⊕ Ũ`: over `[0, r]` the
constant `ũ` contributes `∫₀ᵗ e^{Aσ}dσ ũ`, enclosed as the straight line to its
value at `r`, `(t/r) ∫₀ʳ e^{Aσ}dσ ũ`, widened by the interpolation error
`F̃ ũ` [1, Prop. 3.4]. The segment from the origin to `ũ` carries the line, so
no matrix inverse and no subtraction appear — the arrangement
`inputSolution_timeInterval_outer_split` proves inline, named here so a window
other than the first can reuse it.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the constant `ũ` contributes at any time of `[0, r]`:
`∫₀ʳ e^{Aσ}dσ · [0, ũ] ⊕ F̃ ũ`, at Taylor order `η`. -/
noncomputable def LinearSys.constInputSolution (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (uc : Vec ℝ n) : S n :=
  let seg : S n := LinComb.linComb (OfPoint.ofPoint 0) (OfPoint.ofPoint uc)  -- [0, ũ]
  let Γr := MatExp.expIntegral (toRealMat sys.A) r                  -- ∫₀ʳ e^{Aσ} dσ
  let Fc := MatExp.constCorrectionMatrix (toRealMat sys.A) r η      -- F̃
  let line := Mtimes.mtimes Γr seg                                  -- (t/r) ∫₀ʳ e^{Aσ} dσ ũ
  let err := Mtimes.mtimes (𝕄 := ℐ) Fc (OfPoint.ofPoint uc)        -- F̃ ũ
  Plus.plus line err                                                -- the line ⊕ F̃ ũ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
