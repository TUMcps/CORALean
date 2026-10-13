import CORALean.HybridDynamics.Definitions.NonlinearReset
import CORALean.ContSet.Interval.Float.Instances

/-!
# What a float run is told about a nonlinear reset

`NonlinearReset` stores `f` over ℝ, which no float run can evaluate. A `FloatModel` is what it
evaluates instead: an interval extension of `f` over a box of pre-jump states and a box of
inputs, as a computable function at the scalar `𝕋`. `Encloses` ties it to `f`, beside the
structure rather than inside it, so the real reset stays what it was.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m p : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- An interval extension of the reset. -/
structure NonlinearReset.FloatModel (𝕋 : Type) (n m p : ℕ) where
  f : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 p)

/-- `fm` encloses `r`: its value over two boxes contains `f` at every point of them. -/
structure NonlinearReset.FloatModel.Encloses (fm : NonlinearReset.FloatModel 𝕋 n m p)
    (r : NonlinearReset n m p) : Prop where
  f_mem (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ construct X, ∀ u ∈ construct U, r.f x u ∈ construct (fm.f X U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
