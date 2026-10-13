module

public import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT
public import CORALean.ContSet.Interval.Float.Instances

@[expose] public section

/-!
# What a float run is told about the discrete-time field

`NonlinearSysDT` stores `f` over ℝ, which no float run can evaluate. A `FloatModel` is what it
evaluates instead: an interval extension of `f` over a box of states and a box of inputs, as a
computable function at the scalar `𝕋`. `Encloses` ties it to `f`, beside the structure rather than
inside it, so the real system stays what it was.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- An interval extension of `f`. -/
structure NonlinearSysDT.FloatModel (𝕋 : Type) (n m : ℕ) where
  f : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 n)

/-- `fm` encloses `sys`: its value over a box contains `f` at every point of the boxes. -/
structure NonlinearSysDT.FloatModel.Encloses (fm : NonlinearSysDT.FloatModel 𝕋 n m)
    (sys : NonlinearSysDT n m) : Prop where
  f_mem (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ construct X, ∀ u ∈ construct U, sys.f x u ∈ construct (fm.f X U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
