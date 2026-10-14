module

public import CORALean.ContSet.Taylm.Float.Operations.Sinh
public import CORALean.ContSet.Taylm.Float.Theorems.HyperbolicOuter

@[expose] public section

/-!
# `Taylm.sinh` encloses `sinh ∘ f`

`Taylm.hyperbolic_outer` at the parity that starts with `sinh`. `hp` is `expUp`'s range
hypothesis at the magnitude of the model, as `Taylm.exp_outer` keeps it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sinh_outer (p : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hp : toReal (maximum (absolute T.constCoef) (maximum (absolute T.bounds.inf)
      (absolute T.bounds.sup))) ≤ 2 ^ p / 2) :
    (T.sinh p).Encloses fun t => Real.sinh (f t) := by
  have := Taylm.hyperbolic_outer p true h hp
  simp only [if_true] at this
  exact this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
