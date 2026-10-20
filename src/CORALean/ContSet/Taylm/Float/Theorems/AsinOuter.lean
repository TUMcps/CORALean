module

public import CORALean.ContSet.Taylm.Float.Operations.Asin
public import CORALean.ContSet.Taylm.Float.Theorems.TaylorOuter
public import CORALean.ContSet.Taylm.Float.Theorems.AbsLeMagUp
public import CORALean.ContSet.Taylm.Float.Theorems.ArcsinCoefMem
public import CORALean.ContSet.Taylm.Float.Theorems.ArcsinBoundGe

@[expose] public section

/-!
# `Taylm.asin` encloses `arcsin ∘ f`

`Taylm.taylor_outer` at `arcsin`: the zeroth coefficient between `asinDown` and `asinUp`, the
others `Taylm.arcsinCoef_mem`, the derivative bound `Taylm.arcsinBound_ge`. The hypotheses are the
rounded root `√(1 - c²)` positive at the center and `√(1 - m²)` at the magnitude `Taylm.magUp`,
which put the range inside `(-1, 1)`.

## Inputs
* `p` – precision of the arcsine
* `q` – precision of the square root
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function
* `hc` – the root at the center is positive
* `hm` – the root at the magnitude is positive

## Conclusion
* the result encloses arcsin of the function
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.asin_outer (p q : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hc : 0 < toReal (sqrtDown q (subDown one (mulUp T.constCoef T.constCoef))))
    (hm : 0 < toReal (sqrtDown q (subDown one (mulUp T.magUp T.magUp)))) :
    (T.asin p q).Encloses fun t => Real.arcsin (f t) := by -- --- PROOF ---
  have hM1 : toReal T.magUp < 1 := by
    have := (invSqrtOneSub_mem q T.magUp hm).1
    have h0 : 0 ≤ toReal T.magUp := by
      rw [Taylm.magUp, toReal_maximum, toReal_absolute]
      exact le_trans (abs_nonneg _) (le_max_left _ _)
    nlinarith
  refine Taylm.taylor_outer h Real.arcsin T.constCoef _ _ _ _ (fun k _ => ?_)
    (fun ξ hξ => ?_) (fun ξ hξ => Taylm.arcsinBound_ge q T.magUp hm _ (T.abs_le_magUp hξ))
    le_rfl
  · rcases k with _ | j
    · exact ⟨by simpa using asinDown_le p q T.constCoef, by simpa using le_asinUp p q T.constCoef⟩
    · exact Taylm.arcsinCoef_mem q T.constCoef hc j
  · have := abs_lt.1 (lt_of_le_of_lt (T.abs_le_magUp hξ) hM1)
    exact Real.contDiffAt_arcsin (by linarith [this.1]) (by linarith [this.2])

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
