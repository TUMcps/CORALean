module

public import CORALean.ContSet.Taylm.Float.Operations.Acos
public import CORALean.ContSet.Taylm.Float.Theorems.TaylorOuter
public import CORALean.ContSet.Taylm.Float.Theorems.AbsLeMagUp
public import CORALean.ContSet.Taylm.Float.Theorems.ArcsinCoefMem
public import CORALean.ContSet.Taylm.Float.Theorems.ArcsinBoundGe
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# `Taylm.acos` encloses `arccos ∘ f`

`Taylm.taylor_outer` at `arccos`: the zeroth coefficient between `acosDown` and `acosUp`, the others
the negations of `Taylm.arcsinCoef_mem` (`arccos⁽ᵏ⁾ = -arcsin⁽ᵏ⁾`, `aux_iteratedDeriv_arccos_succ`),
the derivative bound `Taylm.arcsinBound_ge`, the same in magnitude. The hypotheses are the rounded
root `√(1 - c²)` positive at the center and `√(1 - m²)` at the magnitude `Taylm.magUp`, which put
the range inside `(-1, 1)`.

## Inputs
* `p` – precision of the arccosine
* `q` – precision of the square root
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function
* `hc` – the root at the center is positive
* `hm` – the root at the magnitude is positive

## Conclusion
* the result encloses arccos of the function
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Derivatives of `arccos` are those of `arcsin`, negated. -/
private theorem _root_.CORALean.aux_iteratedDeriv_arccos_succ (j : ℕ) :
    iteratedDeriv (j + 1) Real.arccos = -iteratedDeriv (j + 1) Real.arcsin := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ', Real.deriv_arccos, Real.deriv_arcsin]
  funext x
  simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.acos_outer (p q : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hc : 0 < toReal (sqrtDown q (subDown one (mulUp T.constCoef T.constCoef))))
    (hm : 0 < toReal (sqrtDown q (subDown one (mulUp T.magUp T.magUp)))) : -- --- CONCL ---
    (T.acos p q).Encloses fun t => Real.arccos (f t) := by -- --- PROOF ---
  have hM1 : toReal T.magUp < 1 := by
    have := (invSqrtOneSub_mem q T.magUp hm).1
    have h0 : 0 ≤ toReal T.magUp := by
      rw [Taylm.magUp, toReal_maximum, toReal_absolute]
      exact le_trans (abs_nonneg _) (le_max_left _ _)
    nlinarith
  refine Taylm.taylor_outer h Real.arccos T.constCoef _ _ _ _ (fun k _ => ?_)
    (fun ξ hξ => ?_) (fun ξ hξ => ?_) le_rfl
  · rcases k with _ | j
    · exact ⟨by simpa using acosDown_le p q T.constCoef, by simpa using le_acosUp p q T.constCoef⟩
    · have hk := Taylm.arcsinCoef_mem q T.constCoef hc j
      rw [aux_iteratedDeriv_arccos_succ, Pi.neg_apply, neg_div, toReal_neg, toReal_neg]
      exact ⟨neg_le_neg hk.2, neg_le_neg hk.1⟩
  · have := abs_lt.1 (lt_of_le_of_lt (T.abs_le_magUp hξ) hM1)
    exact Real.contDiffAt_arccos (by linarith [this.1]) (by linarith [this.2])
  · rw [aux_iteratedDeriv_arccos_succ, Pi.neg_apply, abs_neg]
    exact Taylm.arcsinBound_ge q T.magUp hm _ (T.abs_le_magUp hξ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
