module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.CoshExact

@[expose] public section

/-!
# `Interval.cosh` contains the image under `cosh`

`coshUp p a` holds only for `|toReal a| ≤ 2 ^ p / 2` (the range of `expUp`, at `a` and `-a`):
the theorem takes `sup ≤ 2 ^ p / 2` and `-inf ≤ 2 ^ p / 2` on the box, which covers every
argument `coshHi` uses.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.cosh_outer (p : ℕ) (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, toReal (I.sup i) ≤ 2 ^ p / 2 ∧ -toReal (I.inf i) ≤ 2 ^ p / 2) :
    (fun x i => Real.cosh (x i)) '' I.construct ⊆ (I.cosh p).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  obtain ⟨h1, h2⟩ := hI i
  have hB : (0:ℝ) ≤ 2 ^ p / 2 := by positivity
  show toReal (Interval.coshLo p (I.inf i) (I.sup i)) ≤ Real.cosh (x i) ∧
    Real.cosh (x i) ≤ toReal (Interval.coshHi p (I.inf i) (I.sup i))
  -- the lower bound: `cosh` is least at the corner nearest `0`, and `1` at a box containing `0`
  constructor
  · unfold Interval.coshLo
    split_ifs with ha hb
    · have := toReal_le_of_le ha
      rw [toReal_zero] at this
      refine le_trans (coshDown_le p _) (Real.cosh_le_cosh.2 ?_)
      rw [abs_of_nonpos this, abs_of_nonpos (by linarith)]; linarith
    · have := toReal_le_of_le hb
      rw [toReal_zero] at this
      refine le_trans (coshDown_le p _) (Real.cosh_le_cosh.2 ?_)
      rw [abs_of_nonneg this, abs_of_nonneg (by linarith)]; linarith
    · rw [toReal_one]; exact Real.one_le_cosh _
  -- the upper bound: `cosh` is largest at the corner farthest from `0`
  · unfold Interval.coshHi
    split_ifs with ha hb
    · have := toReal_le_of_le ha
      rw [toReal_zero] at this
      refine le_trans (Real.cosh_le_cosh.2 ?_) (coshUp_ge p _ (by linarith) (by linarith))
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    · have := toReal_le_of_le hb
      rw [toReal_zero] at this
      refine le_trans (Real.cosh_le_cosh.2 ?_) (coshUp_ge p _ h1 (by linarith))
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    · -- a box that may contain `0`: the larger magnitude bounds `|x|`
      have hm : toReal (maximum (neg (I.inf i)) (I.sup i)) =
          max (-toReal (I.inf i)) (toReal (I.sup i)) := by
        rw [toReal_maximum, toReal_neg]
      have hl := le_max_left (-toReal (I.inf i)) (toReal (I.sup i))
      have hr := le_max_right (-toReal (I.inf i)) (toReal (I.sup i))
      refine le_trans (Real.cosh_le_cosh.2 ?_)
        (coshUp_ge p _ (by rw [hm]; exact max_le h2 h1) (by rw [hm]; linarith))
      rw [hm]
      exact (abs_le.2 ⟨by linarith, by linarith⟩).trans (le_abs_self _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
