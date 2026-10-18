module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.AtanhExact

@[expose] public section

/-!
# `Interval.atanh` contains the image under `artanh`

On the domain `(-1, 1)`, as CORA's (it returns a complex result outside). The hypotheses are the
domain, stated through the rounded quantities `atanhUp` and `atanhDown` divide by: the upper
corner has `1 - sup` provably positive in `subDown`, the lower one has `1 + inf` provably positive
(`subDown one (neg inf)`), and for a nonnegative lower corner the ratio `(1 + inf)/(1 - inf)`
sits in `logDown`'s range `2 ^ p / 2`.
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

theorem Interval.atanh_outer (p k : ℕ) (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, 0 < toReal (subDown one (I.sup i)) ∧ 0 < toReal (subDown one (neg (I.inf i))) ∧
      (0 ≤ toReal (I.inf i) →
        (1 + toReal (I.inf i)) / (1 - toReal (I.inf i)) ≤ 2 ^ p / 2)) : -- --- STMT ---
    (fun x i => Real.artanh (x i)) '' I.construct ⊆ (I.atanh p k).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  obtain ⟨h1, h2, h3⟩ := hI i
  have hs := subDown_le_sub (one : 𝕋) (I.sup i)
  have hn := subDown_le_sub (one : 𝕋) (neg (I.inf i))
  rw [toReal_one] at hs hn
  rw [toReal_neg] at hn
  have hsup : toReal (I.sup i) < 1 := by linarith
  have hinf : -1 < toReal (I.inf i) := by linarith
  refine ⟨le_trans (atanhDown_le p k _ (by linarith) h2 h3)
      (Real.artanh_le_artanh hinf (by linarith) hx'.1),
    le_trans (Real.artanh_le_artanh (by linarith) hsup hx'.2) (le_atanhUp p k _ (by linarith) h1)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
