import CORALean.ContSet.Interval.Float.Operations.Tanh
import CORALean.ContSet.Interval.Real.Theorems.TanhExact

/-!
# `Interval.tanh` contains the image under `tanh`

`tanhUp p a` holds only for `toReal a ≤ 2 ^ p / 2` (the range of `expUp`): the theorem takes
that bound on every upper bound of the box as a hypothesis. `tanhDown` has none.
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

theorem Interval.tanh_outer (p : ℕ) (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, toReal (I.sup i) ≤ 2 ^ p / 2) :
    (fun x i => Real.tanh (x i)) '' I.construct ⊆ (I.tanh p).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ i
  -- the real layer's exact image holds `tanh x` between the tanh of the two corners
  have hmem : (fun j => Real.tanh (x j)) ∈ I.nominal.tanh.construct := by
    rw [Real.Interval.tanh_exact]
    exact ⟨x, hx, rfl⟩
  have h : Real.tanh (toReal (I.inf i)) ≤ Real.tanh (x i) ∧
      Real.tanh (x i) ≤ Real.tanh (toReal (I.sup i)) := hmem i
  exact ⟨le_trans (tanhDown_le p _) h.1, le_trans h.2 (tanhUp_ge p _ (hI i))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
