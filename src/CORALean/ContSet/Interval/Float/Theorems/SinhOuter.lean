module

public import CORALean.ContSet.Interval.Float.Operations.Sinh
public import CORALean.ContSet.Interval.Real.Theorems.SinhExact

@[expose] public section

/-!
# `Interval.sinh` contains the image under `sinh`

`sinhUp p a` holds only for `toReal a ≤ 2 ^ p / 2` and `sinhDown p a` only for
`-toReal a ≤ 2 ^ p / 2` (the range of `expUp`, at `a` and at `-a`): the theorem takes both as a
hypothesis on the box.
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

theorem Interval.sinh_outer (p : ℕ) (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, toReal (I.sup i) ≤ 2 ^ p / 2 ∧ -toReal (I.inf i) ≤ 2 ^ p / 2) :
    (fun x i => Real.sinh (x i)) '' I.construct ⊆ (I.sinh p).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  exact ⟨le_trans (sinhDown_le p _ (hI i).2) (Real.sinh_le_sinh.2 hx'.1),
    le_trans (Real.sinh_le_sinh.2 hx'.2) (sinhUp_ge p _ (hI i).1)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
