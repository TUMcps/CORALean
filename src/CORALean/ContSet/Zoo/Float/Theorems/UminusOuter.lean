import CORALean.ContSet.Zoo.Float.Operations.Uminus
import CORALean.ContSet.Taylm.Float.Theorems.UminusOuter
import CORALean.ContSet.Interval.Float.Theorems.UminusExact

/-!
# `Zoo.uminus` encloses

The Taylor model by `Taylm.uminus_outer`, the interval by `Interval.uminus_exact` (negation is
exact in floats).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.uminus_outer {Z : Zoo 𝕋 n} {f : Vec ℝ n → ℝ} (h : Z.Encloses f) :
    Z.uminus.Encloses fun t => -f t := by -- --- PROOF ---
  refine ⟨fun T hT => ?_, fun I hI t ht => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hT
    exact Taylm.uminus_outer (h.1 a ha)
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hI
    exact (Interval.uminus_exact a) ▸ Set.neg_mem_neg.2 (h.2 a ha t ht)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
