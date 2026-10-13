import CORALean.ContSet.Zonotope.Float.Operations.CompactZeros
import CORALean.ContSet.Zonotope.Real.Theorems.FilterGenConstruct

/-!
# Float `compact_(Z, 'zeros')` changes no point

The nominal zonotope of the result is the exact layer's `filterGen` of the nominal zonotope with
the same predicate, and every column that predicate drops is certified zero, so it is the zero
vector as reals. The error box is copied. Exact, `=`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.compactZeros_exact (Z : Zonotope (Vec 𝕋 n)) :
    Z.compactZeros.construct = Z.construct := by -- --- PROOF ---
  have hz : ∀ j, Z.keepColumn j = false → (nominal Z).G j = 0 := by
    intro j hj
    funext i
    simp only [Zonotope.keepColumn, Bool.not_eq_false', List.all_eq_true, List.mem_finRange,
      Bool.and_eq_true, forall_const] at hj
    have := hj i
    have h₁ := toReal_le_of_le this.1
    have h₂ := toReal_le_of_le this.2
    rw [toReal_zero] at h₁ h₂
    exact le_antisymm h₁ h₂
  have hN : nominal Z.compactZeros = (nominal Z).filterGen Z.keepColumn := rfl
  have hE : error Z.compactZeros = error Z := rfl
  show ContSet.construct (nominal Z.compactZeros) + (error Z.compactZeros).construct =
    ContSet.construct (nominal Z) + (error Z).construct
  rw [hN, hE]
  congr 1
  exact CORALean.Real.Zonotope.filterGen_construct _ _ hz

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
