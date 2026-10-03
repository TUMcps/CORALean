import CORALean.ContSet.Zonotope.Float.Operations.RepresentsaOrigin
import CORALean.ContSet.Zonotope.Real.Theorems.RepresentsaOriginIff
import CORALean.ContSet.Interval.Float.Theorems.RepresentsaOriginSound

/-!
# `Zonotope.representsa_origin` is sound

A `true` answer makes every generator and the centre `0`, so the nominal part is `{0}`, and the
error box is `{0}`: the zonotope is `{0}`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.representsa_origin_sound {Z : Zonotope 𝕋 n}
    (h : Z.representsa_origin = true) : Z.construct = {0} := by -- --- PROOF ---
  simp only [Zonotope.representsa_origin, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hG, hc⟩, hE⟩ := h
  -- every stored generator entry and centre entry is squeezed to `0`
  have hG0 : ∀ i j, toReal (Z.G i j) = 0 := fun i j => le_antisymm
    (by simpa [toReal_zero] using toReal_le_of_le (hG j i).1)
    (by simpa [toReal_zero] using toReal_le_of_le (hG j i).2)
  have hc0 : toRealVec Z.c = 0 := funext fun i => le_antisymm
    (by simpa [toRealVec, toReal_zero] using toReal_le_of_le (hc i).1)
    (by simpa [toRealVec, toReal_zero] using toReal_le_of_le (hc i).2)
  have hN : InflatedContSet.nominalSet Z = {0} :=
    (Real.Zonotope.representsa_origin_iff (InflatedContSet.nominal Z)).2
      ⟨hc0, fun j => funext fun i => hG0 i j⟩
  show InflatedContSet.nominalSet Z + Z.E.construct = _
  rw [hN, Interval.representsa_origin_sound hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
