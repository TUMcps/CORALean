module

public import CORALean.ContSet.Zonotope.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.RepresentsaPointIff
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaPointSound

@[expose] public section

/-!
# `Zonotope.representsa_point` is sound

A `true` answer makes every generator `0`, so the nominal part is the single point `c`, and the
error box is a point: the zonotope is their sum, a point.
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

theorem Zonotope.representsa_point_sound {Z : Zonotope (Vec 𝕋 n)}
    (h : Z.representsa_point = true) : ∃ v, Z.construct = {v} := by -- --- PROOF ---
  simp only [Zonotope.representsa_point, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨hG, hE⟩ := h
  -- every stored generator entry is squeezed to `0`
  have hG0 : ∀ i j, toReal (Z.G j i) = 0 := fun i j => le_antisymm
    (by simpa [toReal_zero] using toReal_le_of_le (hG j i).1)
    (by simpa [toReal_zero] using toReal_le_of_le (hG j i).2)
  obtain ⟨v, hv⟩ := Interval.representsa_point_sound hE
  refine ⟨toRealVec Z.c + v, ?_⟩
  have hN : InflatedContSet.nominalSet Z = {toRealVec Z.c} :=
    (Real.Zonotope.representsa_point_iff (InflatedContSet.nominal Z)).2
      fun j => funext fun i => hG0 i j
  show InflatedContSet.nominalSet Z + Z.I_error.construct = _
  rw [hN, hv, Set.singleton_add_singleton]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
