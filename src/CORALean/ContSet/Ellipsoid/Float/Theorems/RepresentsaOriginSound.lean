module

public import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaOrigin
public import CORALean.ContSet.Ellipsoid.Real.Theorems.RepresentsaOriginIff
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaOriginSound

@[expose] public section

/-!
# `Ellipsoid.representsa_origin` is sound

A `true` answer makes `G` and `q` `0`, so the nominal part is `{0}`, and the error box is `{0}`: the
ellipsoid is `{0}`.
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

theorem Ellipsoid.representsa_origin_sound {E : Ellipsoid 𝕋 n}
    (h : E.representsa_origin = true) : E.construct = {0} := by -- --- PROOF ---
  simp only [Ellipsoid.representsa_origin, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hG, hq⟩, hE⟩ := h
  -- every stored entry of `G` and `q` is squeezed to `0`
  have hG0 : ∀ i j, toReal (E.G i j) = 0 := fun i j => le_antisymm
    (by simpa [toReal_zero] using toReal_le_of_le (hG j i).1)
    (by simpa [toReal_zero] using toReal_le_of_le (hG j i).2)
  have hq0 : toRealVec E.q = 0 := funext fun i => le_antisymm
    (by simpa [toRealVec, toReal_zero] using toReal_le_of_le (hq i).1)
    (by simpa [toRealVec, toReal_zero] using toReal_le_of_le (hq i).2)
  have hN : InflatedContSet.nominalSet E = {0} :=
    (Real.Ellipsoid.representsa_origin_iff (InflatedContSet.nominal E)).2
      ⟨hq0, Matrix.ext fun i j => hG0 i j⟩
  show InflatedContSet.nominalSet E + E.I_error.construct = _
  rw [hN, Interval.representsa_origin_sound hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
