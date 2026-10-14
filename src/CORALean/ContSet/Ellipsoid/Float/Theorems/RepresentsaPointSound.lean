module

public import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Ellipsoid.Real.Theorems.RepresentsaPointIff
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaPointSound

@[expose] public section

/-!
# `Ellipsoid.representsa_point` is sound

A `true` answer makes `G = 0`, so the nominal part is the single point `q`, and the error box is a
point: the ellipsoid is their sum, a point.
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

theorem Ellipsoid.representsa_point_sound {E : Ellipsoid 𝕋 n}
    (h : E.representsa_point = true) : ∃ v, E.construct = {v} := by -- --- PROOF ---
  simp only [Ellipsoid.representsa_point, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨hG, hE⟩ := h
  -- every stored entry of `G` is squeezed to `0`
  have hG0 : ∀ i j, toReal (E.G i j) = 0 := fun i j => le_antisymm
    (by simpa [toReal_zero] using toReal_le_of_le (hG j i).1)
    (by simpa [toReal_zero] using toReal_le_of_le (hG j i).2)
  obtain ⟨v, hv⟩ := Interval.representsa_point_sound hE
  refine ⟨toRealVec E.q + v, ?_⟩
  have hN : InflatedContSet.nominalSet E = {toRealVec E.q} :=
    (Real.Ellipsoid.representsa_point_iff (InflatedContSet.nominal E)).2
      (Matrix.ext fun i j => hG0 i j)
  show InflatedContSet.nominalSet E + E.I_error.construct = _
  rw [hN, hv, Set.singleton_add_singleton]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
