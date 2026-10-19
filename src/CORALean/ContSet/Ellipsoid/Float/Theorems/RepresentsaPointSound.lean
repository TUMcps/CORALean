module

public import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Ellipsoid.Real.Theorems.RepresentsaPointIff
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaPointSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic

@[expose] public section

/-!
# `Ellipsoid.representsa_point` is sound

A `true` answer makes `Q = 0`, so the nominal part is the single point `q`, and the error box is a
point: the ellipsoid is their sum, a point.

## Inputs
* `E` – ellipsoid

## Hypotheses
* `h` – `representsa_point` returns `true`

## Conclusion
* `E` is a single point
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
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
  -- every stored entry of `Q` is squeezed to `0`, and so is the nominal shape
  have hQ0 : toRealMat E.Q = 0 := funext fun i => funext fun j => le_antisymm
    (by simpa [toRealMat, toReal_zero] using toReal_le_of_le (hG i j).1)
    (by simpa [toRealMat, toReal_zero] using toReal_le_of_le (hG i j).2)
  have hN0 : (InflatedContSet.nominal E).ellipsoid.Q = 0 := by
    rw [Ellipsoid.nominal_Q_eq, hQ0]
    split_ifs <;> rfl
  obtain ⟨v, hv⟩ := Interval.representsa_point_sound hE
  refine ⟨toRealVec E.q + v, ?_⟩
  have hN : InflatedContSet.nominalSet E = {toRealVec E.q} := by
    rw [← E.nominal_q]
    exact (Real.Ellipsoid.representsa_point_iff (InflatedContSet.nominal E).ellipsoid).2 hN0
  show InflatedContSet.nominalSet E + E.I_error.construct = _
  rw [hN, hv, Set.singleton_add_singleton]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
