module

public import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaOrigin
public import CORALean.ContSet.Ellipsoid.Real.Theorems.RepresentsaOriginIff
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaOriginSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic

@[expose] public section

/-!
# `Ellipsoid.representsa_origin` is sound

A `true` answer makes `Q` and `q` `0`, so the nominal part is `{0}`, and the error box is `{0}`: the
ellipsoid is `{0}`.

## Inputs
* `E` – ellipsoid

## Hypotheses
* `h` – `representsa_origin` returns `true`

## Conclusion
* `E` is the origin
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

theorem Ellipsoid.representsa_origin_sound {E : Ellipsoid 𝕋 n}
    (h : E.representsa_origin = true) : E.construct = {0} := by -- --- PROOF ---
  simp only [Ellipsoid.representsa_origin, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hG, hq⟩, hE⟩ := h
  -- every stored entry of `Q` and `q` is squeezed to `0`, and so is the nominal shape
  have hQ0 : toRealMat E.Q = 0 := funext fun i => funext fun j => le_antisymm
    (by simpa [toRealMat, toReal_zero] using toReal_le_of_le (hG i j).1)
    (by simpa [toRealMat, toReal_zero] using toReal_le_of_le (hG i j).2)
  have hN0 : (InflatedContSet.nominal E).ellipsoid.Q = 0 := by
    rw [Ellipsoid.nominal_Q_eq, hQ0]
    split_ifs <;> rfl
  have hq0 : toRealVec E.q = 0 := funext fun i => le_antisymm
    (by simpa [toRealVec, toReal_zero] using toReal_le_of_le (hq i).1)
    (by simpa [toRealVec, toReal_zero] using toReal_le_of_le (hq i).2)
  have hN : InflatedContSet.nominalSet E = {0} :=
    (Real.Ellipsoid.representsa_origin_iff (InflatedContSet.nominal E).ellipsoid).2
      ⟨by rw [E.nominal_q, hq0], hN0⟩
  show InflatedContSet.nominalSet E + E.I_error.construct = _
  rw [hN, Interval.representsa_origin_sound hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
