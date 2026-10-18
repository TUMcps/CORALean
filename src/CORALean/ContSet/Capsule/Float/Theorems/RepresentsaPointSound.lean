module

public import CORALean.ContSet.Capsule.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Capsule.Real.Theorems.RepresentsaPointIff
public import CORALean.ContSet.Capsule.Float.Theorems.ConstructEqNominal
public import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointParts

@[expose] public section

/-!
# `Capsule.representsa_point` is sound

`true` makes the error box the origin, so the set is the nominal capsule's, and the nominal
generator and radius `0`, so by the exact layer's `representsa_point_iff` (for `0 < n`) the capsule
is the single point, its stored center.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.representsa_point_sound (hn : 0 < n) {C : Capsule 𝕋 n}
    (h : Capsule.representsa_point C = true) : C.construct = {toRealVec C.c} := by
  obtain ⟨hI, hp⟩ := Capsule.representsa_point_parts h
  rw [Capsule.construct_eq_nominal hI]
  exact (CORALean.Real.Capsule.representsa_point_iff hn C.nominal).mpr hp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
