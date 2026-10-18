module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Origin
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# `ConPolyZono.origin` is exactly the origin

`zero` reads as `0`, and with no generators and no constraint rows the nominal part is that one
point; the error box is the origin box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.origin_exact (n : ℕ) :
    (ConPolyZono.origin n : ConPolyZono 𝕋 (Vec 𝕋 n)).construct = {0} := by -- --- PROOF ---
  -- the nominal part has no generators and no rows: its one point is the stored `zero`
  have hN : InflatedContSet.nominalSet (ConPolyZono.origin n : ConPolyZono 𝕋 (Vec 𝕋 n)) = {0} := by
    ext x
    rw [ConPolyZono.mem_nominalSet_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, β, -, -, -, hx⟩
      funext i
      rw [hx i]
      simp [ConPolyZono.origin, toReal_zero]
    · rintro rfl
      exact ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun j => j.elim0, fun i => i.elim0,
        fun i => by simp [ConPolyZono.origin, toReal_zero]⟩
  have hE : (ConPolyZono.origin n : ConPolyZono 𝕋 (Vec 𝕋 n)).I_error.construct = {0} :=
    Interval.origin_exact n
  -- the sum of the two singletons
  show InflatedContSet.nominalSet (ConPolyZono.origin n : ConPolyZono 𝕋 (Vec 𝕋 n))
      + (ConPolyZono.origin n : ConPolyZono 𝕋 (Vec 𝕋 n)).I_error.construct = _
  rw [hN, hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
