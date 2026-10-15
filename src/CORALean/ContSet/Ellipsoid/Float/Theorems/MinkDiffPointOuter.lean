module

public import CORALean.ContSet.Ellipsoid.Float.Operations.MinkDiffPoint
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AddSubMemNominalSet

@[expose] public section

/-!
# `Ellipsoid.minkDiffPoint` encloses the translate

A point `y + e` of the ellipsoid moved by `-s` is `(q' + (y - q)) + (e + r)`, with `q'` the stored
center and `r` its rounding; `y - q` about `q'` is a point of the result's nominal part, the shape
matrix being the same (`add_sub_mem_nominalSet`), and `r` which `centerResidual` holds. Outer: the
error box grows by the rounding, so the result can be larger than the translate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.minkDiffPoint_outer (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n) :
    (fun x => x - toRealVec s) '' E.construct ⊆ (E.minkDiffPoint s).construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨y, hy, e, he, rfl⟩, rfl⟩
  -- the center's rounding, which the residual box holds
  let r : Vec ℝ n := fun i => toReal (E.q i) + toReal ((-s) i)
    - toReal (addDown (E.q i) ((-s) i))
  have hr : r ∈ (Ellipsoid.centerResidual E.q (-s)).construct :=
    Interval.sub_mem_residual fun _ => ⟨addDown_le_add _ _, add_le_addUp _ _⟩
  -- the same offset from the center, at the stored one
  have hy' := Ellipsoid.add_sub_mem_nominalSet (E := E.minkDiffPoint s)
    (F := (nominal E).ellipsoid) (Ellipsoid.nominal_dominated E) hy
  refine ⟨_, hy', e + r, Interval.plus_outer _ _ ⟨e, he, r, hr, rfl⟩, ?_⟩
  funext i
  rw [Ellipsoid.nominal_q]
  simp only [Pi.add_apply, Pi.sub_apply, r, toRealVec, Ellipsoid.minkDiffPoint]
  rw [show toReal ((-s) i) = -toReal (s i) from toReal_neg (s i)]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
