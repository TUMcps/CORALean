module

public import CORALean.ContSet.Ellipsoid.Float.Operations.MinkDiffPoint
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual

@[expose] public section

/-!
# `Ellipsoid.minkDiffPoint` encloses the translate

A point `y + e` of the ellipsoid, `y = q + G u`, moved by `-s` is `(q' + G u) + (e + r)`, with
`q'` the stored centre and `r` its rounding, which `centerResidual` holds. Outer: the error box
grows by the rounding, so the result can be larger than the translate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.minkDiffPoint_outer (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n) :
    (fun x => x - toRealVec s) '' E.construct ⊆ (E.minkDiffPoint s).construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨y, hy, e, he, rfl⟩, rfl⟩
  obtain ⟨u, hu, hyu⟩ := Ellipsoid.mem_nominalSet_iff.mp hy
  -- the centre's rounding, which the residual box holds
  let r : Vec ℝ n := fun i => toReal (E.q i) + toReal (neg (s i))
    - toReal (addDown (E.q i) (neg (s i)))
  have hr : r ∈ (Ellipsoid.centerResidual E.q fun i => neg (s i)).construct :=
    Interval.sub_mem_residual fun _ => ⟨addDown_le_add _ _, add_le_addUp _ _⟩
  -- the same `u` at the stored centre, and the two boxes summed
  refine ⟨fun i => toReal (addDown (E.q i) (neg (s i))) + ∑ j, toReal (E.G i j) * u j,
    Ellipsoid.mem_nominalSet_iff.mpr ⟨u, hu, fun _ => rfl⟩, e + r,
    Interval.plus_outer _ _ ⟨e, he, r, hr, rfl⟩, ?_⟩
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, hyu i, r, toRealVec, toReal_neg]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
