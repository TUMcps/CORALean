module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Radius
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NormUbLe

@[expose] public section

/-!
# The float `Ellipsoid.radius` bounds the distance to the center

`x - c`, for `x` in the ellipsoid, is in the ellipsoid moved to the origin (the same `u`, the
same error), whose points `norm₂_le_normUb` bounds. An upper bound only.
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

theorem Ellipsoid.radius_le (p : ℕ) (E : Ellipsoid 𝕋 n) {x : Vec ℝ n} (hx : x ∈ E.construct) :
    ‖x - toRealVec E.c‖₂ ≤ toReal (E.radius p) := by -- --- PROOF ---
  obtain ⟨y, hy, e, he, rfl⟩ := hx
  obtain ⟨u, hu, hyu⟩ := Ellipsoid.mem_nominalSet_iff.mp hy
  -- the same point of the ellipsoid moved to the origin
  refine Ellipsoid.norm₂_le_normUb p { E with c := fun _ => zero } ⟨fun i =>
    toReal (zero : 𝕋) + ∑ j, toReal (E.G i j) * u j,
    Ellipsoid.mem_nominalSet_iff.mpr ⟨u, hu, fun _ => rfl⟩, e, he, ?_⟩
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, hyu i, toRealVec, toReal_zero]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
