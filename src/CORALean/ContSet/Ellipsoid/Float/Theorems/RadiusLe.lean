module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Radius
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AddSubMemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NormUbLe

@[expose] public section

/-!
# The float `Ellipsoid.radius` bounds the distance to the center

`x - q`, for `x` in the ellipsoid, is in the ellipsoid moved to the origin (the same shape, the
same error, `add_sub_mem_nominalSet`), whose points `norm₂_le_normUb` bounds. An upper bound only.
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

theorem Ellipsoid.radius_le (p : ℕ) (E : Ellipsoid 𝕋 n) {x : Vec ℝ n} (hx : x ∈ E.construct) :
    ‖x - toRealVec E.q‖₂ ≤ toReal (E.radius p) := by -- --- PROOF ---
  obtain ⟨y, hy, e, he, rfl⟩ := hx
  -- the same point of the ellipsoid moved to the origin
  have hy' := Ellipsoid.add_sub_mem_nominalSet (E := { E with q := fun _ => zero })
    (F := (nominal E).ellipsoid) (Ellipsoid.nominal_dominated E) hy
  refine Ellipsoid.norm₂_le_normUb p { E with q := fun _ => zero } ⟨_, hy', e, he, ?_⟩
  funext i
  rw [E.nominal_q]
  simp only [Pi.add_apply, Pi.sub_apply, toRealVec, toReal_zero]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
