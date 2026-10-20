module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic

@[expose] public section

/-!
# An ellipsoid is a point iff its shape matrix vanishes

Each column `Gⱼ` of `G = Q^(1/2)` is the image of the unit vector `eⱼ`, which has `‖eⱼ‖₂ = 1`, so
`q + Gⱼ` lies in the ellipsoid and, if that is `{q}`, `Gⱼ = 0`; conversely `G = 0` leaves only
`q`; and `G = 0` iff `Q = 0` (`G_eq_zero_iff`). The origin is the
point at `q = 0`. The empty set is never represented: `Ellipsoid.center_mem_construct`.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* `E` is its center iff `representsa_point` holds
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.representsa_point_iff (E : Ellipsoid n) : -- --- CONCL ---
    E.construct = {E.q} ↔ E.representsa_point := by -- --- PROOF ---
  constructor
  · -- a column of `G` is the image of a unit vector, which is in the ball
    intro h
    show E.Q = 0
    rw [← E.G_eq_zero_iff]
    ext i j
    have hu : ‖(Pi.single j 1 : Vec ℝ n)‖₂ ≤ 1 := by
      unfold norm₂
      rw [Real.sqrt_le_one]
      simp [Pi.single_apply]
    have hmem : E.q + E.G *ᵥ Pi.single j 1 ∈ E.construct :=
      Ellipsoid.mem_construct hu
    rw [h] at hmem
    have h0 : E.G *ᵥ (Pi.single j 1 : Vec ℝ n) = 0 := add_eq_left.mp hmem
    have := congrFun h0 i
    simpa [Matrix.mulVec_single_one] using this
  · -- the zero square root leaves only the center
    intro h
    ext x
    constructor
    · rw [E.construct_eq_sqrt]
      rintro ⟨u, -, rfl⟩
      have hG : E.G = 0 := E.G_eq_zero_iff.2 h
      simp [hG]
    · rintro rfl
      exact Ellipsoid.center_mem_construct E

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
