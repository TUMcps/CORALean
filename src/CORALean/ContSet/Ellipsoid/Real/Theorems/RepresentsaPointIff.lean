import CORALean.ContSet.Ellipsoid.Real.Operations.RepresentsaPoint
import CORALean.ContSet.Ellipsoid.Real.Theorems.CentreMemConstruct

/-!
# An ellipsoid is a point iff its generator matrix vanishes

Each column `Gⱼ` is the image of the unit vector `eⱼ`, which has `‖eⱼ‖₂ = 1`, so `q + Gⱼ` lies in
the ellipsoid and, if that is `{q}`, `Gⱼ = 0`; conversely `G = 0` leaves only `q`. The origin is the
point at `q = 0`. The empty set is never represented: `Ellipsoid.centre_mem_construct`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.representsa_point_iff (E : Ellipsoid n) :
    E.construct = {E.q} ↔ E.representsa_point := by -- --- PROOF ---
  constructor
  · -- a column of `G` is the image of a unit vector, which is in the ball
    intro h
    ext i j
    have hu : ‖(Pi.single j 1 : Vec ℝ E.k)‖₂ ≤ 1 := by
      unfold norm₂
      rw [Real.sqrt_le_one]
      simp [Pi.single_apply]
    have hmem : E.q + E.G *ᵥ Pi.single j 1 ∈ E.construct := ⟨_, hu, rfl⟩
    rw [h] at hmem
    have h0 : E.G *ᵥ (Pi.single j 1 : Vec ℝ E.k) = 0 := add_eq_left.mp hmem
    have := congrFun h0 i
    simpa [Matrix.mulVec_single_one] using this
  · intro h
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      simp [Ellipsoid.representsa_point] at h
      simp [h]
    · rintro rfl
      exact Ellipsoid.centre_mem_construct E

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
