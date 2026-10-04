import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaOrigin
import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage

/-!
# A constrained zonotope is the origin iff it is a point and the point is `0`
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.representsa_origin_iff (cZ : ConZonotope α) :
    cZ.construct = {0} ↔ cZ.representsa_origin := by -- --- PROOF ---
  rw [ConZonotope.construct_eq_image]
  constructor
  · -- the origin is the image of some coefficient vector, and every other agrees with it
    intro hp
    have hmem : (0 : α) ∈
        (fun β : Vec ℝ cZ.h => cZ.c + ∑ j, β j • cZ.G j) '' cZ.domain.construct := by
      rw [hp]; rfl
    obtain ⟨β₀, hβ₀, h0⟩ := hmem
    refine ⟨β₀, hβ₀, h0, fun β hβ => ?_⟩
    have : cZ.c + ∑ j, β j • cZ.G j ∈
        (fun β : Vec ℝ cZ.h => cZ.c + ∑ j, β j • cZ.G j) '' cZ.domain.construct := ⟨β, hβ, rfl⟩
    rw [hp] at this
    exact add_left_cancel (this.trans h0.symm)
  · -- the image of the polytope is the one point `β₀` reaches, and it is `0`
    rintro ⟨β₀, hβ₀, h0, h⟩
    ext x
    constructor
    · rintro ⟨β, hβ, rfl⟩
      show cZ.c + ∑ j, β j • cZ.G j = _
      rw [← h0, h β hβ]
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨β₀, hβ₀, h0.trans hx.symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
