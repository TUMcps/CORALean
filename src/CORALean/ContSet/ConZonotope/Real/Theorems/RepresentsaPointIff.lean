module

public import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage

@[expose] public section

/-!
# A constrained zonotope is a point iff `G` is constant on the coefficient polytope

The set is the image `ξ ↦ c + G ξ` of `ConZonotope.domain` (`construct_eq_image`), so it is a single
point exactly when that image is one: the polytope is nonempty and `G ξ` takes one value on it.
The point need not be the center `c`: with `c = 0`, `G = [1 0]`, `A = [1 1]`, `b = 2` the set is
`{1}`.

## Inputs
* `cZ` – constrained zonotope

## Hypotheses
* none

## Conclusion
* the set is a single point iff it represents a point
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.representsa_point_iff (cZ : ConZonotope α) :
    (∃ p, cZ.construct = {p}) ↔ cZ.representsa_point := by -- --- PROOF ---
  rw [ConZonotope.construct_eq_image]
  constructor
  · -- the point is the image of some coefficient vector, and every other agrees with it
    rintro ⟨p, hp⟩
    have hmem : p ∈ (fun β : Vec ℝ cZ.h => cZ.c + ∑ j, β j • cZ.G j) '' cZ.domain.construct := by
      rw [hp]; rfl
    obtain ⟨β₀, hβ₀, hpβ⟩ := hmem
    refine ⟨β₀, hβ₀, fun β hβ => ?_⟩
    have : cZ.c + ∑ j, β j • cZ.G j ∈
        (fun β : Vec ℝ cZ.h => cZ.c + ∑ j, β j • cZ.G j) '' cZ.domain.construct := ⟨β, hβ, rfl⟩
    rw [hp] at this
    have h2 : cZ.c + ∑ j, β j • cZ.G j = cZ.c + ∑ j, β₀ j • cZ.G j := this.trans hpβ.symm
    exact add_left_cancel h2
  · -- the image of the polytope is the one point `β₀` reaches
    rintro ⟨β₀, hβ₀, h⟩
    refine ⟨cZ.c + ∑ j, β₀ j • cZ.G j, ?_⟩
    ext x
    constructor
    · rintro ⟨β, hβ, rfl⟩
      show cZ.c + ∑ j, β j • cZ.G j = _
      rw [h β hβ]
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨β₀, hβ₀, hx.symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
