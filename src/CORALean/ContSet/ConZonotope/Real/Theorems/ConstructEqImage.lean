module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain
public import CORALean.ContSet.ConZonotope.Real.Theorems.MemDomainIff

@[expose] public section

/-!
# A constrained zonotope is a polytope's affine image

The zonotope's own map applied to `domain` rather than to a box. Every guarantee
about the representation is one of the two halves of this: convexity and
compactness come from the polytope through the map, and the operations state
their enclosures as inclusions between the images.

## Inputs
* `cZ` – constrained zonotope

## Hypotheses
* none

## Conclusion
* the set is the affine image of its coefficient polytope
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.construct_eq_image (cZ : ConZonotope α) : -- --- CONCL ---
    cZ.construct
      = (fun β : Vec ℝ cZ.h => cZ.c + ∑ j, β j • cZ.G j) ''
        cZ.domain.construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨β, hβ, hP, rfl⟩
    exact ⟨β, ConZonotope.mem_domain_iff.mpr ⟨hβ, hP⟩, rfl⟩
  -- back, the box and the constraint read off the domain again
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨hbox, hP⟩ := ConZonotope.mem_domain_iff.mp hβ
    exact ⟨β, hbox, hP, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
