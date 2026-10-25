module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# Reordering the generators does not change the zonotope

`c + ∑ βⱼ gⱼ` is a sum over the generators, so permuting them is permuting the coefficients.
It is what lets [1, Alg. 3] sort the generators by angle (line 9) without changing the zonogon.

## Inputs
* `Z` – zonotope
* `π` – generator permutation

## Hypotheses
* none

## Conclusion
* permuting the generators leaves the set unchanged

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems Reachability
      Analysis". Hybrid Systems: Computation and Control, 2008.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.construct_comp_perm (Z : Zonotope α) (π : Equiv.Perm (Fin Z.h)) : -- --- CONCL ---
    (⟨Z.h, Z.c, Z.G ∘ π⟩ : Zonotope α).construct = Z.construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨fun j => β (π.symm j), fun j => hβ _, ?_⟩
    show Z.c + ∑ j, β j • Z.G (π j) = _
    have e := Equiv.sum_comp π (fun i => β (π.symm i) • Z.G i)
    simp only [Equiv.symm_apply_apply] at e
    rw [e]
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨fun j => β (π j), fun j => hβ _, ?_⟩
    show _ = Z.c + ∑ j, β (π j) • Z.G (π j)
    rw [Equiv.sum_comp π (fun j => β j • Z.G j)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
