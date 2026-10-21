module

public import CORALean.ContSet.ConZonotope.Real.Operations.Constrain
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# A constrained zonotope is the shadow of a constrained hypercube

[1, Def. 3]'s second form: `Z|_{C≤d} = c ⊕ G (B_q ∩ ⟨C, d⟩_H)`, the image of the unit box cut by
the constraints under the affine map `β ↦ c + G β`, the "shadow" of the paper's Fig. 1b.

## Inputs
* `Z` – zonotope
* `C` – constraint matrix on the factors
* `d` – constraint offset

## Hypotheses
* none

## Conclusion
* `Z|_{C≤d}` is the image of `B_q ∩ ⟨C, d⟩_H` under `β ↦ c + G β`

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for
      Neural Network Verification". ICLR, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 3]: `Z|_{C≤d} = c ⊕ G (B_q ∩ ⟨C, d⟩_H)`. -/
theorem Zonotope.constrain_construct_eq_image (Z : Zonotope α) (C : Mat ℝ p Z.h) (d : Vec ℝ p) :
    (Z.constrain C d).construct = (fun β : Fin Z.h → ℝ => Z.c + ∑ j, β j • Z.G j) ''
      ({β | ∀ j, |β j| ≤ 1} ∩ (HPolytope.ineqs C d).construct) := by
  ext x
  exact ⟨fun ⟨β, hβ, hP, hx⟩ => ⟨β, ⟨hβ, hP⟩, hx.symm⟩,
    fun ⟨β, ⟨hβ, hP⟩, hx⟩ => ⟨β, hβ, hP, hx.symm⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
