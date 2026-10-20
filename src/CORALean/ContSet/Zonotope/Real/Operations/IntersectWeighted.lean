module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `Zonotope.intersectWeighted`

The zonotope that [1, Lemma 3] gives for the intersection of `d` zonotopes `Zᵢ = ⟨cᵢ, Gᵢ⟩`: the
weighted mean `(Σ wᵢ)⁻¹ Σ wᵢ cᵢ` of the centers and the weighted generators
`(Σ wᵢ)⁻¹ [w₁ G₁, …, w_d G_d]` side by side. The generator counts need not agree, so the
generators are indexed by the sigma type of the `d` families, `finSigmaFinEquiv` order. The weights
are arguments; the lemma only asks that they do not sum to zero.

## Inputs
* `w` – weights
* `Zs` – zonotopes

## Output
* zonotope enclosing the weighted intersection

## References

* [1] A. Alanwar, V. Gaßmann, X. He, H. Said, H. Sandberg, K. H. Johansson and M. Althoff.
      "Privacy-Preserving Set-Based Estimation Using Partially Homomorphic Encryption".
      European Journal of Control, 2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Lemma 3]: `Z₁ ∩ ⋯ ∩ Z_d` is enclosed by this zonotope whenever `Σ wᵢ ≠ 0`. -/
noncomputable def Zonotope.intersectWeighted (w : Fin d → ℝ) (Zs : Fin d → Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) where
  h := ∑ i, (Zs i).h
  c := (∑ i, w i)⁻¹ • ∑ i, w i • (Zs i).c                        -- eq. 27
  G := fun q => (∑ i, w i)⁻¹ •                                    -- eq. 28
    (w (finSigmaFinEquiv.symm q).1 • (Zs (finSigmaFinEquiv.symm q).1).G
      (finSigmaFinEquiv.symm q).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
