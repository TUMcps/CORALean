module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.intervalOfFactorBounds`

[1, Eq. 13], corrected: the bounds `[β̲, β̄]` of a constrained hypercube mapped by `β ↦ c + G β`,
`c ⊕ [G⁺ β̲ + G⁻ β̄, G⁺ β̄ + G⁻ β̲]` with `G⁺ = ½(G + |G|)` and `G⁻ = ½(G - |G|)`, the entries
`≤ 0` as in [1, Prop. 3]'s proof. [1] prints `c ⊕ [G⁺ β̲ - G⁻ β̄, G⁺ β̄ - G⁻ β̲]`, which is
right only for `G⁻ = ½(|G| - G)`, the reading `A⁻ ∈ ℝ_{≥0}` of its notation, under which
[1, Prop. 3] fails instead. CORA's `aux_boundConZonotope` in `conZonotope/approximateBoundsWithGPU`
writes the same box by center and radius, `c + G β_c ± |G| β_r`.

## Inputs
* `Z` – zonotope
* `B` – bounds `[β̲, β̄]` of its factors

## Output
* the interval `c ⊕ [G⁺ β̲ + G⁻ β̄, G⁺ β̄ + G⁻ β̲]`

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

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 13], corrected: `c ⊕ [G⁺ β̲ + G⁻ β̄, G⁺ β̄ + G⁻ β̲]`. -/
noncomputable def Zonotope.intervalOfFactorBounds (Z : Zonotope (Vec ℝ n))
    (B : Interval (Vec ℝ Z.h)) : Interval (Vec ℝ n) :=
  -- 1. `G⁺ = ½(G + |G|)` and `G⁻ = ½(G - |G|)`, `G(i,j)` the `i`-th entry of generator `j`
  let Gplus : Mat ℝ n Z.h := fun i j => (Z.G j i + |Z.G j i|) / 2
  let Gminus : Mat ℝ n Z.h := fun i j => (Z.G j i - |Z.G j i|) / 2
  -- 2. `c ⊕ [G⁺ β̲ + G⁻ β̄, G⁺ β̄ + G⁻ β̲]`
  ⟨Z.c + Gplus *ᵥ B.inf + Gminus *ᵥ B.sup, Z.c + Gplus *ᵥ B.sup + Gminus *ᵥ B.inf⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
