module

public import CORALean.ContSet.ConZonotope.Real.Operations.StripMat
public import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
public import CORALean.ContSet.HPolytope.Real.Operations.Intersection
public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.Global.Block

@[expose] public section

/-!
# `ConZonotope.intersectStrip`

CORA's `@conZonotope/intersectStrip` [1, Lemma 2] with a numeric
gain, `aux_conZonotopeFromLambda`: the intersection of a constrained zonotope with the strip
`{x | |C x - y| ≤ φ}` of `s` parallel slabs, in CG-Rep, the gain form being Alamo et al.'s for
zonotopes. The strip enters as `s` new factors `ν` and `s` equality rows
`C G ξ - φ ν = y - C c`; the center moves to `c + Λ (y - C c)`, the generators become
`[(I - Λ C) G, φ₁ Λ₁, …, φₛ Λₛ]`, and the old constraints keep acting on the old factors.

The gain `Λ` is an argument and any `Λ` works. CORA's `'normGen'`, `'alamo-FRad'` and
`'wang-FRad'` are closed forms for one choice of `Λ` (a matrix inverse), and `'svd'`, `'radius'`
and `'bravo'` are optimiser or search driven; none of them is part of this operation.

## References

* [1] A. Alanwar, V. Gaßmann, X. He, H. Said, H. Sandberg, K. H. Johansson and M. Althoff.
      "Privacy-Preserving Set-Based Estimation Using Partially Homomorphic Encryption".
      European Journal of Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n s : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_conZonotopeFromLambda`: `cZ ∩ {x | |C x - y| ≤ φ}` for the gain `Λ`. -/
def ConZonotope.intersectStrip (cZ : ConZonotope (Vec ℝ n)) (C : Mat ℝ s n) (φ y : Vec ℝ s)
    (Λ : Mat ℝ n s) : ConZonotope (Vec ℝ n) where
  h := cZ.h + s
  c := cZ.c + Λ *ᵥ (y - C *ᵥ cZ.c)
  G := Fin.append (fun j => (1 - Λ * C) *ᵥ cZ.G j) fun i => φ i • fun k => Λ k i
  P := (cZ.P.comap (blockLeft cZ.h s)).intersection
        (HPolytope.eqs (cZ.stripMat C φ) (y - C *ᵥ cZ.c))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
