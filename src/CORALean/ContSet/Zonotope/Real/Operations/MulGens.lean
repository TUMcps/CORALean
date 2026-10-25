module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.mulGens`

The reduced generator matrix `Ĝ = G T` of [1, Eq. (1)]: generator `ĝⱼ = Σᵢ T(i,j) gᵢ`, with
`T ∈ ℝ^{ν×ν̂}`, `ν̂` generators, and the center unchanged ([1, Sec. II-D]).

## Inputs
* `Z` – zonotope
* `r` – new generator count
* `T` – recombination matrix

## Output
* zonotope with generators recombined by `T`

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the Order Reduction
      of Zonotopes". IEEE Control Systems Letters, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⟨c, G T⟩`: the generators of `Z` recombined by the columns of `T`. -/
def Zonotope.mulGens (Z : Zonotope α) {r : ℕ} (T : Mat ℝ Z.h r) : Zonotope α :=
  ⟨r, Z.c, fun j => ∑ i, T i j • Z.G i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
