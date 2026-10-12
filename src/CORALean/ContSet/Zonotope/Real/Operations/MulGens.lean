import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.mulGens`

The reduced generator matrix `Ĝ = G T` of [1, Eq. (1)]: generator `ĝⱼ = Σᵢ T(i,j) gᵢ`, with
`T ∈ ℝ^{ν×ν̂}`, `ν̂` generators, and the centre unchanged ([1, Sec. II-D]).

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⟨c, G T⟩`: the generators of `Z` recombined by the columns of `T`. -/
def Zonotope.mulGens (Z : Zonotope α) {r : ℕ} (T : Mat ℝ Z.h r) : Zonotope α :=
  ⟨r, Z.c, fun j => ∑ i, T i j • Z.G i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
