import CORALean.ContSet.Zonotope.Real.Operations.GenMap
import CORALean.Global.CoeffNorm

/-!
# The zonotope norm

`[1, Def. 4]`: `‖p‖_Z = ν(p) = min {‖γ‖∞ | G γ = p}` (the paper's Eq. 6), the
generator map's `coeffNorm` at the supremum norm of the coefficients. CORA's
`zonotopeNorm(Z, p)`, which also ignores the centre: a point is measured from `c` as
`‖p - c‖_Z`. It is a norm for a non-degenerate `Z` (`zonotopeNorm_isNorm`); off the range of
the generators, where the paper leaves it undefined and CORA returns `Inf`, it reads `0`.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `‖p‖_Z`, `[1, Def. 4]`. -/
noncomputable def Zonotope.zonotopeNorm (Z : Zonotope α) (p : α) : ℝ := coeffNorm Z.genMap p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
