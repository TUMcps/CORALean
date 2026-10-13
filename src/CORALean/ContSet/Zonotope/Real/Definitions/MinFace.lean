module

public import CORALean.ContSet.Zonotope.Real.Definitions.Degree

@[expose] public section

/-!
# The face of a point

[1, Sec. 3 (degree)]: "the face `F`, for which the minimum is attained, is denoted `F(x)`": an
exposed face of `Z` containing `x` whose dimension is `deg(x)` (`Zonotope.degree`). Stated as the
property of being such a face; that it is unique for a polytope (the faces through `x` are closed
under intersection) [1] takes for granted, and nothing here uses it.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3 (degree)]: `F = F(x)`, a face of `Z` through `x` of dimension `deg(x)`. -/
def Zonotope.IsMinFace (Z : Set (Vec ℝ n)) (x : Vec ℝ n) (F : Set (Vec ℝ n)) : Prop :=
  IsExposed ℝ Z F ∧ x ∈ F ∧ Module.finrank ℝ (vectorSpan ℝ F) = Zonotope.degree Z x

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
