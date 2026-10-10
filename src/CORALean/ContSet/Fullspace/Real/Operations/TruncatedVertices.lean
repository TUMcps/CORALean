import CORALean.ContSet.Fullspace.Real.Operations.Vertices
import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# `Fullspace.truncatedVertices`

The vertices of the full space (`Fullspace.vertices`, points at infinity) cut off at radius `t`:
each `⊤` entry becomes `t` and each `⊥` entry `-t`, which are the corners of the box
`[-t, t]^n`, as a vertex polytope. They are the real points the infinite vertices are the limit
of as `t → ∞`.

Source: [1].

## References

* [1] `contSet/@fullspace/vertices_.m`, CORA (Sep. 2025).
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The vertex polytope on `Fullspace.vertices` with `⊤` replaced by `t` and `⊥` by `-t`. -/
noncomputable def Fullspace.truncatedVertices (F : Fullspace (n + 1)) (t : ℝ) :
    VPolytope (Vec ℝ (n + 1)) where
  k := 2 ^ (n + 1)
  V := fun l j => if F.vertices l j = ⊤ then t else -t

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
