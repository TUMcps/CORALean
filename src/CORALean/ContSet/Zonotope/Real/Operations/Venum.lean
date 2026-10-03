import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm
import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope

/-!
# `Zonotope.venum`

`[1, Alg. 1]` (vertex enumeration), CORA's `contains_(Z, S, 'exact:venum')`: `Z₁ ⊆ Z₂`
iff no vertex of `Z₁` has `‖v - c₂‖_{Z₂} > 1`. `vertices(Z₁)` is read as the `2^{m₁}` sign
corners, a superset of the vertices with the same convex hull, which changes nothing the
algorithm decides. Exponential in `m₁`, as the paper says; `[1, Thm. 2]` is why nothing
much better is expected.

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

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[1, Alg. 1]`: `true` iff every corner of `Z₁` has `‖v - c₂‖_{Z₂} ≤ 1`. -/
noncomputable def Zonotope.venum (Z₁ Z₂ : Zonotope (Vec ℝ n)) : Bool :=
  let V := Finset.univ.image Z₁.corner
  if ∀ v ∈ V, ¬ Z₂.zonotopeNorm (v - Z₂.c) > 1 then true else false

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
