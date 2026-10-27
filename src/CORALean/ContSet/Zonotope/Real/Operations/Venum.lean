module

public import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# `Zonotope.venum`

`[1, Alg. 1]` (vertex enumeration), CORA's `contains_(Z, S, 'exact:venum')`: `Z₁ ⊆ Z₂`
iff no vertex of `Z₁` has `‖v - c₂‖_{Z₂} > 1`. `vertices(Z₁)` is read as the `2^{m₁}` sign
corners, a superset of the vertices with the same convex hull, which changes nothing the
algorithm decides. Exponential in `m₁`, as the paper says; `[1, Thm. 2]` is why nothing
much better is expected.

## Inputs
* `Z₁` – zonotope tested
* `Z₂` – containing zonotope

## Output
* `true` iff every corner is inside `Z₂`

## References

* [1] [A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment Problem".
      European Journal of Control,
      2021.](../../../../../../references/2021/kulmburg-ejc-zonotope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[1, Alg. 1]`: `true` iff every corner of `Z₁` has `‖v - c₂‖_{Z₂} ≤ 1`. -/
noncomputable def Zonotope.venum (Z₁ Z₂ : Zonotope (Vec ℝ n)) : Bool :=
  -- 1. `V ← vertices(Z₁)`, read as the sign corners
  let V := Finset.univ.image Z₁.corner
  -- 2. for `v ∈ V`, return False if `‖v - c₂‖_{Z₂} > 1`; 3. return True
  if ∀ v ∈ V, ¬ Z₂.zonotopeNorm (v - Z₂.c) > 1 then true else false

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
