module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `Zonotope.parallelotope`

[1, Prop. 8]: the parallelotope `Ψ = Γ box(Γ⁻¹Z)` enclosing a zonotope, its edges along the
columns of `Γ`. One `let` per step of the sketched proof: the coordinates changed by `Γ⁻¹`, the
box there (`Zonotope.interval` read back as a zonotope), and the coordinates changed back. The
proposition takes `Γ`'s columns from `Z`'s own generators and asks full rank;
`parallelotope_outer` needs the rank alone, so any invertible `Γ` will do, the choice being a
matter of tightness, `Zonotope.methodC`'s. At a singular `Γ`, Mathlib's `Γ⁻¹` is zero and the
result encloses nothing. Real only for now: the float layer would round the inverse and both
products apart.

## Inputs
* `Γ` – basis matrix
* `Z` – zonotope

## Output
* parallelotope `Γ box(Γ⁻¹Z)` enclosing `Z`

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 8]: `Ψ = Γ box(Γ⁻¹Z)`. -/
noncomputable def Zonotope.parallelotope (Γ : Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) :=
  let Z' := Zonotope.mtimes Γ⁻¹ Z            -- `Γ⁻¹Z`, in the coordinates `Γ` names
  let box := Z'.interval.zonotope             -- `box(Γ⁻¹Z)`, as a zonotope
  Zonotope.mtimes Γ box

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
