module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Real.Sign

@[expose] public section

/-!
# The exposed face of a zonotope in a direction

For `Z = c + ∑ βⱼgⱼ, |βⱼ| ≤ 1` and a functional `u`, the face `{x ∈ Z | u x = max_Z u}` is the
zonotope with center `c + ∑ sign(u gⱼ)gⱼ` and the generators `u` annihilates, `construct_face`.
The generators are kept at their indices, those with `u gⱼ ≠ 0` replaced by `0`, so a face's
generator `j` is `Z`'s generator `j` and the face is the zonotope of the subset
`{gⱼ | u gⱼ = 0}`, as [1, Sec. 3 (faces)] states. `noncomputable` as the real layer is: it decides
`u gⱼ = 0` over ℝ.

## Inputs
* `Z` – zonotope
* `u` – linear functional

## Output
* face of `Z` maximizing `u`

## References

* [1] [M. Černý. "Goffin's algorithm for zonotopes". Kybernetika,
      2012.](../../../../../../references/2012/cerny-kybernetika-goffin-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3 (faces)]: the face of `Z` maximizing `u`, the zonotope of the generators `u`
annihilates about `c + ∑ sign(u gⱼ)gⱼ`. -/
noncomputable def Zonotope.face (Z : Zonotope α) (u : α →ₗ[ℝ] ℝ) : Zonotope α where
  h := Z.h
  c := Z.c + ∑ j, Real.sign (u (Z.G j)) • Z.G j
  G := fun j => if u (Z.G j) = 0 then Z.G j else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
