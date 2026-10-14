module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `Zonotope.enclosePolytopes`

[1, Prop. 12]: one zonotope enclosing `μ` polytopes, `Z_encl = Λ box(Λ⁻¹P₁, ..., Λ⁻¹P_μ)`,
the box computed as the proposition lists it: (1) the vertices of every `Λ⁻¹P_l`, (2) their
least and greatest value in each dimension, (3) that interval in generator representation,
`Interval.zonotope`. The polytopes enter by their vertices, `V l` those of `P_l`, the
proposition's step (1) needing them and nothing else. `Λ` is the caller's; [1, Sec. 6.2]'s
flow-aligned choice is `ZonoBundle.dirFlow`.

`Λ⁻¹` is Mathlib's, zero at a singular `Λ`, where the result encloses nothing: the
proposition asks full rank, and so does `enclosePolytopes_outer`.

Real only for now: the float layer would round the inverse, the vertices and the product
apart, each into an error box, and no caller asks for it yet.

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

open Matrix

variable {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 12]: the zonotope `Λ box(Λ⁻¹P₁, ..., Λ⁻¹P_μ)` enclosing the polytopes whose
vertices are `V l`, `l` ranging over the `μ` polytopes. -/
noncomputable def Zonotope.enclosePolytopes (Λ : Mat ℝ n n) (V : ι → κ → Vec ℝ n) :
    Zonotope (Vec ℝ n) :=
  let V' : ι × κ → Vec ℝ n := fun v => Λ⁻¹ *ᵥ V v.1 v.2   -- (1) the vertices of every `Λ⁻¹P_l`
  let box : Interval (Vec ℝ n) := Interval.enclosePoints V'  -- (2) `[m̲, m̄]`, dimension-wise
  let Z : Zonotope (Vec ℝ n) := box.zonotope                 -- (3) its generator representation
  Zonotope.mtimes Λ Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
