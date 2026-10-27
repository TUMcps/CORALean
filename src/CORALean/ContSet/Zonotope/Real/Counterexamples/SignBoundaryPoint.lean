module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Sign.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The printed falsification candidate lies on the far side of the unsafe set

[1, Eq. 9] as printed: `β̃ = sign(A(i,·) G_y)` and `ỹ = c_y + G_y β̃`, offered as a boundary point
of the intersection of `Y` and the unsafe set `U = {y | A y ≤ b}`. The sign maximizes `A(i,·) y`
over `Y`, the vertex farthest from the halfspace: for `Y = ⟨0, [1]⟩_Z = [-1, 1]` and
`U = {y ≤ 0}`, `Y ∩ U = [-1, 0]` is nonempty and `ỹ = 1 ∉ U`. CORA's `'zonotack'` takes
`-sign`, `Zonotope.zonotackFactors`, whose vertex is the least (`Zonotope.zonotackFactors_isLeast`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed vertex lies outside the unsafe set though `Y` meets it

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations,
      2026.](../../../../../../references/2026/koller-iclr-latent-space.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 9] as printed gives a vertex outside the unsafe set although `Y` meets it. -/
theorem Zonotope.signBoundaryPoint_counterexample : -- --- CONCL ---
    ∃ (Y : Zonotope (Vec ℝ 1)) (A : Mat ℝ 1 1) (b : Vec ℝ 1),
      (Y.construct ∩ (HPolytope.ineqs A b).construct).Nonempty ∧
      Y.c + ∑ j, (SignType.sign (A 0 ⬝ᵥ Y.G j) : ℝ) • Y.G j ∉
        Y.construct ∩ (HPolytope.ineqs A b).construct := by -- --- PROOF ---
  refine ⟨⟨1, 0, fun _ _ => 1⟩, fun _ _ => 1, fun _ => 0, ⟨0, ⟨0, fun _ => by simp, ?_⟩,
    (HPolytope.mem_ineqs_iff).2 fun _ => by simp [mulVec]⟩, ?_⟩
  · funext
    simp
  · -- `ỹ = c_y + sign(1) · 1 = 1`, and `1 ≤ 0` fails
    rintro ⟨-, hU⟩
    have h := (HPolytope.mem_ineqs_iff).1 hU 0
    simp [mulVec, dotProduct] at h
    norm_num at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
