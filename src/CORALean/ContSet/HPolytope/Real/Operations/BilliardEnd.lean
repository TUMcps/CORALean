module

public import CORALean.ContSet.HPolytope.Real.Operations.FacetNormal
public import CORALean.ContSet.HPolytope.Real.Operations.ChordHighIndex
public import CORALean.Global.BilliardReflect

@[expose] public section

/-!
# `HPolytope.billiardEnd`

`[1, Alg., steps 3-4]`: from `x` with direction `d`, follow the billiard trajectory of length `ℓ`,
reflecting `d → d - 2 (d, s) s` at each boundary, and return its end. Each segment runs to the
first hyperplane, `t̄` of `[1, Eq. 1]`; when `ℓ` is no longer than that the trajectory ends on it.
`none` is step 4's "go to step 2": the trajectory met a point on more than one hyperplane (the
nonsmooth boundary of the paper, here every corner and edge of the polytope) or needs more than
`R` reflections. `R` counts the reflections still allowed. A bounded polytope always has a `t̄`;
without one the ray never leaves and the end is `x + ℓ d`.

## Inputs
* `P` – H-polytope

## Output
* the end of the billiard trajectory of length `ℓ` from `x` along `d`, at most `R` reflections

## References

* [1] [B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control and
      optimization". IFAC Proceedings Volumes,
      2014.](../../../../../../references/2014/polyak-ifac-billiard-walk.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The end of the billiard trajectory of length `ℓ` from `x` along `d`, at most `R` reflections. -/
noncomputable def HPolytope.billiardEnd (P : HPolytope E) :
    ℕ → E → E → ℝ → Option E
  | R, x, d, ℓ =>
    -- the first hyperplane the ray meets, `t̄` of `[1, Eq. 1]`
    match P.chordHighIndex x d with
    | none => some (x + ℓ • d)
    | some i =>
      let tBar : ℝ := P.hitTime x d i
      -- the trajectory ends on this segment
      if ℓ ≤ tBar then some (x + ℓ • d)
      else
        match R with
        | 0 => none
        | R + 1 =>
          -- the boundary point and its unit normal
          let y : E := x + tBar • d
          let s : E := P.facetNormal i
          -- on more than one hyperplane: nonsmooth, go to step 2
          if ∀ j, j ≠ i → P.A j y < P.b j then
            P.billiardEnd R y (billiardReflect s d) (ℓ - tBar)
          else none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
