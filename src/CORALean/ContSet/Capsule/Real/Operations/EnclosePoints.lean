module

public import CORALean.ContSet.Capsule.Real.Operations.Empty
public import CORALean.Global.EuclideanNorm
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-!
# `Capsule.enclosePoints`

CORA's `@capsule/enclosePoints.m`: the center is the mean, the generator runs to the point
farthest from it (`[~,idxMax] = max(dist)`, here the first such by `List.argmax`), and the radius
is the largest distance of a point from the axis. No points give the empty capsule, as CORA's
`capsule.empty(n)`; one point gives `g = 0` and `r = 0` (CORA special-cases it).

CORA's radius is `max(vecnorm(((points-c)' * g_unit)' .* g_unit))`, the *projection* of each
point onto the axis rather than its distance from it. That is at least the generator's length
for the farthest point, so the ball it gives is sound but wasteful. Here the radius is the
distance from the axis, the rejection `d - (d·g/g·g) g`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A capsule enclosing the points `pts`: mean center, generator to the farthest point, radius
the largest distance from the axis. -/
noncomputable def Capsule.enclosePoints (pts : Fin N → Vec ℝ n) : Capsule n :=
  let c := (1 / (N : ℝ)) • ∑ j, pts j
  let d := fun j => pts j - c
  match (List.finRange N).argmax (fun j => ∑ i, d j i ^ 2) with
  | none => Capsule.empty n
  | some jmax =>
    let g := d jmax
    let rej := fun j => d j - ((d j ⬝ᵥ g) / (g ⬝ᵥ g)) • g
    let r := ((List.finRange N).map fun j => ‖rej j‖₂).foldr max 0
    ⟨c, g, r⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
