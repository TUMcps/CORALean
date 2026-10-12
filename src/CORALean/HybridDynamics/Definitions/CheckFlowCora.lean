import CORALean.HybridDynamics.Definitions.Location
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# `Location.checkFlowCora`: CORA's `checkFlow` as printed, with the vector offset

CORA's `@location/checkFlow.m` at a hyperplane guard `{x | c·x = d}` and a `linearSys`
`ẋ = A x + B u + sys.c`, `u ∈ [uLo, uHi]`, the linear branch of `aux_flowInDirection`, one `let`
per MATLAB line. `A` is the location's; `B` and `off` (`sys.c`) are passed beside it, since
`Location` folds them into `U`. The last summand of `flow = cA*cen + (cA*G)*I +
(c*sys.B)*interval(params.U) + sys.c` is the `n×1` vector `sys.c`, so `res` is a vector and `if
res` holds only if every entry `… + sys.c(i)` of the supremum is positive. That is kept.

`@location/guardIntersect.m` runs `[res,P{i}] = checkFlow(loc,guard,P{i},params)` on each group
of time-interval sets meeting a hyperplane or level-set guard and skips the group if `res` is
false: the sets dropped here are never intersected with the guard.

Left out: `c = guard.Ae ./ norm(guard.Ae)` and `aux_adaptGuard` (`c` is the outward unit normal,
as for `Location.checkFlow`); `E*params.w` (no `E`); and `R = B * reduce(B'*Rproj,'pca',1)`,
which leaves `Rproj` unchanged when it has at most `n` generators and encloses it otherwise.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `checkFlow`, linear branch, as printed: the reach sets kept, `sys.c` added entrywise. -/
noncomputable def Location.checkFlowCora (ℓ : Location (fun n => Real.Zonotope (Vec ℝ n)) G L ℝ n)
    (B : Mat ℝ n m) (off : Vec ℝ n) (uLo uHi : Vec ℝ m) (c : Vec ℝ n) (d : ℝ)
    (Rs : List (Real.Zonotope (Vec ℝ n))) : List (Real.Zonotope (Vec ℝ n)) :=
  open Classical in Rs.filter fun R =>
    let A : Mat ℝ n n := toRealMat ℓ.dynamics.A
    -- Rproj = projectOnHyperplane(R,guard): the map (I - c cᵀ) x + d c
    let P : Mat ℝ n n := 1 - vecMulVec c c
    let Rproj : Real.Zonotope (Vec ℝ n) := ⟨R.h, P *ᵥ R.c + d • c, fun j => P *ᵥ R.G j⟩
    -- params.u = center(params.U)
    let u : Vec ℝ m := (1 / 2 : ℝ) • (uLo + uHi)
    -- flow = fcnHan(0,center(Rproj)), with fcnHan = A*x + B*params.u + sys.c
    let flow₀ : Vec ℝ n := A *ᵥ Rproj.c + B *ᵥ u + off
    -- flow = c*flow
    let flowC : ℝ := c ⬝ᵥ flow₀
    -- cen = center(R); G = generators(R)   (R = Rproj, the 'pca' box step left out)
    let cen : Vec ℝ n := Rproj.c
    let Gs : Fin Rproj.h → Vec ℝ n := Rproj.G
    -- cA = c*sys.A
    let cA : Vec ℝ n := Aᵀ *ᵥ c
    -- flow = cA*cen + (cA*G)*I + (c*sys.B)*interval(params.U) + sys.c, its supremum entrywise
    let cB : Vec ℝ m := Bᵀ *ᵥ c
    let flowSup : Vec ℝ n := fun i =>
      cA ⬝ᵥ cen + ∑ j, |cA ⬝ᵥ Gs j| + ∑ k, max (cB k * uLo k) (cB k * uHi k) + off i
    -- if flow > 0 (fast check), else res = supremum(interval(flow)) > 0, `if res`: every entry
    (0 < flowC ∨ ∀ i, 0 < flowSup i : Prop)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
