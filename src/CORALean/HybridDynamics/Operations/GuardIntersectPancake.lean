module

public import CORALean.ContDynamics.NonlinParamSys.Operations.ReachUnion
public import CORALean.ContDynamics.NonlinParamSys.Definitions.PancakeScaled
public import CORALean.ContDynamics.NonlinearSys.Operations.ReachUnion
public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplane

@[expose] public section

/-!
# `NonlinearSys.WithSteps.guardIntersectPancake`, the time-scaling guard intersection

CORA's `guardIntersect_pancake` [1], one `let` per step: the scaled system `F = g f`
(`NonlinearSys.pancakeScaled`, `aux_scaledSystem`), its reach set (`aux_reachTimeScaled`), a
single jump of the original system across the guard (`aux_jump`) and the projection onto the
hyperplane. Departures: the guard `nᵀx = d` is oriented by the caller (`nᵀx > d` where the reach
set's center is; CORA flips the halfspace when it holds the center); the scaled reach is the union
of its time-point sets over `[0, tScaled]` and the jump runs from every member (CORA takes
the last time-point set, `timePoint.set{end}`, and stops at the specification), so the result is
a union, outer where CORA's is one set; the jump's step `δ` (the loop of `aux_jump` that bisects
or grows it until the end set lies across) and the scaled system's certificates are the caller's;
`none` where a reach fails. `maxDist = sup(nᵀR₀ − d)` enters through the parameter set
`scaled.P` (CORA's `paramInt`), which soundness needs only to hold a positive value.

## References

* [1] `hybridDynamics/@location/guardIntersect_pancake.m`; S. Bak et al. "Time-Triggered
      Conversion of Guards for Reachability Analysis of Hybrid Automata". In Proc. of FORMATS,
      2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R = guardIntersect_pancake(loc,R0,guard,guardID,params,options)` for the guard `nᵀx = d`,
the scaled run over `[0, tScaled]` and the jump over `[0, δ]`. -/
noncomputable def NonlinearSys.WithSteps.guardIntersectPancake
    (sys : NonlinearSys.WithSteps S Rg m n) (scaled : NonlinParamSys.WithSteps S Rg m 1 n)
    (nv : Vec ℝ n) (d : ℝ) (R₀ : S n) (tScaled δ : ℝ) (optionsScaled optionsJump :
      LinearSys.ReachOptions ℝ) : Option (SetUnion (S n)) :=
  let Rscaled := scaled.reachUnion ⟨R₀, 0, tScaled⟩ optionsScaled   -- aux_reachTimeScaled
  let jump := fun Ri => sys.reachUnion ⟨Ri, 0, δ⟩ optionsJump       -- aux_jump, from each member
  let nrm := Real.sqrt (nv ⬝ᵥ nv)                                    -- normalizeConstraints
  Rscaled.bind fun Rs => (Rs.sets.mapM jump).map fun Rj =>
    ⟨(Rj.flatMap SetUnion.sets).map fun Rk =>                     -- R = projectOnHyperplane(R,..)
      ContSet.projectOnHyperplane Rk (nrm⁻¹ • nv) (d / nrm)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
