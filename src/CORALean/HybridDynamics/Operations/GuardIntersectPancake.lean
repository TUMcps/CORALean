module

public import CORALean.ContDynamics.NonlinParamSys.Operations.ReachUnion
public import CORALean.ContDynamics.NonlinParamSys.Definitions.PancakeScaled
public import CORALean.ContDynamics.NonlinearSys.Operations.ReachUnion
public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplane

@[expose] public section

/-!
# `NonlinearSys.WithSteps.guardIntersectPancake`, the time-scaling guard intersection

CORA's `guardIntersect_pancake` [1], one `let` per step: the scaled system `F = g f`
(`NonlinearSys.pancakeScaled`), its reach set, a single jump of the original system across the
guard (`aux_jump`) and the projection onto the hyperplane. Departures: the guard `nᵀx = d` is
oriented by the caller; the scaled reach is a union of time-point sets and the jump runs from
every member (CORA takes the last), so the result is a union, outer where CORA's is one set; the
jump's step `δ` and the scaled system's certificates are the caller's; `none` where a reach fails.
`maxDist` enters through the parameter set `scaled.P` (CORA's `paramInt`).

## Inputs
* `sys` – nonlinear system
* `scaled` – time-scaled system
* `nv` – guard normal
* `d` – guard offset
* `R₀` – initial set
* `tScaled` – scaled final time
* `δ` – jump step
* `optionsScaled` – options of the scaled reach
* `optionsJump` – options of the jump reach

## Output
* union of sets on the guard, none if a reach fails

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
