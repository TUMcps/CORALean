module

public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# The dynamics interfaces

CORA's `contDynamics` and its `reach`, as classes; each system's `Instances.lean` instantiates them,
and every system class does but `LinProbSys`, which defines no run yet.

`ContDynamics`: `n` states (CORA's `nrOfDims`), `nrOfInputs`, `nrOfDisturbances`, and
`IsTrajectory sys T X₀ U W x u w`, the class's own run on `T` over its whole equation, under the
input `u` in `U` and the disturbance `w` in `W`, what else it carries (outputs, noise, parameters,
algebraic variables) quantified away. `ContDynamicsDT` is the same over steps, a class of its own
because every discrete-time class constrains every step, with no `T` to give.

`Reach`: `reachExact sys params` is what the dynamics reach, a `Set` nothing may widen;
`reach sys params options` what an algorithm computes, `none` where it could not certify its
soundness conditions at run time, where CORA raises an error; `reach_outer` the enclosure, at
`reach … = some R` only, so a failed run proves nothing. A positive zonotope order is a field with
a default proof, refused at elaboration as CORA's `validateOptions` refuses it. `P n sys` is CORA's
`params` (`X₀`, `[tStart, tFinal]`, `U` in the system's own input dimension), `O` its `options`,
both `outParam`s as CORA dispatches on `sys` alone; `Sys` may sit in `Type 1`, as a loop does.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- CORA's `contDynamics` in continuous time: `n` states, `nrOfInputs` inputs, `nrOfDisturbances`
disturbances, and `IsTrajectory sys T X₀ U W x u w`: `x` is a run of `sys` on `T` from `X₀` under
the input `u` in `U` and the disturbance `w` in `W`. -/
class ContDynamics (Sys : Type u) (n : outParam ℕ) where
  nrOfInputs : Sys → ℕ
  nrOfDisturbances : Sys → ℕ
  IsTrajectory (sys : Sys) (T : Set ℝ) (X₀ : Set (Vec ℝ n)) (U : Set (Vec ℝ (nrOfInputs sys)))
    (W : Set (Vec ℝ (nrOfDisturbances sys))) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ (nrOfInputs sys))
    (w : ℝ → Vec ℝ (nrOfDisturbances sys)) : Prop

/-- `ContDynamics` over sampling steps: a run is indexed by ℕ and constrained at every step, so
`IsTrajectory` takes no time set. -/
class ContDynamicsDT (Sys : Type u) (n : outParam ℕ) where
  nrOfInputs : Sys → ℕ
  nrOfDisturbances : Sys → ℕ
  IsTrajectory (sys : Sys) (X₀ : Set (Vec ℝ n)) (U : Set (Vec ℝ (nrOfInputs sys)))
    (W : Set (Vec ℝ (nrOfDisturbances sys))) (x : ℕ → Vec ℝ n) (u : ℕ → Vec ℝ (nrOfInputs sys))
    (w : ℕ → Vec ℝ (nrOfDisturbances sys)) : Prop

/-- `reachExact sys params` is the exact set the problem `params` asks for; `reach sys params
options` is what an algorithm computes for it, `none` if it could not certify itself;
`reach_outer` is the enclosure between them, at a set `reach` returned and at nothing else. -/
class Reach (Sys : ℕ → Type u) (P : outParam ((n : ℕ) → Sys n → Type)) (O : outParam Type)
    (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] where
  reachExact {n : ℕ} : (sys : Sys n) → P n sys → Set (Vec ℝ n)
  reach {n : ℕ} : (sys : Sys n) → P n sys → O → Option (SetUnion (S n))
  reach_outer {n : ℕ} (sys : Sys n) (params : P n sys) (options : O) {R : SetUnion (S n)}
    (h : reach sys params options = some R) : reachExact sys params ⊆ construct R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
