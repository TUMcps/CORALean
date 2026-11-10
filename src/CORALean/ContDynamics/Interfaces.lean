module

public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# The dynamics interfaces

CORA's `contDynamics` and its `reach`, as classes, instantiated by every system class but
`LinProbSys`. `ContDynamics`: `n` states, `nrOfInputs`, `nrOfDisturbances` and `IsTrajectory`,
the class's own run on `T` under input `u` in `U` and disturbance `w` in `W`; `ContDynamicsDT`
is the same over steps. `Reach`: `reachExact` is what the dynamics reach, a `Set` nothing may
widen; `reach` what an algorithm computes, `none` where it could not certify its soundness
conditions at run time; `reach_outer` the enclosure. `P n sys` is CORA's `params`, `O` its
`options`, both `outParam`s as CORA dispatches on `sys` alone. `reach` returns CORA's
`reachSet` as the general `SetUnion`, without the times CORA stores with each set.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

open ContSetLike


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
class Reach (Sys : ℕ → Type u) (Params : outParam ((n : ℕ) → Sys n → Type))
    (Options : outParam Type) (ContSet : ℕ → Type)
    [∀ n, ContSetLike (ContSet n) (Vec ℝ n)] where
  reachExact {n : ℕ} : (sys : Sys n) → Params n sys → Set (Vec ℝ n)
  reach {n : ℕ} : (sys : Sys n) → Params n sys → Options → Option (SetUnion (ContSet n))
  reach_outer {n : ℕ} (sys : Sys n) (params : Params n sys) (options : Options)
    {R : SetUnion (ContSet n)} (h : reach sys params options = some R) :
    reachExact sys params ⊆ toSet R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
