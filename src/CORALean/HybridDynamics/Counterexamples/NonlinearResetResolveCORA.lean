module

public import CORALean.HybridDynamics.Operations.NonlinearResetResolve
public import CORALean.HybridDynamics.Operations.NonlinearResetResolveCORA
public import CORALean.Global.StepOf

@[expose] public section

/-!
# CORA's `nonlinearReset/resolve` ignores the global index of an input

CORA's `@nonlinearReset/resolve.m` ends with `f_sym = subs(f_sym, u_sym(idxGlobalInput),
u_sym(1:numGlobalInputs))`: the globally bound inputs of the components are numbered `1, 2, ...`
in the order they occur, whatever global input `inputBinds{i}(j,2)` they are bound to, while
`linearReset/resolve` sums the columns of one global index. With two components whose inputs are
bound to the global inputs `2` and `1`, the first component receives the *first* argument of
the resolved reset (read from the source, not run).

The example: two components with one state, input and output each, the reset `x'_i = u_i`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the corrected resolve gives one, CORA's gives zero
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ------------------------------------------  STEPS  ------------------------------------------- --

namespace ResolveSwapExample

-- two components, one state, input and output each
@[step_of NonlinearReset.resolveCORA_swap]
abbrev step_dims : Fin 2 → ℕ := fun _ => 1

@[step_of NonlinearReset.resolveCORA_swap]
def step_reset : NonlinearReset 2 (∑ i, step_dims i) 2 where
  f := fun _ u a => u (finSigmaFinEquiv ⟨a, 0⟩)

@[step_of NonlinearReset.resolveCORA_swap]
def step_out : ∀ i : Fin 2, Vec ℝ (step_dims i) → Vec ℝ (step_dims i) → Vec ℝ (step_dims i) :=
  fun _ _ _ => 0

@[step_of NonlinearReset.resolveCORA_swap]
def step_stateBinds : ∀ i : Fin 2, Fin (step_dims i) → Fin 2 := fun i _ => i

-- the inputs are bound to the global inputs `1` and `0`
@[step_of NonlinearReset.resolveCORA_swap]
def step_binds : ∀ i : Fin 2, Fin (step_dims i) → ResolveSource 2 step_dims 2 :=
  fun i _ => .global (if i = 0 then 1 else 0)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_globalColumns : NonlinearReset.globalColumns step_binds = 2 := rfl

private theorem aux_rank : NonlinearReset.globalRank step_binds ⟨0, 0⟩ = 0 := rfl

end ResolveSwapExample

open ResolveSwapExample


-- =======================================  MAIN THEOREM  ======================================= --

/-- The first component's state after the jump is the global input `1` (`NonlinearReset.resolve`),
but CORA's resolved reset hands it its first argument. At the arguments `v i = i` the two
disagree. -/
theorem NonlinearReset.resolveCORA_swap : -- --- CONCL ---
    ((step_reset.resolve step_out step_stateBinds step_binds).f (fun _ => 0)
      (fun i => (i : ℝ)) 0 = 1) ∧
    ((step_reset.resolveCORA step_out step_stateBinds step_binds).f (fun _ => 0)
      (fun i => (i : ℝ)) 0 = 0) := by -- --- PROOF ---
  constructor
  · simp [NonlinearReset.resolve, step_reset, step_binds]
  · simp [NonlinearReset.resolveCORA, step_reset, step_binds, aux_rank, aux_globalColumns]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
