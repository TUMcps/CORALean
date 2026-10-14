module

public import CORALean.HybridDynamics.Operations.NonlinearResetSynchronizeResolveCORA
public import CORALean.HybridDynamics.Operations.NonlinearResetResolve

@[expose] public section

/-!
# The bug in `resolve` reaches `transition/synchronize`

`transition/synchronize.m` ends its reset by `resolve(reset_sync, flowList, stateBinds,
inputBinds)`, which `mergeTransitionSets.m` calls with the `pHA.bindsInputs` the user passed to
`parallelHybridAutomaton`; the constructor only checks that the left column lies in `0..numComps`,
so global inputs may be bound out of order. Two components with one state, input and output each,
the resets `x'_i = u_i` lifted to the product, the inputs bound to the global inputs `2` and `1`:
the composed reset of CORA gives the first component its first argument, the product its second.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace SynchronizeResolveExample

abbrev aux_dims : Fin 2 → ℕ := fun _ => 1

def aux_out : ∀ i : Fin 2, Vec ℝ (aux_dims i) → Vec ℝ (aux_dims i) → Vec ℝ (aux_dims i) :=
  fun _ _ _ => 0

def aux_stateBinds : ∀ i : Fin 2, Fin (aux_dims i) → Fin 2 := fun i _ => i

/-- the inputs are bound to the global inputs `1` and `0` -/
def aux_binds : ∀ i : Fin 2, Fin (aux_dims i) → ResolveSource 2 aux_dims 2 :=
  fun i _ => .global (if i = 0 then 1 else 0)

theorem aux_globalColumns : NonlinearReset.globalColumns aux_binds = 2 := rfl

theorem aux_rank : NonlinearReset.globalRank aux_binds ⟨0, 0⟩ = 0 := rfl

/-- the reset of component `i` lifted to the product: `x'_i = u_i`, other states `0` -/
def aux_resets (i : Fin 2) : NonlinearReset 2 (∑ i, aux_dims i) 2 where
  f := fun _ u a => if a = i then u (finSigmaFinEquiv ⟨i, 0⟩) else 0

end SynchronizeResolveExample

open SynchronizeResolveExample


-- =======================================  MAIN THEOREM  ======================================= --

/-- At the arguments `v i = i`, the first component's state after the synchronized jump is `1`
for the parallel automaton (`resolve` of the synchronized reset), `0` for CORA. -/
theorem NonlinearReset.synchronizeResolveCORA_counterexample :
    (((NonlinearReset.synchronize aux_resets ∅).resolve aux_out aux_stateBinds aux_binds).f
      (fun _ => 0) (fun i => (i : ℝ)) 0 = 1) ∧
    ((NonlinearReset.synchronizeResolveCORA aux_resets ∅ aux_out aux_stateBinds aux_binds).f
      (fun _ => 0) (fun i => (i : ℝ)) 0 = 0) := by
  constructor
  · simp [NonlinearReset.resolve, NonlinearReset.synchronize, aux_resets, aux_binds]
  · simp [NonlinearReset.synchronizeResolveCORA, NonlinearReset.resolveCORA,
      NonlinearReset.synchronize, aux_resets, aux_binds, aux_rank, aux_globalColumns]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
