module

public import CORALean.HybridDynamics.Operations.NonlinearResetResolve
public import CORALean.HybridDynamics.Operations.NonlinearResetResolveCORA

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
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace ResolveSwapExample

-- two components, one state, input and output each
abbrev aux_dims : Fin 2 → ℕ := fun _ => 1

def aux_reset : NonlinearReset 2 (∑ i, aux_dims i) 2 where
  f := fun _ u a => u (finSigmaFinEquiv ⟨a, 0⟩)

def aux_out : ∀ i : Fin 2, Vec ℝ (aux_dims i) → Vec ℝ (aux_dims i) → Vec ℝ (aux_dims i) :=
  fun _ _ _ => 0

def aux_stateBinds : ∀ i : Fin 2, Fin (aux_dims i) → Fin 2 := fun i _ => i

-- the inputs are bound to the global inputs `1` and `0`
def aux_binds : ∀ i : Fin 2, Fin (aux_dims i) → ResolveSource 2 aux_dims 2 :=
  fun i _ => .global (if i = 0 then 1 else 0)

theorem aux_globalColumns : NonlinearReset.globalColumns aux_binds = 2 := rfl

theorem aux_rank : NonlinearReset.globalRank aux_binds ⟨0, 0⟩ = 0 := rfl

end ResolveSwapExample

open ResolveSwapExample


-- =======================================  MAIN THEOREM  ======================================= --

/-- The first component's state after the jump is the global input `1` (`NonlinearReset.resolve`),
but CORA's resolved reset hands it its first argument. At the arguments `v i = i` the two
disagree. -/
theorem NonlinearReset.resolveCORA_swap : -- --- STMT ---
    ((aux_reset.resolve aux_out aux_stateBinds aux_binds).f (fun _ => 0)
      (fun i => (i : ℝ)) 0 = 1) ∧
    ((aux_reset.resolveCORA aux_out aux_stateBinds aux_binds).f (fun _ => 0)
      (fun i => (i : ℝ)) 0 = 0) := by -- --- PROOF ---
  constructor
  · simp [NonlinearReset.resolve, aux_reset, aux_binds]
  · simp [NonlinearReset.resolveCORA, aux_reset, aux_binds, aux_rank, aux_globalColumns]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
