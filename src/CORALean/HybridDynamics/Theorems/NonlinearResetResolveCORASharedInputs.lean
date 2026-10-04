import CORALean.HybridDynamics.Operations.NonlinearResetGlobalColumns

/-!
# CORA's `nonlinearReset/resolve` has too many inputs for shared global inputs

`numGlobalInputs = nnz(idxGlobalInput)` counts the inputs of the components bound to a global
input, with repetitions, while a `parallelHybridAutomaton` has `length(unique(...))` global inputs
(`linearReset/resolve` sums the columns of one index). With both components' inputs bound to the
global input `1` the resolved reset has two inputs where the product has one (read from the
source, not run).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace ResolveSharedExample

-- two components, one state, input and output each
abbrev aux_dims : Fin 2 → ℕ := fun _ => 1

-- both inputs are bound to the global input `0`
def aux_binds : ∀ i : Fin 2, Fin (aux_dims i) → ResolveSource 2 aux_dims 1 := fun _ _ => .global 0

theorem aux_globalColumns : NonlinearReset.globalColumns aux_binds = 2 := rfl

end ResolveSharedExample


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `numGlobalInputs` is `2` where the product has the one global input `0`. -/
theorem NonlinearReset.globalColumns_shared :
    NonlinearReset.globalColumns ResolveSharedExample.aux_binds ≠ 1 := by
  rw [ResolveSharedExample.aux_globalColumns]
  exact Nat.succ_ne_self 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
