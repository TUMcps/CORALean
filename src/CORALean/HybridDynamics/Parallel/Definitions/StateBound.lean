module

public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# Components whose inputs and outputs are their states

Where `mergeFlows` is `mergeFlowsLinearSys`: at every location tuple, every component's `B` and
`C` read as identities (`B p j = 1` exactly where `p` and `j` are the same index, likewise `C`),
its `D` and `k` as zero. An input `j` then drives state `j` and an output `s` is state `s`, the
reading CORA's `mergeFlows` gives `C = 1` with no `D`, `k`, `F`. A location in CORA's canonical
form, `LinearSys.canonical`, is one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar

variable {S G : ℕ → Type} {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.StateBound (P : ParallelHybridAutomaton S G k L 𝕋 n m) : Prop :=
  ∀ ℓ : ∀ i, L i,
    (∀ i (p : Fin (n i)) (j : Fin (P.sys ℓ i).m),
      toReal ((P.sys ℓ i).B p j) = if p.val = j.val then 1 else 0) ∧
    (∀ c (s : Fin (P.sys ℓ c).q) (q : Fin (n c)),
      toReal ((P.sys ℓ c).C s q) = if s.val = q.val then 1 else 0) ∧
    (∀ c (s : Fin (P.sys ℓ c).q) (j : Fin (P.sys ℓ c).m), toReal ((P.sys ℓ c).D s j) = 0) ∧
    (∀ c (s : Fin (P.sys ℓ c).q), toReal ((P.sys ℓ c).k s) = 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
