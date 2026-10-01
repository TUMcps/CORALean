import CORALean.Global.ExactScalar
import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

/-!
# `mergeFlows`

CORA's `mergeFlows` at linear flows: the components' dynamics as one system of dimension
`∑ i, n i`. The matrix is block diagonal in the components' `A`, plus a `1` at
row `⟨i, j⟩`, column `⟨c, s⟩` for each input `binds i j = state c s`: that coordinate's
input *is* state `⟨c, s⟩`, so it moves from `u` into `A`, as in CORA's `Amerged += B * C`.
A global input stays in `u`. The matrix is built by `if` out of the components' own entries and
the constants `0` and `1`, with no arithmetic, so it is exact at every scalar with an exact `0`
and `1`, rounded ones included (#117).

Restriction: CORA's `Amerged += B * C` *adds* the `1` to the block entry, and an addition rounds.
Where the bound state is a state of the coordinate's own component, that sum would need `A_ij + 1`
at the one entry both land on, so this definition puts the `1` there and drops `A_ij`. That is
`Amerged` exactly when `A_ij = 0`, which `SelfBindFree` states and the theorems assume. A binding
to another component's state is always exact: the block is `0` there.
CORA's nonlinear branch, symbolic, is not here (#40).
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.mergeFlows [ExactScalar 𝕋] (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (ℓ : ∀ i, L i) : LinearSys 𝕋 (∑ i, n i) where
  A := Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv <| Matrix.of fun a b =>
    match P.binds a.1 a.2 with
    | .global _ => if h : a.1 = b.1 then ((P.comp a.1).loc (ℓ a.1)).dynamics.A a.2
        (Fin.cast (congrArg n h.symm) b.2) else 0
    | .state c s =>
      if (⟨c, s⟩ : Σ i, Fin (n i)) = b then 1
      else if h : a.1 = b.1 then ((P.comp a.1).loc (ℓ a.1)).dynamics.A a.2
        (Fin.cast (congrArg n h.symm) b.2) else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
