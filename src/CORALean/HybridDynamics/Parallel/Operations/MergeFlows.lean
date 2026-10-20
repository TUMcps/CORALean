module

public import CORALean.Global.ExactScalar
public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# `mergeFlows`: `mergeFlowsLinearSys` assembled without arithmetic

CORA's `aux_mergeFlowsLinearSys` at components whose inputs and outputs are their states: `B` and
`C` identities, `D` and `k` zero. Every entry of the merged system is an existing entry, `0` or
`1`, chosen by `if`, with no arithmetic, so the result is exact at every scalar with an exact `0`
and `1`, rounded ones included (#117). It reads `A`, `c`, `E`, `F` and the bindings; the flow law
`mergeFlows_flowLaw` holds where the rest is as said (`StateBound`). Restriction: CORA's
`Amerged += B * C` adds the `1`, and an addition rounds; where an input is bound to its own
component's output the `1` replaces `A_ij`, which is `Amerged` exactly when `A_ij = 0`
(`SelfBindFree`). At a commutative ring the merge is `mergeFlowsLinearSys`.

## Inputs
* `P` – parallel automaton
* `ℓ` – current locations

## Output
* product flow assembled without arithmetic
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {S G : ℕ → Type} {𝕋 : Type} {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_mergeFlowsLinearSys` at state-bound components: `1` where `B C` and `B` are, `A`, `c`, `E`
and the bound rows of `F` copied. -/
def ParallelHybridAutomaton.mergeFlows [Scalar 𝕋] [ExactScalar 𝕋]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m) (ℓ : ∀ i, L i) : LinearSys 𝕋 (∑ i, n i) :=
  -- the binding of input `p` of component `i`, the input of its state `p`
  let bindOf : (i : Fin k) → Fin (n i) → Option (ResolveSource k (fun c => (P.sys ℓ c).q) m) :=
    fun i p => if h : p.val < (P.sys ℓ i).m then some (P.bindsAt ℓ i ⟨p.val, h⟩) else none
  let blockA : (Σ i, Fin (n i)) → (Σ i, Fin (n i)) → 𝕋 := fun a b =>
    if h : a.1 = b.1 then (P.sys ℓ a.1).A a.2 (Fin.cast (congrArg n h.symm) b.2) else 0
  let Amerged : Mat 𝕋 (∑ i, n i) (∑ i, n i) :=                     -- A, a `1` at the bound state
    Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv <| Matrix.of fun a b =>
      match bindOf a.1 a.2 with
      | some (.output c s) => if c = b.1 ∧ s.val = b.2.val then 1 else blockA a b
      | _ => blockA a b
  let Bmerged : Mat 𝕋 (∑ i, n i) m :=                               -- a `1` at the bound global
    Matrix.reindex finSigmaFinEquiv (Equiv.refl _) <| Matrix.of fun a g =>
      match bindOf a.1 a.2 with
      | some (.global a') => if a' = g then 1 else 0
      | _ => 0
  let cMerged : Vec 𝕋 (∑ i, n i) := fun r =>                         -- c
    (P.sys ℓ (finSigmaFinEquiv.symm r).1).c (finSigmaFinEquiv.symm r).2
  let Emerged : Mat 𝕋 (∑ i, n i) (∑ i, (P.sys ℓ i).r) :=             -- E, block diagonal
    Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv <| Matrix.of fun p q =>
      if h : p.1 = q.1 then (P.sys ℓ p.1).E p.2 (Fin.cast (by rw [h]) q.2) else 0
  let Fmerged : Mat 𝕋 (∑ i, n i) (∑ i, (P.sys ℓ i).s) :=             -- F of the bound output
    Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv <| Matrix.of fun p q =>
      match bindOf p.1 p.2 with
      | some (.output c s) => if h : c = q.1 then (P.sys ℓ q.1).F (h ▸ s) q.2 else 0
      | _ => 0
  ⟨m, ∑ i, n i, ∑ i, (P.sys ℓ i).r, ∑ i, (P.sys ℓ i).s, Amerged, Bmerged, cMerged,
    fun a b => if a = b then 1 else 0, fun _ _ => 0, fun _ => 0, Emerged, Fmerged⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
