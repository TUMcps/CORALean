module

public import CORALean.Global.ExactScalar
public import CORALean.HybridDynamics.Parallel.Definitions.Lifting

@[expose] public section

/-!
# `liftTransition`

A transition of component `c` as a transition of the product: the guard lifted, the reset the
identity off component `c`'s block and `e`'s on it, and the target the location tuple with
component `c` moved. CORA's `lift` and `synchronize` for a transition without a sync label;
labels are not in `Transition` (#40).
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.liftTransition [ExactScalar 𝕋]
    {binds : ∀ i, Fin (n i) → InputSource k n m}
    (lift : ParallelHybridAutomaton.Lifting S G n m binds) (ℓ : ∀ i, L i) (c : Fin k)
    (e : Transition G (L c) 𝕋 (n c)) : Transition G (∀ i, L i) 𝕋 (∑ i, n i) where
  guard := lift.guard c e.guard
  W := Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv <| Matrix.of fun a b =>
    if h : a.1 = c then
      (if h' : b.1 = c then e.W (Fin.cast (congrArg n h) a.2) (Fin.cast (congrArg n h') b.2)
        else 0)
    else (if a = b then 1 else 0)
  w := Equiv.piCongrLeft (fun _ => 𝕋) finSigmaFinEquiv fun a =>
    if h : a.1 = c then e.w (Fin.cast (congrArg n h) a.2) else 0
  target := Function.update ℓ c e.target

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
