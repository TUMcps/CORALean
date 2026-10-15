module

public import CORALean.HybridDynamics.Parallel.Operations.SyncPick

@[expose] public section

/-!
# Runs of a parallel automaton with synchronization labels

`Run` with the labels' semantics: an unlabeled transition is taken by its component alone, as in
`Run`; a labeled one is never taken alone but together with the `λ`-labeled transition of every
participant of `λ` (CORA's `priv_gatherTransitions`), all guards holding at the end of the same
stay, every participant resetting and moving, the rest standing still. `Run` is the case of no
labels (`labels = []`, every `label = none`).
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type} {Λ : Type}


-- ========================================  MAIN TYPE  ========================================= --

inductive ParallelHybridAutomaton.SyncRun [DecidableEq Λ] [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lab : ParallelHybridAutomaton.SyncLabels G L 𝕋 n Λ) :
    (∀ i, L i) → (∀ i, Vec ℝ (n i)) → (∀ i, L i) → (∀ i, Vec ℝ (n i)) → Prop where
  | flow {ℓ : ∀ i, L i} {τ : ℝ} {x : ∀ i, ℝ → Vec ℝ (n i)} {u w} {g : ℝ → Vec ℝ m}
      (h : P.Stay ℓ τ x u w g) : P.SyncRun lab ℓ (fun i => x i 0) ℓ (fun i => x i τ)
  -- an unlabeled transition of one component, the others standing still
  | jump {ℓ ℓ' : ∀ i, L i} {τ : ℝ} {x : ∀ i, ℝ → Vec ℝ (n i)} {u w} {g : ℝ → Vec ℝ m}
      {y : ∀ i, Vec ℝ (n i)} {c : Fin k} {e : Transition G (L c) 𝕋 (n c)}
      (h : P.Stay ℓ τ x u w g) (hmem : e ∈ ((P.comp c).loc (ℓ c)).trans)
      (hlab : lab.label c e = none) (hguard : x c τ ∈ construct e.guard)
      (rest : P.SyncRun lab (Function.update ℓ c e.target)
        (Function.update (fun i => x i τ) c (e.reset (x c τ))) ℓ' y) :
      P.SyncRun lab ℓ (fun i => x i 0) ℓ' y
  -- the transitions of label `a`, all together
  | sync {ℓ ℓ' : ∀ i, L i} {τ : ℝ} {x : ∀ i, ℝ → Vec ℝ (n i)} {u w} {g : ℝ → Vec ℝ m}
      {y : ∀ i, Vec ℝ (n i)} {a : Λ} (ha : a ∈ lab.labels) (h : P.Stay ℓ τ x u w g)
      (havail : ∀ c, lab.parts a c = true → (lab.pick P ℓ a c).isSome)
      (hguard : ∀ c e, lab.pick P ℓ a c = some e → x c τ ∈ construct e.guard)
      (rest : P.SyncRun lab
        (fun c => match lab.pick P ℓ a c with
          | some e => e.target
          | none => ℓ c)
        (fun c => match lab.pick P ℓ a c with
          | some e => e.reset (x c τ)
          | none => x c τ) ℓ' y) :
      P.SyncRun lab ℓ (fun i => x i 0) ℓ' y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
