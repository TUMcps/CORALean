module

public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# Synchronization labels

CORA's `syncLabel` of a transition, and what CORA reads off all of them (`priv_labelOccurrences`).
`Transition` carries no label, so the labels live beside the automaton: `label i e` is the label of
a transition `e` of component `i`, `none` for an unlabeled one; `parts λ` are the components in
which `λ` occurs anywhere, and `labels` lists every label. The last two the caller supplies, as
`Lifting` is supplied, since a location type `L i` is not enumerable. A labeled transition is never
taken alone: it fires together with the `λ`-labeled transition of every component in `parts λ`,
or not at all (`IsSyncRun`, `mergeTransitionSetsSync`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {G : ℕ → Type} {𝕋 : Type} {k : ℕ} {n : Fin k → ℕ} {L : Fin k → Type} {Λ : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- The synchronization labels of a parallel automaton: the label of each transition, the components
in which a label occurs, and the list of all labels. -/
structure ParallelHybridAutomaton.SyncLabels (G : ℕ → Type) (L : Fin k → Type) (𝕋 : Type)
    (n : Fin k → ℕ) (Λ : Type) where
  label : ∀ i, Transition G (L i) 𝕋 (n i) → Option Λ
  parts : Λ → Fin k → Bool
  labels : List Λ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
