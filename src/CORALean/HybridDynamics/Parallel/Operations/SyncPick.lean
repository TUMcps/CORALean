import CORALean.HybridDynamics.Parallel.Definitions.SyncLabels

/-!
# `SyncLabels.pick`

The transition component `c` contributes to the synchronized transition for label `λ` at the
location tuple `ℓ`: the first `λ`-labeled transition of its current location, if `c` is one of
`λ`'s participants, and none otherwise. CORA's constructor allows one transition per label in a
location, so `find?` takes that one; `none` for a participant is what makes `λ` unavailable.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type} {Λ : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.SyncLabels.pick [DecidableEq Λ]
    (lab : ParallelHybridAutomaton.SyncLabels G L 𝕋 n Λ)
    (P : ParallelHybridAutomaton S G k L 𝕋 n m) (ℓ : ∀ i, L i) (a : Λ) (c : Fin k) :
    Option (Transition G (L c) 𝕋 (n c)) :=
  if lab.parts a c then
    ((P.comp c).loc (ℓ c)).trans.find? fun e => decide (lab.label c e = some a)
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
