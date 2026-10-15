module

public import CORALean.HybridDynamics.Parallel.Definitions.Lifting

@[expose] public section

/-!
# A `Lifting` that loses nothing

`Lifting` asks only that the lifted sets contain what the components' sets put together: an outer
bargain, which is all `IsRun.toProduct` needs. The converse of `toProduct` needs the opposite
inclusions, and this structure is them: a point of a lifted set has the components' blocks in the
components' sets. The input set is read where no global input feeds two inputs (`hb`) and every
component's set is nonempty (`hne`): a product of boxes cannot say which of two feeders a global
input came from, nor that an empty set of one component empties the whole.

`boxLifting`, `zonoLifting` and `conZonoLifting` satisfy it (`Theorems.BoxLiftingExact`, ...).
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {k m : ℕ} {n : Fin k → ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure ParallelHybridAutomaton.Lifting.Exact
    (lift : ParallelHybridAutomaton.Lifting S G n m) : Prop where
  inv_inv (gs : ∀ i, G (n i)) (x : ∀ i, Vec ℝ (n i)) (hx : stack x ∈ construct (lift.inv gs)) :
    ∀ i, x i ∈ construct (gs i)
  guard_inv (i : Fin k) (g : G (n i)) (x : ∀ i, Vec ℝ (n i))
    (hx : stack x ∈ construct (lift.guard i g)) : x i ∈ construct g
  input_inv {d q : Fin k → ℕ} (b : ∀ i, Fin (d i) → ResolveSource k q m)
    (hb : ∀ i i' j j' a, b i j = .global a → b i' j' = .global a →
      (⟨i, j⟩ : Σ i, Fin (d i)) = ⟨i', j'⟩)
    (us : ∀ i, S (d i)) (hne : ∀ i, (construct (us i)).Nonempty) (g : Vec ℝ m)
    (hg : g ∈ construct (lift.input b us)) :
    ∀ i, ∃ v ∈ construct (us i), ∀ j a, b i j = .global a → v j = g a
  dist_inv {d : Fin k → ℕ} (ws : ∀ i, S (d i)) (w : ∀ i, Vec ℝ (d i))
    (hw : stack w ∈ construct (lift.dist ws)) : ∀ i, w i ∈ construct (ws i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
