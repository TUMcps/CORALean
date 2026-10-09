import CORALean.NN.Operations.PropagateBounds
import CORALean.NN.Theorems.EncloseOuter

/-!
# The propagated bounds contain the stretch's image
If `seg` is sound at `f` and the bounds `j` already held contain the image of `B`'s points
under `f`, which is what makes them bounds of that input, the propagated bounds contain it
too: the intersection of two outer sets is an outer set of the points in both. Outer, not
exact: the interval image through the stretch is an enclosure.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of `B` goes, under `f`, into the propagated bounds. -/
theorem NeuralNetwork.Sound.propagateBounds_outer [Intersection (S m) (Vec ℝ m)]
    {seg : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m} (hf : seg.Sound f) (B : S n)
    (stored : Option (S m))
    (hstored : ∀ I, stored = some I → ∀ x ∈ construct B, f x ∈ construct I) :
    ∀ x ∈ construct B, f x ∈ construct (seg.propagateBounds B stored) := by -- --- PROOF ---
  intro x hx
  cases stored with
  | none => exact hf.enclose_outer B x hx
  | some I =>
      exact Intersection.intersection_outer _ _
        ⟨hf.enclose_outer B x hx, hstored I rfl x hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
