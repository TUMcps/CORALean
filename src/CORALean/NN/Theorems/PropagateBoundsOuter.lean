module

public import CORALean.NN.Operations.PropagateBounds
public import CORALean.NN.Theorems.EncloseOuter

@[expose] public section

/-!
# The propagated bounds contain the stretch's image
If `seg` is sound at `f` and the bounds `j` already held contain the image of `B`'s points
under `f`, which is what makes them bounds of that input, the propagated bounds contain it
too: the intersection of two outer sets is an outer set of the points in both. Outer, not
exact: the interval image through the stretch is an enclosure.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of `B` goes, under `f`, into the propagated bounds. -/
theorem NeuralNetwork.Encloses.propagateBounds_outer [Intersection (S m) (Vec ℝ m)]
    {seg : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m} (hf : seg.Encloses f) (B : S n)
    (stored : Option (S m))
    (hstored : ∀ I, stored = some I → ∀ x ∈ construct B, f x ∈ construct I) : -- --- STMT ---
    ∀ x ∈ construct B, f x ∈ construct (seg.propagateBounds B stored) := by -- --- PROOF ---
  intro x hx
  cases stored with
  | none => exact hf.enclose_outer B x hx
  | some I =>
      exact Intersection.intersection_outer _ _
        ⟨hf.enclose_outer B x hx, hstored I rfl x hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
