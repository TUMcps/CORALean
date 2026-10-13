module

public import CORALean.NN.Operations.Enclose

@[expose] public section

/-!
# Propagating a layer's bounds to the next activation layer
CORA's `propagateBounds(obj, i)` takes the bounds `[l, u]` stored in activation layer `i`,
evaluates the interval image through layer `i` and the layers after it up to the next
activation layer `j`, and stores in `j` that image, or its intersection with the bounds `j`
already holds. `seg` is that stretch of layers (layer `i` to the one before `j`), an ordinary
network; finding `j` and the option gates (`propagate_bounds`, `reuse_bounds`, empty or `NaN`
bounds) are the caller's. The store into `layer_j.l`, `layer_j.u` is the returned set.
Generic in the representation: at the intervals of either layer it is CORA's.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The new bounds of layer `j`: the image of `B` through `seg`, met with the bounds `j` held. -/
def NeuralNetwork.propagateBounds [Intersection (S m) (Vec ℝ m)] (seg : NeuralNetwork S n m)
    (B : S n) : Option (S m) → S m
  | none => seg.enclose B
  | some stored => Intersection.intersection (seg.enclose B) stored

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
