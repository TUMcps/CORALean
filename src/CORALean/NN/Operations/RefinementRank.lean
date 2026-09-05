import CORALean.NN.Operations.Schedule
import CORALean.NN.Operations.Sensitivity

/-!
# Which layer to refine next

The paper's heuristic [1]: a neuron's own approximation error, weighted by how
far the rest of the network moves that neuron — its column of the backpropagated
Jacobian. A neuron with a large error the output barely sees is not worth an
order, and one with a small error the output magnifies is.

Nothing here is proved and nothing here can be wrong. `propagateAt_outer` holds
at *every* schedule, so this file only decides where the next order is spent —
the same freedom `reduceBy_outer` has at every partition. The column norm, the
aggregate over a layer's neurons and the tie-break are therefore all free, and
each is taken at its cheapest.

`worstLayer` sorts on the negated rank, which is `reduce`'s own idiom for
ordering by a real: `Tuple.sort` is total and `0` is then the largest.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}

/-- Neuron `j`'s share of the output's error: its column of the sensitivity,
summed in magnitude, against the error its own relaxation leaves. -/
def refinementRank (J : Mat ℝ m n) (d : Vec ℝ n) (j : Fin n) : ℝ :=
  (∑ i, |J i j|) * |d j|

/-- A layer's own rank, its neurons' summed. A layer is refined as a whole here,
so the aggregate only has to order layers. -/
def layerRank (J : Mat ℝ m n) (d : Vec ℝ n) : ℝ := ∑ j, refinementRank J d j

/-- The rank at what CORA actually backpropagates: the network's sensitivity at
a point of the input set, weighing the errors the layer's relaxation leaves. -/
noncomputable def NeuralNetwork.layerRank (nn : NeuralNetwork S n m) (x d : Vec ℝ n) : ℝ :=
  _root_.CORALean.Real.layerRank (nn.sensitivity x) d

/-- The layer the heuristic refines next: the largest rank, ties to the earlier
layer, which is what `Tuple.sort` gives at index `0`. -/
noncomputable def worstLayer (r : Fin (k + 1) → ℝ) : Fin (k + 1) :=
  (Tuple.sort fun l => -r l) 0

/-- One step of the loop at the heuristic: the worst-ranked of `k + 1` layers
moves up a level. -/
noncomputable def Schedule.refineWorst (sch : Schedule) (r : Fin (k + 1) → ℝ) : Schedule :=
  Schedule.refine sch (worstLayer r)

end CORALean.Real
