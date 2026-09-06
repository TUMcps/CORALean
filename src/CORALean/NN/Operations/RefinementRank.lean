import CORALean.NN.Operations.Schedule
import CORALean.NN.Operations.Sensitivity

/-!
# Which layer to refine next

The paper's heuristic [1]: a neuron's own approximation error, weighted by its
column of the backpropagated Jacobian. A neuron with a large error the output
barely sees is not worth an order, and one with a small error it magnifies is.

Nothing here is proved and nothing here can be wrong. `propagateAt_outer` holds
at *every* schedule, so this file only decides where the next order is spent —
the same freedom `reduceBy_outer` has at every partition. The column norm, the
aggregate and the tie-break are therefore all free, each taken at its cheapest.

`refinementRank` is a rank per neuron and `layerRank` sums it, which is what the
layer-wise rule [1, Def. 4.6] ranks over. [1, Eq. 28] and CORA's `norm(...)` take
the 2-norm of those ranks instead; the aggregate only has to order layers, so
which of the two is used is free. `Operations.RefinementNeuron` is the
neuron-wise rule [1, Def. 4.4], reading `refinementRank` unaggregated.

`worstIndex` sorts on the negated rank: `Tuple.sort` is total, so `0` is largest.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}

/-- Neuron `j`'s share of the output's error: its column of the sensitivity,
summed in magnitude, against the error its own relaxation leaves. -/
def refinementRank (J : Mat ℝ m n) (d : Vec ℝ n) (j : Fin n) : ℝ :=
  (∑ i, |J i j|) * |d j|

/-- A layer's own rank, its neurons' summed: what the layer-wise rule ranks
layers by, the neurons of the layer it names all moving together. -/
def layerRank (J : Mat ℝ m n) (d : Vec ℝ n) : ℝ := ∑ j, refinementRank J d j

/-- The rank at what CORA actually backpropagates: the network's sensitivity at
a point of the input set, weighing the errors the layer's relaxation leaves. -/
noncomputable def NeuralNetwork.layerRank (nn : NeuralNetwork S n m) (x d : Vec ℝ n) : ℝ :=
  _root_.CORALean.Real.layerRank (nn.sensitivity x) d

/-- The largest-ranked of `k + 1` candidates, ties to the earlier one, which is
what `Tuple.sort` gives at index `0`. -/
noncomputable def worstIndex (r : Fin (k + 1) → ℝ) : Fin (k + 1) :=
  (Tuple.sort fun l => -r l) 0

/-- The layer the layer-wise rule refines next [1, Def. 4.6]: the largest
`layerRank` of `k + 1` layers. -/
noncomputable def worstLayer (r : Fin (k + 1) → ℝ) : Fin (k + 1) := worstIndex r

/-- The layer-wise rule [1, Def. 4.6]: every neuron of the worst-ranked of
`k + 1` layers moves up an order. -/
noncomputable def Schedule.refineWorst (sch : Schedule) (r : Fin (k + 1) → ℝ) : Schedule :=
  Schedule.refineLayer sch (worstLayer r)

end CORALean.Real
