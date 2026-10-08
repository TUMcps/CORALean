import CORALean.NN.Operations.Raise
import CORALean.NN.Operations.RefinementRank
import CORALean.NN.Operations.Sensitivity
import CORALean.NN.Operations.WorstIndex

/-!
# Which neuron to refine next

The paper's neuron-wise rule [1, Def. 4.4], CORA's `'neuron'` granularity: the
best-ranked `(layer, neuron)` pair names a layer, and every neuron of that layer
whose rank clears `ω` times the best rank moves up an order. At `ω = 1` that is
the single best neuron, at `ω = 0` the whole layer, which is [1, Def. 4.6].

`refinementRank` is read per neuron here, where `layerRank` folds it into `‖σ_k‖₂`. The
norm orders layers and cannot say which neuron inside one deserves the order; by
[1, Lemma 4.3] a layer costs no more generators than its largest order anyway,
so the two rules differ in the time spent and not in the size of the set.

Nothing here is proved and nothing here can be wrong: `encloseAt_outer` holds
at every schedule, so `ω`, the tie-break and the ranking are free. The layers
are ranked at one width, a `Schedule` being indexed by plain ℕ.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Neuron `j`'s own rank at what CORA backpropagates, left unaggregated: this
rule ranks `(layer, neuron)` pairs and never layers. -/
noncomputable def Chain.aux_neuronRank (c : Chain n m) (x d : Vec ℝ n)
    (j : Fin n) : ℝ := refinementRank (c.sensitivity x) d j

/-- The pair the rule refines at: the layer holding the best-ranked neuron, and
that neuron. Ties go to the earlier layer, then to the earlier neuron. -/
noncomputable def aux_worstNeuron (r : Fin (k + 1) → Fin (n + 1) → ℝ) :
    Fin (k + 1) × Fin (n + 1) :=
  let l := worstIndex fun i => Finset.univ.sup' Finset.univ_nonempty (r i)
  (l, worstIndex (r l))

/-- The order each neuron of that layer gains [1, Eq. 27]: one where its rank
clears `ω` times the best, none elsewhere and none outside the layer. -/
noncomputable def aux_neuronwiseStep (r : Fin (k + 1) → Fin (n + 1) → ℝ) (ω : ℝ) :
    ℕ → ℕ :=
  fun j => if h : j < n + 1 then
      (if ω * r (aux_worstNeuron r).1 (aux_worstNeuron r).2
          ≤ r (aux_worstNeuron r).1 ⟨j, h⟩ then 1 else 0)
    else 0


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The neuron-wise rule itself [1, Def. 4.4]: those neurons, in the layer the
best rank names, each moving up one order. -/
noncomputable def Schedule.refineWorstNeurons (sch : Schedule)
    (r : Fin (k + 1) → Fin (n + 1) → ℝ) (ω : ℝ) : Schedule :=
  Schedule.raise sch (aux_worstNeuron r).1 (aux_neuronwiseStep r ω)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
