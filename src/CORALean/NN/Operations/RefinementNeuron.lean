module

public import CORALean.NN.Operations.Raise
public import CORALean.NN.Operations.RefinementRank
public import CORALean.NN.Operations.Sensitivity
public import CORALean.NN.Operations.WorstIndex
public import CORALean.Global.StepOf

@[expose] public section

/-!
# Which neuron to refine next

The paper's neuron-wise rule [1, Def. 4.4], CORA's `'neuron'` granularity: the best-ranked `(layer,
neuron)` pair names a layer, and every neuron of that layer whose rank clears `ω` times the best
rank moves up an order. At `ω = 1` that is the single best neuron, at `ω = 0` the whole layer, which
is [1, Def. 4.6]. `refinementRank` is read per neuron here, where `layerRank` folds it into
`‖σ_k‖₂`; by [1, Lemma 4.3] a layer costs no more generators than its largest order anyway. Nothing
here is proved and nothing here can be wrong: `encloseAt_outer` holds at every schedule, so `ω`, the
tie-break and the ranking are free.

## Inputs
* `sch` – schedule of order patterns
* `r` – rank of every neuron
* `ω` – fraction of the best rank a neuron must reach

## Output
* schedule with the selected neurons of the best layer raised by one

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The pair the rule refines at: the layer holding the best-ranked neuron, and
that neuron. Ties go to the earlier layer, then to the earlier neuron. -/
@[step_of Schedule.refineWorstNeurons]
noncomputable def step_worstNeuron (r : Fin (k + 1) → Fin (n + 1) → ℝ) :
    Fin (k + 1) × Fin (n + 1) :=
  let l := worstIndex fun i => Finset.univ.sup' Finset.univ_nonempty (r i)
  (l, worstIndex (r l))

/-- The order each neuron of that layer gains [1, Eq. 27]: one where its rank
clears `ω` times the best, none elsewhere and none outside the layer. -/
@[step_of Schedule.refineWorstNeurons]
noncomputable def step_neuronwiseStep (r : Fin (k + 1) → Fin (n + 1) → ℝ) (ω : ℝ) :
    ℕ → ℕ :=
  fun j => if h : j < n + 1 then
      (if ω * r (step_worstNeuron r).1 (step_worstNeuron r).2
          ≤ r (step_worstNeuron r).1 ⟨j, h⟩ then 1 else 0)
    else 0


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Neuron `j`'s own rank at what CORA backpropagates, left unaggregated: this
rule ranks `(layer, neuron)` pairs and never layers. -/
private noncomputable def Chain.aux_neuronRank (c : Chain n m) (x d : Vec ℝ n)
    (j : Fin n) : ℝ := refinementRank (c.sensitivity x) d j


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The neuron-wise rule itself [1, Def. 4.4]: those neurons, in the layer the
best rank names, each moving up one order. -/
noncomputable def Schedule.refineWorstNeurons (sch : Schedule)
    (r : Fin (k + 1) → Fin (n + 1) → ℝ) (ω : ℝ) : Schedule :=
  Schedule.raise sch (step_worstNeuron r).1 (step_neuronwiseStep r ω)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
