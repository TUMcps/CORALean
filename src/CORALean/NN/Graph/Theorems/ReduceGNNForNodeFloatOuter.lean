module

public import CORALean.NN.Graph.Operations.ReduceGNNForNodeFloat
public import CORALean.NN.Graph.Operations.Ball
public import CORALean.NN.Graph.Theorems.ReducedStepsFloatOuter
public import CORALean.NN.Graph.Operations.SupportFloat
public import CORALean.NN.Graph.Theorems.BallSubsetReduceKeepFloat

@[expose] public section

/-!
# The float reduced network encloses the whole-graph answer at `v`
For a float adjacency matrix `A` and an interval `P` containing its real message-passing matrix,
the interval `GNN.reduceGNNForNodeFloat` contains a real matrix each of whose rows naming `v`
is row `v` of the `L` message-passing steps on the whole graph, for any weights and features in
their intervals [1, §4.3]. The node sets come from `GNN.support A`, which misses no nonzero edge,
so no node the receptive field of `v` reads is dropped; the equality of the real reduced chain
(`GNN.reduceGNNForNode_exact`) is what the rows keep, the float products only widen them.

## Inputs
* `A` – float adjacency matrix
* `v` – node of interest
* `L` – number of steps
* `P` – interval message-passing matrix
* `W` – interval weights of the steps
* `Wr` – exact weights of the steps
* `Xi` – interval node-feature matrix
* `X` – exact node-feature matrix

## Hypotheses
* `hP` – interval contains the exact message-passing matrix
* `hW` – each interval contains its exact weights
* `hX` – interval contains the exact features

## Conclusion
* some matrix in the float result has the exact chain's row at the node

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open FloatOps
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N : ℕ}

/-- A nonzero entry is on the float support. -/
private theorem GNN.aux_support_of_ne_zero (A : Mat 𝕋 N N) (i j : Fin N)
    (h : toReal (A i j) ≠ 0) : -- --- CONCL ---
    GNN.support A i j = true := by -- --- PROOF ---
  by_contra hf
  have hb : (le (A i j) FloatOps.zero && le FloatOps.zero (A i j)) = true := by
    simpa [GNN.support] using hf
  rw [Bool.and_eq_true] at hb
  have h1 := toReal_le_of_le hb.1
  have h2 := toReal_le_of_le hb.2
  rw [toReal_zero] at h1 h2
  exact h (le_antisymm h1 h2)

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.reduceGNNForNodeFloat_outer (A : Mat 𝕋 N N) (v : Fin N) (L : ℕ)
    (P : Interval (Mat 𝕋 N N)) (hP : Real.GNN.messagePassing (toRealMat A) ∈ P.construct)
    (W : ℕ → Interval (Mat 𝕋 F F)) (Wr : ℕ → Mat ℝ F F) (hW : ∀ k, Wr k ∈ (W k).construct)
    (Xi : Interval (Mat 𝕋 N F)) (X : Mat ℝ N F) (hX : X ∈ Xi.construct) : -- --- CONCL ---
    ∃ Z ∈ (GNN.reduceGNNForNodeFloat A v L P W Xi).construct,
      ∀ a, (GNN.reduceKeepFloat (GNN.support A) v L L).orderEmbOfFin rfl a = v →
        Z a = Real.GNN.evalSteps (Real.GNN.messagePassing (toRealMat A)) L
          (fun i : Fin L => Wr i) X v := by -- --- PROOF ---
  have hE : ∀ i j, toRealMat A i j ≠ 0 → GNN.support A i j = true :=
    fun i j h => GNN.aux_support_of_ne_zero A i j h
  exact GNN.reducedStepsFloat_outer (toRealMat A) P hP v L
    (fun k => (GNN.reduceKeepFloat (GNN.support A) v L k).card)
    (fun k => (GNN.reduceKeepFloat (GNN.support A) v L k).orderEmbOfFin rfl)
    (fun k => (RelEmbedding.injective _))
    (fun k hk x hx => by
      have hx' := GNN.ball_subset_reduceKeepFloat (toRealMat A) (GNN.support A) hE v L k hk hx
      have : x ∈ Set.range ((GNN.reduceKeepFloat (GNN.support A) v L k).orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx'
      exact this)
    W Wr hW X _ _ (Interval.submatrix_mem hX _ id) (fun a _ => rfl)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
