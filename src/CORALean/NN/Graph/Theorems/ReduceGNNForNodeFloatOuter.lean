module

public import CORALean.NN.Graph.Operations.ReduceGNNForNodeFloat
public import CORALean.NN.Graph.Theorems.BallSubsetReduceKeepFloat
public import CORALean.NN.Graph.Theorems.ReducedStepsFloatOuter
public import CORALean.NN.Graph.Theorems.SupportFloatOfNeZero

@[expose] public section

/-!
# The float reduced network encloses the whole-graph answer at `v`
For a float adjacency matrix `A` and an interval `P` containing its real message-passing matrix,
the interval `GNN.reduceGNNForNodeFloat` contains a real matrix each of whose rows naming `v`
is row `v` of the `L` message-passing steps on the whole graph, for any weights and features in
their intervals [1, §4.3]. The node sets come from `GNN.support A`, which misses no nonzero edge,
so no node the receptive field of `v` reads is dropped; the equality of the real reduced chain
(`GNN.reduceGNNForNode_exact`) is what the rows keep, the float products only widen them.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F : ℕ}


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
    fun i j h => GNN.support_of_ne_zero A i j h
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
