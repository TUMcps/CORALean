import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadFrontPoint
import CORALean.NN.Graph.Theorems.EvalLayersMemGcnActSteps
import CORALean.NN.Graph.Theorems.MessagePassingEnclosureOuter

/-!
# The graph part of `Alg. 1` contains what the uncertain graph actually computes

[1, Thm. 1]: `gcnActSteps` at `P = 𝒫` of [1, Prop. 4] padded against the input set contains, for
every weighting of the uncertain edges and every point of the feature set, the layered iteration
that graph runs. `messagePassing_mem_enclosure` puts the graph's own `P` in `𝒫`,
`exists_point_of_q_zero` names the factors reaching it, and those sit beside the feature factors
on the one padded factor set, as in `evalSteps_mem_gcnSteps`, now with an activation after
each step.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: the graph's own layered iteration, at any admissible weighting and any point
of the feature set, lies in `gcnActSteps`. -/
theorem GNN.evalLayers_mem_gcnActSteps_uncertain (R : Relaxation ℝ) (hR : R.Sound invSqrt)
    (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) (hA : ∀ i j, 0 ≤ A i j) (lam : Fin m → ℝ)
    (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (L : ℕ) (c : ℕ → ℕ) (σ : ℕ → ℝ → ℝ)
    (W : ∀ s, Mat ℝ (c s) (c (s + 1))) (acts : ∀ s, GNN.ActLayer N (c (s + 1)))
    (hσ : ∀ s, (acts s).Sound (σ s)) (H : PolyZonotope (Mat ℝ N (c 0))) (aH : Fin H.p → ℝ)
    (haH : ∀ k, |aH k| ≤ 1) :
    GNN.evalLayers (GNN.messagePassing (GNN.adjAt A U lam)) L c σ W (H.point aH)
      ∈ (GNN.gcnActSteps L c W acts ((GNN.messagePassingEnclosure R A U).padBack H.p)
          (H.padFront (GNN.messagePassingEnclosure R A U).p) rfl).construct := by -- --- PROOF ---
  -- the enclosure keeps nothing independent, so a member of it is a point of it
  obtain ⟨aP, haP, hP⟩ := PolyZonotope.exists_point_of_q_zero (GNN.messagePassingEnclosure R A U)
    rfl (GNN.messagePassing_mem_enclosure R hR A U hA lam hlam)
  have hadm : ∀ k, |Fin.append aP aH k| ≤ 1 := by
    intro k
    refine Fin.addCases (fun e => ?_) (fun t => ?_) k
    · rw [Fin.append_left]
      exact haP e
    · rw [Fin.append_right]
      exact haH t
  refine GNN.evalLayers_mem_gcnActSteps L c σ W acts hσ _ _ rfl _ _ (Fin.append aP aH) hadm ?_ ?_
  · -- the joint vector's first half is the edge factors
    rw [PolyZonotope.padBack_point,
      show Fin.append aP aH ∘ Fin.castAdd H.p = aP from funext fun k => Fin.append_left aP aH k]
    exact hP.symm
  · rw [PolyZonotope.padFront_point]
    exact congrArg _ (funext fun k => Fin.append_right aP aH k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
