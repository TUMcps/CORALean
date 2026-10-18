module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PadFrontPoint
public import CORALean.NN.Graph.Theorems.GcnStepsExact
public import CORALean.NN.Graph.Theorems.MessagePassingEnclosureOuter

@[expose] public section

/-!
# A chain of steps contains what the graph actually computes

The statement a caller of [1] wants over several message-passing steps: whatever
the uncertain edges weigh, the iteration `H ↦ P H W_k` that *that* graph runs,
started at any point of the node-feature set, is a point of `gcnSteps`.

The pieces are the ones the one-step version used. `messagePassing_mem_enclosure`
puts the graph's own `P` in `𝒫`, `exists_point_of_q_zero` names the factors
reaching it, and `Fin.append` puts those beside the feature factors on the one
padded factor set `gcnSteps` then keeps for every step.

Padding once, before the chain, is the whole point: the edges and the features
are independent only at the *first* step, and every later step reads the edge
factors it was handed, so an edge weighs the same at each of them.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Several message-passing steps at an uncertain graph are sound: the graph's
own iteration, at any point of the feature set, lies in the chain. -/
theorem GNN.evalSteps_mem_gcnSteps (R : Relaxation ℝ) (hR : R.Sound invSqrt) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (hA : ∀ i j, 0 ≤ A i j) (lam : Fin m → ℝ)
    (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (L : ℕ) (W : Fin (L + 1) → Mat ℝ F F)
    (H : PolyZonotope (Mat ℝ N F)) (aH : Fin H.p → ℝ) (haH : ∀ k, |aH k| ≤ 1) : -- --- STMT ---
    GNN.evalSteps (GNN.messagePassing (GNN.adjAt A U lam)) (L + 1) W (H.point aH)
      ∈ (GNN.gcnSteps ((GNN.messagePassingEnclosure R A U).padBack H.p) (L + 1) W
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
  -- the joint vector's two halves are the edge factors and the feature factors
  have hleft : ((GNN.messagePassingEnclosure R A U).padBack H.p).point (Fin.append aP aH)
      = GNN.messagePassing (GNN.adjAt A U lam) := by
    rw [PolyZonotope.padBack_point,
      show Fin.append aP aH ∘ Fin.castAdd H.p = aP from funext fun k => Fin.append_left aP aH k]
    exact hP.symm
  have hright : (H.padFront (GNN.messagePassingEnclosure R A U).p).point (Fin.append aP aH)
      = H.point aH := by
    rw [PolyZonotope.padFront_point]
    exact congrArg _ (funext fun k => Fin.append_right aP aH k)
  -- the chain over the padded sets is exactly the iteration over that vector
  rw [← GNN.gcnSteps_exact ((GNN.messagePassingEnclosure R A U).padBack H.p) L W
    (H.padFront (GNN.messagePassingEnclosure R A U).p) rfl]
  refine ⟨Fin.append aP aH, hadm, ?_⟩
  show GNN.evalSteps (((GNN.messagePassingEnclosure R A U).padBack H.p).point (Fin.append aP aH))
      (L + 1) W ((H.padFront (GNN.messagePassingEnclosure R A U).p).point (Fin.append aP aH))
    = GNN.evalSteps (GNN.messagePassing (GNN.adjAt A U lam)) (L + 1) W (H.point aH)
  rw [hleft, hright]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
