import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.NN.Graph.Theorems.ConvUncertainExact
import CORALean.NN.Graph.Theorems.MessagePassingEnclosureOuter

/-!
# The uncertain-graph layer contains what the graph actually computes

The composite, and the statement a caller of [1] wants: whatever the uncertain
edges weigh, the layer `P H W` that *that* graph computes at any point of the
node-feature set is a point of `gcnUncertain W 𝒫 H`.

Two facts and one factor vector. `messagePassing_mem_enclosure` puts the graph's
own message passing in `𝒫`, and `𝒫` has no independent generators, so
`exists_point_of_q_zero` names the factors reaching it; `gcnUncertain_exact`
then asks only for the two halves side by side, which `Fin.append` supplies.

That the halves may be chosen independently is exactly what padding bought: the
edges and the node features are separate factors, so no choice of one restricts
the other, and the only approximation left in the composite is the one
`messagePassing_mem_enclosure` already paid.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1]'s uncertain-graph convolution is sound: at admissible edge weights and
any point of the node-feature set, the graph's own `P H W` lies in it. -/
theorem GNN.gcn_mem_gcnUncertain (R : Relaxation invSqrt) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (hA : ∀ i j, 0 ≤ A i j) (lam : Fin m → ℝ)
    (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (W : Mat ℝ F₁ F₂) (H : PolyZonotope (Mat ℝ N F₁))
    (aH : Fin H.p → ℝ) (haH : ∀ k, |aH k| ≤ 1) :
    GNN.messagePassing (GNN.adjAt A U lam) * H.point aH * W
      ∈ (GNN.gcnUncertain W (GNN.messagePassingEnclosure R A U) H).construct := by -- --- PROOF ---
  -- the enclosure keeps nothing independent, so a member of it is a point of it
  obtain ⟨aP, haP, hP⟩ := PolyZonotope.exists_point_of_q_zero (GNN.messagePassingEnclosure R A U)
    rfl (GNN.messagePassing_mem_enclosure R A U hA lam hlam)
  have hadm : ∀ k, |Fin.append aP aH k| ≤ 1 := by
    intro k
    refine Fin.addCases (fun e => ?_) (fun t => ?_) k
    · rw [Fin.append_left]
      exact haP e
    · rw [Fin.append_right]
      exact haH t
  -- the two halves of the joint vector are the two sets' own factors again
  have hleft : Fin.append aP aH ∘ Fin.castAdd H.p = aP := funext fun k => Fin.append_left aP aH k
  have hright : Fin.append aP aH ∘ Fin.natAdd (GNN.messagePassingEnclosure R A U).p = aH :=
    funext fun k => Fin.append_right aP aH k
  rw [← GNN.gcnUncertain_exact W (GNN.messagePassingEnclosure R A U) H]
  refine ⟨Fin.append aP aH, hadm, ?_⟩
  show (GNN.messagePassingEnclosure R A U).point (Fin.append aP aH ∘ Fin.castAdd H.p)
      * H.point (Fin.append aP aH ∘ Fin.natAdd (GNN.messagePassingEnclosure R A U).p) * W
    = GNN.messagePassing (GNN.adjAt A U lam) * H.point aH * W
  rw [hleft, hright, hP]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
