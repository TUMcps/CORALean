import CORALean.NN.Layers.Definitions.ApproxError
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The approximation errors enclose the activation

[1, Def. 6]: `ϕ([l,u]) ⊆ p(x) ⊕ [e_low, e_up]`: at every `x ∈ [l, u]` the distance `ϕ(x) - p(x)`
lies in `[e_low, e_up]`, the least and greatest it takes there. Needs `ϕ - p` continuous on
`[l, u]`, which makes the image compact and so bounded, the infimum and supremum then being its
bounds.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem approxError_enclosure (ϕ p : ℝ → ℝ) (l u : ℝ)
    (hc : ContinuousOn (fun x => ϕ x - p x) (Set.Icc l u)) (x : ℝ) (hx : x ∈ Set.Icc l u) :
    approxErrorLow ϕ p l u ≤ ϕ x - p x ∧ ϕ x - p x ≤ approxErrorUp ϕ p l u := by
  have hK := isCompact_Icc.image_of_continuousOn hc
  exact ⟨csInf_le hK.bddBelow ⟨x, hx, rfl⟩, le_csSup hK.bddAbove ⟨x, hx, rfl⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
