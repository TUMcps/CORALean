module

public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-!
# The boundary of the image is inside what encloses the image of the boundary

[1, Prop. 1]: an operator `reachSubset` enclosing the reachable set of every subset of `X₀`
(its (6), [2, Thm. 1]) encloses `∂R_{X₀}(t)` when applied to `∂X₀`. The proof is [1]'s, with
[1, Thm. 2] as `Homeomorph.image_frontier`: the flow at time `t` of a globally Lipschitz field
is a homeomorphism `φ`, and `R_{X₀}(t) = φ(X₀)`. `X₀` is closed, so that `∂X₀ ⊆ X₀` and (6)
applies to it; [1, Thm. 2] assumes it compact, Prop. 1 does not say so.

## Inputs
* `φ` – homeomorphism, the flow at the end time
* `X₀` – closed set of initial states
* `reachSubset` – operator enclosing reachable sets of subsets

## Hypotheses
* `hX₀` – the initial set is closed
* `h6` – the operator encloses the image of every subset of the initial set

## Conclusion
* the frontier of the image lies in the enclosure of the initial set's frontier

## References

* [1] N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets for
      Nonlinear Continuous Systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
* [2] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: `φ(X̂₀) ⊆ S(X̂₀)` for every `X̂₀ ⊆ X₀`, `X₀` closed, gives `∂φ(X₀) ⊆ S(∂X₀)`. -/
theorem frontier_image_subset_of_forall_subset (φ : X ≃ₜ Y) {X₀ : Set X} (hX₀ : IsClosed X₀)
    (reachSubset : Set X → Set Y) (h6 : ∀ Xs ⊆ X₀, φ '' Xs ⊆ reachSubset Xs) :
    frontier (φ '' X₀) ⊆ reachSubset (frontier X₀) := by
  rw [← φ.image_frontier]
  exact h6 _ hX₀.frontier_subset

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
