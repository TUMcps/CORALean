module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# A path from the interior to the outside meets the frontier

[1, Lemma A.1]: for `E` compact (closed is all that is used), `y ∈ int E`, `z ∉ E`, every
continuous path from `y` to `z` meets `∂E`. The proof is the paper's: the path's image is
connected, so it cannot lie in the disjoint open sets `int E` and `(closure E)ᶜ` once it
misses the frontier.

## Inputs
* `K` – closed set
* `w` – path

## Hypotheses
* `hK` – the set is closed
* `hw` – the path is continuous on the unit interval
* `h0` – the path starts in the interior
* `h1` – the path ends outside the set

## Conclusion
* the path meets the frontier at some time

## References

* [1] [A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued functions".
      Reliable Computing, 2010.](../../../references/2010/goldsztejn-rc-inner-range.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {E : Type*} [TopologicalSpace E]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma A.1]: a continuous path from `int K` to the outside of `K` meets `∂K`. -/
theorem path_meets_frontier {K : Set E} (hK : IsClosed K) {w : ℝ → E}
    (hw : ContinuousOn w (Icc 0 1)) (h0 : w 0 ∈ interior K) (h1 : w 1 ∉ K) : -- --- CONCL ---
    ∃ t ∈ Icc (0 : ℝ) 1, w t ∈ frontier K := by -- --- PROOF ---
  by_contra hno
  simp only [not_exists, not_and] at hno
  -- the image of the path is connected
  have hpc : IsPreconnected (w '' Icc 0 1) := isPreconnected_Icc.image w hw
  -- missing the frontier, it stays inside `int K`
  have hsub : w '' Icc 0 1 ⊆ interior K :=
    hpc.subset_of_closure_inter_subset isOpen_interior
      ⟨w 0, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, h0⟩ fun z hz => by
        obtain ⟨t, ht, rfl⟩ := hz.2
        by_contra hz'
        exact hno t ht ⟨subset_closure (closure_minimal interior_subset hK hz.1), hz'⟩
  exact h1 (interior_subset (hsub ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
