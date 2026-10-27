module

public import CORALean.ContSet.Zonotope.Real.Theorems.EdgeNotMemInterior
public import CORALean.ContSet.Zonotope.Real.Theorems.MemWalkEdgesIff
public import CORALean.ContSet.Zonotope.Real.Theorems.CornerSuccAdd
public import CORALean.ContSet.Zonotope.Real.Theorems.CornerNotSuccSub
public import CORALean.ContSet.Zonotope.Real.Theorems.WalkEdgesSubsetConstruct
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# The walk edges are on the boundary

For nonzero generators sorted by angle, no point of a walk edge is interior: the zonogon is on one
side of each edge's line (`edge_not_mem_interior`), in the first block of the walk with the
sorted order and in the second with the order reversed (`σ = -1`). With the converse
(`frontier_subset_walkEdges`) the boundary of the zonogon is the union of the two chains
[1, Alg. 3] scans. A zero generator gives a degenerate edge, a point, which is on the boundary
too but is not covered by a line.

## Inputs
* `Z` – planar zonotope

## Hypotheses
* `h2` – generators sorted by angle
* `hne` – generators nonzero

## Conclusion
* the walk edges lie on the frontier

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.walkEdges_subset_frontier (Z : Zonotope (Vec ℝ 2))
    (h2 : ∀ i j : Fin Z.h, i < j → 0 ≤ Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0)
    (hne : ∀ j, Z.G j ≠ 0) : -- --- CONCL ---
    Z.walkEdges ⊆ frontier Z.construct := by -- --- PROOF ---
  intro x hx
  refine ⟨subset_closure (Z.walkEdges_subset_construct hx), ?_⟩
  obtain ⟨k, hk | hk⟩ := (Z.mem_walkEdges_iff x).mp hx
  · -- the first block: the walk up the chain, `σ = 1`
    rw [Z.corner_succ_add] at hk
    refine Z.edge_not_mem_interior (σ := 1) (Or.inl rfl) (fun j => decide (j.val < k.val)) k
      (by simp) (fun b hb => ?_) (fun c hc hck => ?_) (hne k) hk
    · have : b < k := Fin.lt_def.mpr (by simpa using hb)
      simpa using h2 b k this
    · have : k < c := lt_of_le_of_ne (not_lt.mp (Fin.lt_def.not.mpr (by simpa using hc)))
        (Ne.symm hck)
      simpa using h2 k c this
  · -- the second block: the walk down the chain, `σ = -1`
    have hend := Z.corner_not_succ_sub k
    have hseg : x ∈ segment ℝ (Z.corner fun j => !decide (j.val < k.val + 1))
        ((Z.corner fun j => !decide (j.val < k.val + 1)) + (2 : ℝ) • Z.G k) := by
      have hA : (Z.corner fun j => !decide (j.val < k.val + 1)) + (2 : ℝ) • Z.G k
          = Z.corner fun j => !decide (j.val < k.val) := by rw [hend]; abel
      rw [hA, segment_symm]
      exact hk
    refine Z.edge_not_mem_interior (σ := -1) (Or.inr rfl) (fun j => !decide (j.val < k.val + 1)) k
      (by simp) (fun b hb => ?_) (fun c hc hck => ?_) (hne k) hseg
    · have : k < b := Fin.lt_def.mpr (by simpa using hb)
      have := h2 k b this
      linarith
    · have hle : c ≤ k := by simpa [Nat.lt_succ_iff] using hc
      have := h2 c k (lt_of_le_of_ne hle hck)
      linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
