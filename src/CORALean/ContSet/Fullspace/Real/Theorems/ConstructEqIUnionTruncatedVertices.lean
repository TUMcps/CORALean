module

public import CORALean.ContSet.Fullspace.Real.Operations.TruncatedVertices
public import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope

@[expose] public section

/-!
# The full space is the union of its truncated vertex hulls

Every point of `ℝ^n` lies in the hull of the corners of some box `[-t, t]^n`, namely any `t`
bounding its coordinates, and the truncated vertices are those corners (`⊤ ↦ t`, `⊥ ↦ -t`).
Exact: the hull of any truncation is inside the space. This is what the infinite columns of
`Fullspace.vertices` stand for: the space has no vertices, and its exhausting boxes' vertices
tend to them.

Source: [1].

## References

* [1] `contSet/@fullspace/vertices_.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.construct_eq_iUnion_truncatedVertices (F : Fullspace (n + 1)) :
    F.construct = ⋃ t : ℝ, (F.truncatedVertices t).construct := by -- --- PROOF ---
  refine Set.eq_of_subset_of_subset (fun x _ => ?_) (fun _ _ => Set.mem_univ _)
  rw [Set.mem_iUnion]
  set t : ℝ := ∑ j, |x j| with ht
  -- the box `[-t, t]`, whose corners are the truncated vertices
  have hbox : x ∈ (Interval.mk (fun _ : Fin (n + 1) => -t) (fun _ => t)).construct := by
    intro j
    have : |x j| ≤ t := Finset.single_le_sum (f := fun j => |x j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
    exact abs_le.mp this
  refine ⟨t, ?_⟩
  have hV : F.truncatedVertices t =
      (Interval.mk (fun _ : Fin (n + 1) => -t) (fun _ => t)).vPolytope := by
    unfold Fullspace.truncatedVertices Interval.vPolytope
    congr 1
    funext l j
    simp [Fullspace.vertices, Interval.corner]
  rw [hV]
  exact Interval.vPolytope_contains _ hbox

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
