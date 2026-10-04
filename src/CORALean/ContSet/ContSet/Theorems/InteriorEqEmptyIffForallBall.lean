import CORALean.Global.EuclideanNorm
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Degenerate sets, by balls

[1, Def. 3]: a set is degenerate — has empty interior — exactly when no point of it carries a
Euclidean ball `s ⊕ B_ε` inside it. `Vec ℝ n` carries the supremum norm, so the Euclidean ball is
read through `toEuclidean`, a homeomorphism; any norm would give the same interior.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point is interior exactly when some Euclidean ball around it stays inside. -/
theorem aux_mem_interior_iff (S : Set (Vec ℝ n)) (s : Vec ℝ n) :
    s ∈ interior S ↔ ∃ ε > 0, ∀ x : Vec ℝ n, ‖x‖₂ ≤ ε → s + x ∈ S := by -- --- PROOF ---
  rw [mem_interior_iff_mem_nhds]
  -- the neighbourhoods of `s` are those of its Euclidean copy, pulled back
  have hc : 𝓝 s = comap toEuclidean (𝓝 (toEuclidean s)) := by
    have := (toEuclidean (n := n)).toHomeomorph.comap_nhds_eq (toEuclidean s)
    simpa using this.symm
  rw [hc, ((Metric.nhds_basis_closedBall (x := toEuclidean s)).comap _).mem_iff]
  refine exists_congr fun ε => and_congr_right fun _ => ?_
  constructor
  · intro h x hx
    apply h
    show dist (toEuclidean (s + x)) (toEuclidean s) ≤ ε
    rw [dist_eq_norm, map_add, add_sub_cancel_left, norm_toEuclidean]
    exact hx
  · intro h y hy
    have hy' : dist (toEuclidean y) (toEuclidean s) ≤ ε := hy
    rw [dist_eq_norm, ← map_sub, norm_toEuclidean] at hy'
    have := h (y - s) hy'
    rwa [add_sub_cancel] at this


-- =======================================  MAIN THEOREM  ======================================= --

theorem interior_eq_empty_iff_forall_ball (S : Set (Vec ℝ n)) :
    interior S = ∅ ↔ ∀ s ∈ S, ∀ ε > 0, ¬ ∀ x : Vec ℝ n, ‖x‖₂ ≤ ε → s + x ∈ S := by -- --- PROOF ---
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h s _ ε hε hball
    exact h s ((aux_mem_interior_iff S s).mpr ⟨ε, hε, hball⟩)
  · intro h s hs
    obtain ⟨ε, hε, hball⟩ := (aux_mem_interior_iff S s).mp hs
    exact h s (interior_subset hs) ε hε hball

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
