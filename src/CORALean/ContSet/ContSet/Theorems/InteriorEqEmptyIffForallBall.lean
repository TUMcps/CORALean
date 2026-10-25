module

public import CORALean.Global.EuclideanNorm
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Degenerate sets, by balls

[1, Def. 3]: a set is degenerate — has empty interior — exactly when no point of it carries a
Euclidean ball `s ⊕ B_ε` inside it. `Vec ℝ n` carries the supremum norm, so the Euclidean ball is
read through `toEuclidean`, a homeomorphism; any norm would give the same interior.

## Inputs
* `S` – set

## Hypotheses
* none

## Conclusion
* the interior is empty iff no point of `S` has a ball inside `S`

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral Operations
      in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for Continuous
      and Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point is interior exactly when some Euclidean ball around it stays inside. -/
theorem aux_mem_interior_iff (S : Set (Vec ℝ n)) (s : Vec ℝ n) : -- --- CONCL ---
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

theorem interior_eq_empty_iff_forall_ball (S : Set (Vec ℝ n)) : -- --- CONCL ---
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
