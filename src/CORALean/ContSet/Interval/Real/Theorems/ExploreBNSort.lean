module

public import CORALean.ContSet.Interval.Real.Theorems.ExploreBNEqExtremePoints
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# Sorting the box first makes `EXPLORE BN` complete

The repair of [1, Sec. 6.3 (general problem)]: before [1, Alg. 2], permute the coordinates so
that the upper corner is ordered, `σ = Tuple.sort b`, and permute the solutions back. Then the
output is exactly the set of vertices of the cut, for any box `[0, b₁] × … × [0, bₙ]` with
positive sides and `0 ≤ α`: a permutation of coordinates maps the box, the plane `Σᵢ xᵢ = α`
and the edges onto themselves. Translation and scaling, the paper's two mappings, reduce any
box to this one.

## Inputs
* `b` – upper bound vector
* `α` – level of the plane

## Hypotheses
* `hb0` – bounds positive
* `hα` – level nonnegative

## Conclusion
* the vertices of the cut are the permuted result of the algorithm on the sorted box

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection Problem".
      INFOCOMP Journal of Computer Science, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.exploreBN_sort {b : Vec ℝ n} {α : ℝ} (hb0 : ∀ i, 0 < b i)
    (hα : 0 ≤ α) : -- --- CONCL ---
    Set.extremePoints ℝ ((⟨0, b⟩ : Interval (Vec ℝ n)).construct ∩ Interval.hyperplane 1 α) =
      (fun y : Vec ℝ n => fun i => y ((Tuple.sort b).symm i)) ''
        ↑(Interval.exploreBN (fun i => b (Tuple.sort b i)) α) := by -- --- PROOF ---
  set σ := Tuple.sort b
  have hmono : Monotone fun i => b (σ i) := Tuple.monotone_sort b
  rw [Interval.exploreBN_eq_extremePoints hmono (fun i => hb0 _) hα]
  ext x
  rw [Interval.mem_extremePoints_inter_hyperplane_iff (a := 1) (fun _ => by simp)]
  constructor
  · -- `x ∘ σ` is a vertex of the sorted cut, and maps back to `x`
    rintro ⟨⟨hxB, hxP⟩, hedge⟩
    refine ⟨fun i => x (σ i), ?_, funext fun i => by simp⟩
    rw [Interval.mem_extremePoints_inter_hyperplane_iff (a := 1) (fun _ => by simp)]
    refine ⟨⟨fun i => hxB (σ i), ?_⟩, fun i j hij => hedge (σ i) (σ j) (σ.injective.ne hij)⟩
    have h : ∑ i, x i = α := by simpa [Interval.hyperplane] using hxP
    simpa [Interval.hyperplane, Equiv.sum_comp σ x] using h
  -- a vertex of the sorted cut, permuted back, is a vertex of the cut
  · rintro ⟨y, hy, rfl⟩
    rw [Interval.mem_extremePoints_inter_hyperplane_iff (a := 1) (fun _ => by simp)] at hy
    obtain ⟨⟨hyB, hyP⟩, hedge⟩ := hy
    refine ⟨⟨fun i => ?_, ?_⟩, fun i j hij => ?_⟩
    · have h : 0 ≤ y (σ.symm i) ∧ y (σ.symm i) ≤ b (σ (σ.symm i)) := hyB (σ.symm i)
      rw [Equiv.apply_symm_apply] at h
      exact h
    · have h : ∑ i, y i = α := by simpa [Interval.hyperplane] using hyP
      simpa [Interval.hyperplane, Equiv.sum_comp σ.symm y] using h
    · have h := hedge (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij)
      change ((y (σ.symm i) = 0 ∨ y (σ.symm i) = b (σ (σ.symm i))) ∨
        (y (σ.symm j) = 0 ∨ y (σ.symm j) = b (σ (σ.symm j)))) at h
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
