module

public import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsInterHyperplaneIff
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The printed scaled box is empty for a negative coefficient

[1, Sec. 6.3 (scaling)] allows every `βᵢ ≠ 0` and maps the box to `B⋆ = [0, β₁b₁] × … ×
[0, βₙbₙ]`. With `n = 1`, `b = 1`, `β = -1` and `α = -1/2`, the cut `{1/2}` has the vertex `1/2`,
while `[0, -1]`, its bounds crossed, holds no point at all: the solution `c⋆ = -1/2` lies
outside it. `Interval.mem_extremePoints_scale_iff` takes `[min(0, βᵢbᵢ), max(0, βᵢbᵢ)]`.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.scale_box_counterexample :
    let b : Vec ℝ 1 := fun _ => 1
    let β : Vec ℝ 1 := fun _ => -1
    (fun _ => (1 / 2 : ℝ)) ∈ Set.extremePoints ℝ
        ((⟨0, b⟩ : Interval (Vec ℝ 1)).construct ∩ Interval.hyperplane β (-1 / 2)) ∧
      (⟨0, fun i => β i * b i⟩ : Interval (Vec ℝ 1)).construct = ∅ := by -- --- PROOF ---
  intro b β
  refine ⟨?_, ?_⟩
  · -- in the box, on the plane, and on an edge, there being one coordinate only
    rw [Interval.mem_extremePoints_inter_hyperplane_iff (fun _ => by norm_num [β])]
    refine ⟨⟨fun i => ?_, ?_⟩, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
    · show (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1
      norm_num
    · show ∑ i : Fin 1, β i * (1 / 2 : ℝ) = -1 / 2
      norm_num [β]
  · -- `0 ≤ x ≤ -1` has no solution
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have h : (0 : ℝ) ≤ x 0 ∧ x 0 ≤ β 0 * b 0 := hx 0
    norm_num [β, b] at h
    linarith [h.1, h.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
