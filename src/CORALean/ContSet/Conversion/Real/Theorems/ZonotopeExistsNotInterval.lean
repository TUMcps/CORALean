module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A zonotope that is no box

The box is a zonotope (`Interval.zonotope_exact`), and the inclusion is strict: the diagonal segment
`{t (1, 1) | t ∈ [-1, 1]}` is a zonotope, and no box has it as its set, since a box containing the
two ends of the segment contains the corner `(1, -1)`, which the segment does not.

This is the arrow from intervals to zonotopes of [1, Fig. 1 (Intervals → Zonotopes)].

## Inputs
* none

## Hypotheses
* none

## Conclusion
* some planar zonotope is no interval

## References

* [1] [N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set Representation for
      Reachability Analysis". IEEE Transactions on Automatic Control,
      2021.](../../../../../../references/2021/kochdumper-tac-sparse-polyzonotopes.md)

-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.exists_not_interval : -- --- CONCL ---
    ∃ Z : Zonotope (Vec ℝ 2),
      ¬ ∃ I : Interval (Vec ℝ 2), I.construct = Z.construct := by -- --- PROOF ---
  refine ⟨⟨1, 0, fun _ => fun _ => 1⟩, ?_⟩
  rintro ⟨I, hI⟩
  -- the two ends of the segment are in the box
  have hend : ∀ t : ℝ, |t| ≤ 1 → (fun _ => t : Vec ℝ 2) ∈ I.construct := fun t ht =>
    hI ▸ ⟨fun _ => t, fun _ => ht, funext fun i => by simp⟩
  have h1 := hend 1 (by norm_num)
  have h2 := hend (-1) (by norm_num)
  -- so is the corner `(1, -1)`, coordinate by coordinate
  have hcorner : (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1 : Vec ℝ 2) ∈ I.construct :=
    fun i => by
    have a : I.inf i ≤ 1 ∧ 1 ≤ I.sup i := h1 i
    have b : I.inf i ≤ -1 ∧ -1 ≤ I.sup i := h2 i
    fin_cases i
    · exact a
    · exact b
  obtain ⟨β, hβ, hx⟩ := hI ▸ hcorner
  have e0 := congrFun hx 0
  have e1 := congrFun hx 1
  simp at e0 e1
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
