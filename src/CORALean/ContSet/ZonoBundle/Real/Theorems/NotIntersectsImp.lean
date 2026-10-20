module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Intersection detection: the printed converse is false

[1, Prop. 7] prints `Z_∩ ∩ S ≠ ∅ ↔ ∀ i, Zᵢ ∩ S ≠ ∅`; `IntersectsOfIntersects` is the `→`
that holds. `not_intersects_imp` is the `←` failing: `Z₁ = [0,1]`, `Z₂ = [2,3]` and
`S = [0,3]` in `ℝ`, each member meets `S`, the bundle is empty.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* every member can meet a set that the bundle misses

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The printed converse is false: the members meet `S` one by one, the bundle does not. -/
theorem ZonoBundle.not_intersects_imp : -- --- CONCL ---
    ∃ (zB : ZonoBundle ℝ) (S : Set ℝ),
      (∀ i, ((zB.Z i).construct ∩ S).Nonempty) ∧
        ¬ (zB.construct ∩ S).Nonempty := by -- --- PROOF ---
  let Z₁ : Zonotope ℝ := ⟨1, 1 / 2, fun _ => 1 / 2⟩
  let Z₂ : Zonotope ℝ := ⟨1, 5 / 2, fun _ => 1 / 2⟩
  refine ⟨⟨2, ![Z₁, Z₂]⟩, Set.Icc 0 3, ?_, ?_⟩
  · intro i
    fin_cases i
    · refine ⟨1 / 2, ⟨fun _ => 0, fun _ => by simp, by simp [Z₁]⟩, by norm_num, by norm_num⟩
    · refine ⟨5 / 2, ⟨fun _ => 0, fun _ => by simp, by simp [Z₂]⟩, by norm_num, by norm_num⟩
  · rintro ⟨x, hx, -⟩
    have h1 := SetIntersection.mem_construct_ofFn.mp hx 0
    have h2 := SetIntersection.mem_construct_ofFn.mp hx 1
    obtain ⟨β, hβ, e1⟩ := h1
    obtain ⟨γ, hγ, e2⟩ := h2
    have a := abs_le.mp (hβ ⟨0, Nat.one_pos⟩)
    have b := abs_le.mp (hγ ⟨0, Nat.one_pos⟩)
    have e1' : x = 1 / 2 + β ⟨0, Nat.one_pos⟩ * (1 / 2) := by
      rw [e1]; simp [Z₁]
    have e2' : x = 5 / 2 + γ ⟨0, Nat.one_pos⟩ * (1 / 2) := by
      rw [e2]; simp [Z₂]
    linarith [a.2, b.1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
