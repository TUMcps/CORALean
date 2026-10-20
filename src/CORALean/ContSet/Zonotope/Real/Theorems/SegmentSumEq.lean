module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Definitions.SegmentSum
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The sum with a segment, parametrized

[1, Eq. 12]: for a convex `A`, `A ⊕ x = {a + αx | a ∈ A, α ∈ [0, 1]}`. The right side is
convex and holds `A` (at `α = 0`) and `A + x` (at `α = 1`), so it holds the hull; and
`a + αx = (1 − α) a + α (a + x)` is in the hull. The paper states it without proof.

## Inputs
* `A` – convex set
* `x` – vector

## Hypotheses
* `hA` – `A` convex

## Conclusion
* the segment sum is the set of `a` plus multiples of `x`

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 12]: for convex `A`, `A ⊕ x = {a + αx | a ∈ A, α ∈ [0, 1]}`. -/
theorem Zonotope.segmentSum_eq {A : Set (Vec ℝ n)} (hA : Convex ℝ A)
    (x : Vec ℝ n) : -- --- CONCL ---
    Zonotope.segmentSum A x
      = {y | ∃ a ∈ A, ∃ t ∈ Set.Icc (0:ℝ) 1, y = a + t • x} := by -- --- PROOF ---
  unfold Zonotope.segmentSum
  apply Set.Subset.antisymm
  · -- the right side is convex and holds `A` and `A + x`, so it holds the hull
    refine convexHull_min ?_ ?_
    · rintro y (hy | ⟨a, ha, rfl⟩)
      · exact ⟨y, hy, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
      · exact ⟨a, ha, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
    · rintro _ ⟨a₁, ha₁, t₁, ht₁, rfl⟩ _ ⟨a₂, ha₂, t₂, ht₂, rfl⟩ p q hp hq hpq
      refine ⟨p • a₁ + q • a₂, hA ha₁ ha₂ hp hq hpq, p * t₁ + q * t₂, ⟨?_, ?_⟩, ?_⟩
      · nlinarith [ht₁.1, ht₂.1]
      · nlinarith [ht₁.2, ht₂.2]
      · simp only [smul_add, smul_smul, add_smul]
        abel
  · rintro _ ⟨a, ha, t, ⟨ht0, ht1⟩, rfl⟩
    -- `a + t x = (1 - t) a + t (a + x)`
    have h := convex_convexHull ℝ (A ∪ (fun a => a + x) '' A)
      (subset_convexHull ℝ _ (Or.inl ha)) (subset_convexHull ℝ _ (Or.inr ⟨a, ha, rfl⟩))
      (sub_nonneg.2 ht1) ht0 (by ring)
    convert h using 1
    simp only [smul_add, sub_smul, one_smul]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
