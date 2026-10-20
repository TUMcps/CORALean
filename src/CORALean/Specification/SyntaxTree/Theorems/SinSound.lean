module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Definitions.UnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.PeriodicContains
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `aux_sin_` is sound

`aux_sin_` keeps every solution of `sin s ∈ int`.

## Inputs
* `s` – point
* `lo` – lower bound
* `hi` – upper bound

## Hypotheses
* `h₁` – the sine is at least the lower bound
* `h₂` – the sine is at most the upper bound

## Conclusion
* the point lies in a shifted branch of the inverse sine
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A time with `sin s ∈ [lo,hi]` lies in a shifted branch of `asin`. -/
private theorem SyntaxTree.exists_sin_branch {s lo hi : ℝ}
    (h₁ : lo ≤ Real.sin s) (h₂ : Real.sin s ≤ hi) : -- --- CONCL ---
    ∃ k : ℤ, (Real.arcsin lo + k * (2 * Real.pi) ≤ s ∧ s ≤ Real.arcsin hi + k * (2 * Real.pi)) ∨
      (Real.pi - Real.arcsin hi + k * (2 * Real.pi) ≤ s ∧
        s ≤ Real.pi - Real.arcsin lo + k * (2 * Real.pi)) := by -- --- PROOF ---
  -- reduce `s` into `[-pi/2, 3pi/2)`
  have hp : 0 < 2 * Real.pi := by positivity
  set k : ℤ := ⌊(s + Real.pi / 2) / (2 * Real.pi)⌋ with hk
  have f₁ := Int.floor_le ((s + Real.pi / 2) / (2 * Real.pi))
  have f₂ := Int.lt_floor_add_one ((s + Real.pi / 2) / (2 * Real.pi))
  rw [le_div_iff₀ hp] at f₁
  rw [div_lt_iff₀ hp] at f₂
  refine ⟨k, ?_⟩
  set u : ℝ := s - k * (2 * Real.pi) with hu
  have hsin : Real.sin u = Real.sin s := by
    rw [hu, Real.sin_sub_int_mul_two_pi]
  have hu₁ : -(Real.pi / 2) ≤ u := by rw [hu]; linarith
  -- the fact `u < 3 * Real.pi / 2`
  have hu₂ : u < 3 * Real.pi / 2 := by rw [hu]; nlinarith
  by_cases hle : u ≤ Real.pi / 2
  · left
    have e : Real.arcsin (Real.sin u) = u := Real.arcsin_sin hu₁ hle
    have a₁ : Real.arcsin lo ≤ u := by
      rw [← e, hsin]; exact Real.arcsin_le_arcsin (hsin ▸ h₁)
    have a₂ : u ≤ Real.arcsin hi := by
      rw [← e, hsin]; exact Real.arcsin_le_arcsin h₂
    constructor <;> linarith
  · right
    have hv₁ : -(Real.pi / 2) ≤ Real.pi - u := by linarith
    have hv₂ : Real.pi - u ≤ Real.pi / 2 := by linarith [not_le.1 hle]
    -- the fact `Real.arcsin (Real.sin (Real.pi - u)) = Real.pi - u`
    have e : Real.arcsin (Real.sin (Real.pi - u)) = Real.pi - u := Real.arcsin_sin hv₁ hv₂
    rw [Real.sin_pi_sub, hsin] at e
    have a₁ : Real.arcsin lo ≤ Real.pi - u := by
      rw [← e]; exact Real.arcsin_le_arcsin h₁
    have a₂ : Real.pi - u ≤ Real.arcsin hi := by
      rw [← e]; exact Real.arcsin_le_arcsin h₂
    constructor <;> linarith

/-- `aux_sin_` is sound for `sin`. -/
theorem SyntaxTree.sin_sound (prev : Dom) :
    UnarySound Unary.sin.fn prev (Real.Interval.sin prev) funHanSin := by -- --- PROOF ---
  intro int _ s hs hi
  have h : int.inf 0 ≤ Real.sin s ∧ Real.sin s ≤ int.sup 0 := hi
  obtain ⟨k, hk⟩ := exists_sin_branch (s := s) (lo := max (int.inf 0) (-1)) (hi := min (int.sup 0)
      1)
    (max_le h.1 (Real.neg_one_le_sin s)) (le_min h.2 (Real.sin_le_one s))
  obtain ⟨c, w⟩ := periodic_contains (R₁ := Real.Interval.asin (Real.Interval.intersection int
      (interval (-1) 1)))
    (R₂ := interval (Real.pi - (Real.Interval.asin (Real.Interval.intersection int (interval (-1)
        1))).sup 0)
      (Real.pi - (Real.Interval.asin (Real.Interval.intersection int (interval (-1) 1))).inf 0))
    hs k (by simpa [Real.Interval.asin, Real.Interval.intersection, interval] using hk)
  exact ⟨_, rfl, c, w⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
