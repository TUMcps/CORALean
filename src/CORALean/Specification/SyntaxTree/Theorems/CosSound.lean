module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Cos
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Definitions.UnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.PeriodicContains
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `aux_cos_` is sound

`aux_cos_` keeps every solution of `cos s ∈ int`.

## Inputs
* `s` – point
* `lo` – lower bound
* `hi` – upper bound

## Hypotheses
* `h₁` – the cosine is at least the lower bound
* `h₂` – the cosine is at most the upper bound

## Conclusion
* the point lies in a shifted branch of the inverse cosine
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A time with `cos s ∈ [lo,hi]` lies in a shifted branch of `acos`. -/
private theorem SyntaxTree.exists_cos_branch {s lo hi : ℝ} (h₁ : lo ≤ Real.cos s) (h₂ : Real.cos s
    ≤ hi) : -- --- CONCL ---
    ∃ k : ℤ, (Real.arccos hi + k * (2 * Real.pi) ≤ s ∧ s ≤ Real.arccos lo + k * (2 * Real.pi)) ∨
      (-Real.arccos lo + k * (2 * Real.pi) ≤ s ∧ s ≤ -Real.arccos hi + k * (2 *
        Real.pi)) := by -- --- PROOF ---
  -- reduce `s` into `[-pi, pi)`
  have hp : 0 < 2 * Real.pi := by positivity
  set k : ℤ := ⌊(s + Real.pi) / (2 * Real.pi)⌋ with hk
  have f₁ := Int.floor_le ((s + Real.pi) / (2 * Real.pi))
  have f₂ := Int.lt_floor_add_one ((s + Real.pi) / (2 * Real.pi))
  rw [le_div_iff₀ hp] at f₁
  rw [div_lt_iff₀ hp] at f₂
  refine ⟨k, ?_⟩
  set u : ℝ := s - k * (2 * Real.pi) with hu
  have hcos : Real.cos u = Real.cos s := by
    rw [hu, Real.cos_sub_int_mul_two_pi]
  have hu₁ : -Real.pi ≤ u := by rw [hu]; linarith
  -- the fact `u < Real.pi`
  have hu₂ : u < Real.pi := by rw [hu]; nlinarith
  by_cases hnn : 0 ≤ u
  · left
    have e : Real.arccos (Real.cos u) = u := Real.arccos_cos hnn hu₂.le
    have a₁ : Real.arccos hi ≤ u := by
      rw [← e, hcos]; exact Real.arccos_le_arccos h₂
    have a₂ : u ≤ Real.arccos lo := by
      rw [← e, hcos]; exact Real.arccos_le_arccos h₁
    constructor <;> linarith
  · right
    have hv₁ : 0 ≤ -u := by linarith [not_le.1 hnn]
    have hv₂ : -u ≤ Real.pi := by linarith
    -- the fact `Real.arccos (Real.cos (-u)) = -u`
    have e : Real.arccos (Real.cos (-u)) = -u := Real.arccos_cos hv₁ hv₂
    rw [Real.cos_neg, hcos] at e
    have a₁ : Real.arccos hi ≤ -u := by
      rw [← e]; exact Real.arccos_le_arccos h₂
    have a₂ : -u ≤ Real.arccos lo := by
      rw [← e]; exact Real.arccos_le_arccos h₁
    constructor <;> linarith

/-- `aux_cos_` is sound for `cos`. -/
theorem SyntaxTree.cos_sound (prev : Dom) : -- --- CONCL ---
    UnarySound Unary.cos.fn prev (Real.Interval.cos prev) funHanCos := by -- --- PROOF ---
  intro int _ s hs hi
  have h : int.inf 0 ≤ Real.cos s ∧ Real.cos s ≤ int.sup 0 := hi
  obtain ⟨k, hk⟩ := exists_cos_branch (s := s) (lo := max (int.inf 0) (-1)) (hi := min (int.sup 0)
      1)
    (max_le h.1 (Real.neg_one_le_cos s)) (le_min h.2 (Real.cos_le_one s))
  obtain ⟨c, w⟩ := periodic_contains (R₁ := Real.Interval.acos (Real.Interval.intersection int
      (interval (-1) 1)))
    (R₂ := interval (-(Real.Interval.acos (Real.Interval.intersection int (interval (-1) 1))).sup 0)
      (-(Real.Interval.acos (Real.Interval.intersection int (interval (-1) 1))).inf 0))
    hs k (by simpa [Real.Interval.acos, Real.Interval.intersection, interval] using hk)
  exact ⟨_, rfl, c, w⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
