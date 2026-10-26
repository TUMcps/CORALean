module

public import CORALean.ContSet.Interval.Float.Theorems.AcosOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanCosFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat
public import CORALean.Specification.SyntaxTree.Theorems.PeriodicFloatContains
public import CORALean.Specification.SyntaxTree.Theorems.PiFloatContains

@[expose] public section

/-!
# `aux_cos_` over floats is sound

`SyntaxTree.funHanCosFloat` keeps every solution of `cos s ∈ int`: a time with `cos s` between two
bounds lies in a copy `x + 2 pi n` of one of the two inverse branches, `acos` and `-acos`, whose
ends the rounded `acos` encloses; `periodicFloat_contains` then holds it.

## Inputs
* `p` – precision of `pi` and of the inverse cosine
* `k` – Newton steps
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* none

## Conclusion
* the float inverse of the cosine keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A time with `cos s ∈ [lo,hi]` lies in a shifted branch of `acos`. -/
theorem SyntaxTree.aux_exists_cos_branchFloat {s lo hi : ℝ} (h₁ : lo ≤ Real.cos s)
    (h₂ : Real.cos s ≤ hi) : -- --- CONCL ---
    ∃ k : ℤ, (Real.arccos hi + k * (2 * Real.pi) ≤ s ∧
        s ≤ Real.arccos lo + k * (2 * Real.pi)) ∨
      (-Real.arccos lo + k * (2 * Real.pi) ≤ s ∧
        s ≤ -Real.arccos hi + k * (2 * Real.pi)) := by -- --- PROOF ---
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_cos_` over floats is sound for `cos`. -/
theorem SyntaxTree.funHanCosFloat_sound (p k : ℕ)
    (prev v : Float.SyntaxTree.Dom 𝕋) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.cos.fn prev v
      (SyntaxTree.funHanCosFloat p k) := by -- --- PROOF ---
  intro int _ s hs hi
  have h : toReal (int.inf 0) ≤ Real.cos s ∧ Real.cos s ≤ toReal (int.sup 0) := hi
  have hcut : Float.SyntaxTree.Dom.contains
      (Float.Interval.intersection int (SyntaxTree.intervalFloat (neg one) one)) (Real.cos s) := by
    simp only [Float.SyntaxTree.Dom.contains, Float.Interval.intersection, SyntaxTree.intervalFloat,
      toReal_maximum, toReal_minimum, toReal_neg, toReal_one]
    exact ⟨max_le h.1 (Real.neg_one_le_cos s), le_min h.2 (Real.cos_le_one s)⟩
-- the cut target holds the point
  set cut := Float.Interval.intersection int (SyntaxTree.intervalFloat (neg one) one) with hcdef
  have hne : toReal (cut.inf 0) ≤ toReal (cut.sup 0) := hcut.1.trans hcut.2
-- the rounded inverse encloses the inverse at both ends of the cut target
  have a₁ := SyntaxTree.contains_of_outerFloat (f := Real.arccos)
    (Float.Interval.acos_outer p k cut)
    (show Float.SyntaxTree.Dom.contains cut (toReal (cut.inf 0)) from ⟨le_rfl, hne⟩)
  have a₂ := SyntaxTree.contains_of_outerFloat (f := Real.arccos)
    (Float.Interval.acos_outer p k cut)
    (show Float.SyntaxTree.Dom.contains cut (toReal (cut.sup 0)) from ⟨hne, le_rfl⟩)
-- the point lies in a copy of one of the two branches
  obtain ⟨n, hn⟩ := SyntaxTree.aux_exists_cos_branchFloat (s := s) hcut.1 hcut.2
-- the copy lies in the branch intervals the rounding encloses
  have hn' : (toReal ((Float.Interval.acos p k cut).inf 0) + n * (2 * Real.pi) ≤ s ∧
        s ≤ toReal ((Float.Interval.acos p k cut).sup 0) + n * (2 * Real.pi)) ∨
      (toReal ((⟨fun _ => neg ((Float.Interval.acos p k cut).sup 0),
        fun _ => neg ((Float.Interval.acos p k cut).inf 0)⟩ : Float.SyntaxTree.Dom 𝕋).inf 0) +
          n * (2 * Real.pi) ≤ s ∧
        s ≤ toReal ((⟨fun _ => neg ((Float.Interval.acos p k cut).sup 0),
        fun _ => neg ((Float.Interval.acos p k cut).inf 0)⟩ : Float.SyntaxTree.Dom 𝕋).sup 0) +
          n * (2 * Real.pi)) := by
    rcases hn with hn | hn
    · exact Or.inl ⟨by linarith [a₂.1, hn.1], by linarith [a₁.2, hn.2]⟩
    · refine Or.inr ⟨?_, ?_⟩
      · show toReal (neg _) + _ ≤ s
        rw [toReal_neg]; linarith [a₁.2, hn.1]
      · show s ≤ toReal (neg _) + _
        rw [toReal_neg]; linarith [a₂.1, hn.2]
  obtain ⟨c, w⟩ := SyntaxTree.periodicFloat_contains p k hs n hn'
  exact ⟨_, rfl, c, w⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
