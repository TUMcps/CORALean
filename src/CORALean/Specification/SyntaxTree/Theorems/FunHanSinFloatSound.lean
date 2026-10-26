module

public import CORALean.ContSet.Interval.Float.Theorems.AsinOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat
public import CORALean.Specification.SyntaxTree.Theorems.PeriodicFloatContains
public import CORALean.Specification.SyntaxTree.Theorems.PiFloatContains

@[expose] public section

/-!
# `aux_sin_` over floats is sound

`SyntaxTree.funHanSinFloat` keeps every solution of `sin s ∈ int`: a time with `sin s` between two
bounds lies in a copy `x + 2 pi n` of one of the two inverse branches, `asin` and `pi - asin`, whose
ends the rounded `asin` and the bounds of `pi` enclose; `periodicFloat_contains` then holds it.

## Inputs
* `p` – precision of `pi` and of the inverse sine
* `k` – Newton steps
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* none

## Conclusion
* the float inverse of the sine keeps every solution
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

/-- A time with `sin s ∈ [lo,hi]` lies in a shifted branch of `asin`. -/
theorem SyntaxTree.aux_exists_sin_branchFloat {s lo hi : ℝ} (h₁ : lo ≤ Real.sin s)
    (h₂ : Real.sin s ≤ hi) : -- --- CONCL ---
    ∃ k : ℤ, (Real.arcsin lo + k * (2 * Real.pi) ≤ s ∧ s ≤ Real.arcsin hi + k * (2 * Real.pi)) ∨
      (Real.pi - Real.arcsin hi + k * (2 * Real.pi) ≤ s ∧ s ≤ Real.pi - Real.arcsin lo + k * (2 *
      Real.pi)) := by -- --- PROOF ---
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_sin_` over floats is sound for `sin`. -/
theorem SyntaxTree.funHanSinFloat_sound (p k : ℕ)
    (prev v : Float.SyntaxTree.Dom 𝕋) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.sin.fn prev v
      (SyntaxTree.funHanSinFloat p k) := by -- --- PROOF ---
  intro int _ s hs hi
  have h : toReal (int.inf 0) ≤ Real.sin s ∧ Real.sin s ≤ toReal (int.sup 0) := hi
  have hcut : Float.SyntaxTree.Dom.contains
      (Float.Interval.intersection int (SyntaxTree.intervalFloat (neg one) one)) (Real.sin s) := by
    simp only [Float.SyntaxTree.Dom.contains, Float.Interval.intersection, SyntaxTree.intervalFloat,
      toReal_maximum, toReal_minimum, toReal_neg, toReal_one]
    exact ⟨max_le h.1 (Real.neg_one_le_sin s), le_min h.2 (Real.sin_le_one s)⟩
-- the cut target holds the point
  set cut := Float.Interval.intersection int (SyntaxTree.intervalFloat (neg one) one) with hcdef
  have hne : toReal (cut.inf 0) ≤ toReal (cut.sup 0) := hcut.1.trans hcut.2
-- the rounded inverse encloses the inverse at both ends of the cut target
  have a₁ := SyntaxTree.contains_of_outerFloat (f := Real.arcsin)
    (Float.Interval.asin_outer p k cut)
    (show Float.SyntaxTree.Dom.contains cut (toReal (cut.inf 0)) from ⟨le_rfl, hne⟩)
  have a₂ := SyntaxTree.contains_of_outerFloat (f := Real.arcsin)
    (Float.Interval.asin_outer p k cut)
    (show Float.SyntaxTree.Dom.contains cut (toReal (cut.sup 0)) from ⟨hne, le_rfl⟩)
-- the point lies in a copy of one of the two branches
  obtain ⟨n, hn⟩ := SyntaxTree.aux_exists_sin_branchFloat (s := s) hcut.1 hcut.2
  have hπ := SyntaxTree.piFloat_contains (𝕋 := 𝕋) p k
  have e₁ := Float.subDown_le_sub (SyntaxTree.piFloat (𝕋 := 𝕋) p k).inf
    ((Float.Interval.asin p k cut).sup 0)
  have e₂ := Float.sub_le_subUp (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup
    ((Float.Interval.asin p k cut).inf 0)
-- the copy lies in the branch intervals the rounding encloses
  have hn' : (toReal ((Float.Interval.asin p k cut).inf 0) + n * (2 * Real.pi) ≤ s ∧
        s ≤ toReal ((Float.Interval.asin p k cut).sup 0) + n * (2 * Real.pi)) ∨
      (toReal ((⟨fun _ => subDown (SyntaxTree.piFloat (𝕋 := 𝕋) p k).inf
          ((Float.Interval.asin p k cut).sup 0),
        fun _ => subUp (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup
          ((Float.Interval.asin p k cut).inf 0)⟩ : Float.SyntaxTree.Dom 𝕋).inf 0) +
          n * (2 * Real.pi) ≤ s ∧
        s ≤ toReal ((⟨fun _ => subDown (SyntaxTree.piFloat (𝕋 := 𝕋) p k).inf
          ((Float.Interval.asin p k cut).sup 0),
        fun _ => subUp (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup
          ((Float.Interval.asin p k cut).inf 0)⟩ : Float.SyntaxTree.Dom 𝕋).sup 0) +
          n * (2 * Real.pi)) := by
    rcases hn with hn | hn
    · exact Or.inl ⟨by linarith [a₁.1, hn.1], by linarith [a₂.2, hn.2]⟩
    · exact Or.inr ⟨by linarith [hπ.1, a₂.2, hn.1], by linarith [hπ.2, a₁.1, hn.2]⟩
  obtain ⟨c, w⟩ := SyntaxTree.periodicFloat_contains p k hs n hn'
  exact ⟨_, rfl, c, w⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
