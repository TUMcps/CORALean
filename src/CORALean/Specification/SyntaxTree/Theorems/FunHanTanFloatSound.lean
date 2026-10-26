module

public import CORALean.ContSet.Interval.Float.Theorems.AtanOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat
public import CORALean.Specification.SyntaxTree.Theorems.PeriodicFloatContains
public import CORALean.Specification.SyntaxTree.Theorems.PiFloatContains

@[expose] public section

/-!
# `aux_tan_` over floats is sound

`SyntaxTree.funHanTanFloat` keeps every solution of `tan s ∈ int` for an operand inside `(-pi/2,
pi/2)`: `s` is the inverse tangent of its tangent, which lies between the inverse tangents of the
bounds, in the first branch, whose ends the rounded `atan` encloses; `periodicFloat_contains` then
holds it.

## Inputs
* `p` – precision of `pi` and of the inverse tangent
* `k` – Newton steps
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hd₁` – the operand interval stays above minus half of `pi`
* `hd₂` – the operand interval stays below half of `pi`

## Conclusion
* the float inverse of the tangent keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_tan_` over floats is sound for `tan` on an operand inside `(-pi/2, pi/2)`. -/
theorem SyntaxTree.funHanTanFloat_sound (p k : ℕ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (hd₁ : -(Real.pi / 2) < toReal (prev.inf 0))
    (hd₂ : toReal (prev.sup 0) < Real.pi / 2) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.tan.fn prev v
      (SyntaxTree.funHanTanFloat p k) := by -- --- PROOF ---
  intro int _ s hs hi
  have h : toReal (int.inf 0) ≤ Real.tan s ∧ Real.tan s ≤ toReal (int.sup 0) := hi
  have e : Real.arctan (Real.tan s) = s :=
    Real.arctan_tan (hd₁.trans_le hs.1) (hs.2.trans_lt hd₂)
  have hne : toReal (int.inf 0) ≤ toReal (int.sup 0) := h.1.trans h.2
-- the rounded `atan` encloses the inverse tangent of both ends
  have a₁ := SyntaxTree.contains_of_outerFloat (f := Real.arctan)
    (Float.Interval.atan_outer p k int)
    (show Float.SyntaxTree.Dom.contains int (toReal (int.inf 0)) from ⟨le_rfl, hne⟩)
  have a₂ := SyntaxTree.contains_of_outerFloat (f := Real.arctan)
    (Float.Interval.atan_outer p k int)
    (show Float.SyntaxTree.Dom.contains int (toReal (int.sup 0)) from ⟨hne, le_rfl⟩)
  have b₁ : Real.arctan (toReal (int.inf 0)) ≤ s := by
    rw [← e]; exact Real.arctan_strictMono.monotone h.1
  have b₂ : s ≤ Real.arctan (toReal (int.sup 0)) := by
    rw [← e]; exact Real.arctan_strictMono.monotone h.2
-- the point lies in the first branch, whose ends the rounded `atan` bounds
  have hn' : (toReal ((Float.Interval.atan p k int).inf 0) + ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ s ∧
        s ≤ toReal ((Float.Interval.atan p k int).sup 0) + ((0 : ℤ) : ℝ) * (2 * Real.pi)) ∨
      (toReal ((⟨fun _ => addDown ((Float.Interval.atan p k int).inf 0)
          (SyntaxTree.piFloat (𝕋 := 𝕋) p k).inf,
        fun _ => addUp ((Float.Interval.atan p k int).sup 0)
          (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup⟩ : Float.SyntaxTree.Dom 𝕋).inf 0) +
          ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ s ∧
        s ≤ toReal ((⟨fun _ => addDown ((Float.Interval.atan p k int).inf 0)
          (SyntaxTree.piFloat (𝕋 := 𝕋) p k).inf,
        fun _ => addUp ((Float.Interval.atan p k int).sup 0)
          (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup⟩ : Float.SyntaxTree.Dom 𝕋).sup 0) +
          ((0 : ℤ) : ℝ) * (2 * Real.pi)) :=
    Or.inl ⟨by simp only [Int.cast_zero, zero_mul, add_zero]; linarith [a₁.1],
      by simp only [Int.cast_zero, zero_mul, add_zero]; linarith [a₂.2]⟩
  obtain ⟨c, w⟩ := SyntaxTree.periodicFloat_contains p k hs 0 hn'
  exact ⟨_, rfl, c, w⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
