module

public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.Specification.SyntaxTree.Operations.PeriodicFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.PiFloatContains

@[expose] public section

/-!
# The periodic tail over floats keeps every solution

`SyntaxTree.periodicFloat` holds every `s` of `intPrev` that lies in a copy `x + k·2 pi` of one of
the two branches. A copy certified to start above the upper end of `intPrev` leaves `s` in an
earlier copy, whose top the rounded shift bounds; the lower end is symmetric. Where nothing is
certified the end of `intPrev` itself bounds `s`. The index `k` of the bounds is arbitrary: only the
certificate is used.

## Inputs
* `p` – precision of `pi`
* `k` – Newton steps of `pi`
* `R₁` – interval of the first branch
* `R₂` – interval of the second branch
* `prev` – previous interval
* `s` – point
* `n` – index of the copy holding the point

## Hypotheses
* `hs` – the previous interval holds the point
* `hn` – the point lies in a copy of one of the branches

## Conclusion
* the result holds the point and lies inside the previous interval
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

omit [ToRat 𝕋] in
/-- The rounded shift of `R` by `m` periods encloses the shift by the real period `P`. -/
private theorem SyntaxTree.aux_shift_enclosesFloat {twoPi R : Float.SyntaxTree.Dom 𝕋} {P : ℝ}
    (hP : toReal (twoPi.inf 0) ≤ P ∧ P ≤ toReal (twoPi.sup 0)) (m : ℤ) : -- --- CONCL ---
    toReal ((SyntaxTree.aux_periodicFloat_shift twoPi R m).inf 0) ≤ toReal (R.inf 0) + m * P ∧
      toReal (R.sup 0) + m * P ≤ toReal
      ((SyntaxTree.aux_periodicFloat_shift twoPi R m).sup 0) := by -- --- PROOF ---
  have hm := intDown_le_intUp (𝕋 := 𝕋) m
  have hb := Float.Interval.mul_between_corners (a := (intDown m : 𝕋)) (b := intUp m)
    (c := twoPi.inf 0) (d := twoPi.sup 0) hm.1 hm.2 hP.1 hP.2
  constructor
  · change toReal (addDown (R.inf 0) (Float.Interval.mulLo (intDown m) (intUp m) (twoPi.inf 0)
      (twoPi.sup 0))) ≤ _
    exact (addDown_le_add _ _).trans (by linarith [hb.1])
  · change _ ≤ toReal (addUp (R.sup 0) (Float.Interval.mulHi (intDown m) (intUp m) (twoPi.inf 0)
      (twoPi.sup 0)))
    exact le_trans (by linarith [hb.2]) (add_le_addUp _ _)

omit [ToRat 𝕋] in
/-- A solution in a copy at or below the index `m` of a certified shift cannot reach above `a`. -/
private theorem SyntaxTree.aux_lower_coreFloat {twoPi R : Float.SyntaxTree.Dom 𝕋} {P s : ℝ} {a : 𝕋}
    (hP : toReal (twoPi.inf 0) ≤ P ∧ P ≤ toReal (twoPi.sup 0)) (hp : 0 < P) (ind n : ℤ)
    (hn : toReal (R.inf 0) + n * P ≤ s ∧ s ≤ toReal (R.sup 0) + n * P)
    (has : toReal a ≤ s) : -- --- CONCL ---
    toReal
      (if ltStrict ((SyntaxTree.aux_periodicFloat_shift twoPi R ind).sup 0) a = true then
      (SyntaxTree.aux_periodicFloat_shift twoPi R (ind + 1)).inf 0 else
      a) ≤ s := by -- --- PROOF ---
  split_ifs with hc
  · have h1 := toReal_lt_of_ltStrict hc
    have hk : ind + 1 ≤ n := by
      by_contra hlt
      have hn' : n ≤ ind := by omega
      have : (n : ℝ) ≤ ind := by exact_mod_cast hn'
      nlinarith [(SyntaxTree.aux_shift_enclosesFloat (R := R) hP ind).2, hn.2]
    have hk' : ((ind + 1 : ℤ) : ℝ) ≤ n := by exact_mod_cast hk
    refine le_trans (SyntaxTree.aux_shift_enclosesFloat (R := R) hP (ind + 1)).1 ?_
    nlinarith [hn.1]
  · exact has

omit [ToRat 𝕋] in
/-- A solution in a copy at or above the index `m` of a certified shift cannot reach below `b`. -/
private theorem SyntaxTree.aux_upper_coreFloat {twoPi R : Float.SyntaxTree.Dom 𝕋} {P s : ℝ} {b : 𝕋}
    (hP : toReal (twoPi.inf 0) ≤ P ∧ P ≤ toReal (twoPi.sup 0)) (hp : 0 < P) (ind n : ℤ)
    (hn : toReal (R.inf 0) + n * P ≤ s ∧ s ≤ toReal (R.sup 0) + n * P)
    (hsb : s ≤ toReal b) : -- --- CONCL ---
    s ≤ toReal
      (if ltStrict b ((SyntaxTree.aux_periodicFloat_shift twoPi R ind).inf 0) = true then
      (SyntaxTree.aux_periodicFloat_shift twoPi R (ind - 1)).sup 0 else b) := by -- --- PROOF ---
  split_ifs with hc
  · have h1 := toReal_lt_of_ltStrict hc
    have hk : n ≤ ind - 1 := by
      by_contra hlt
      have hn' : ind ≤ n := by omega
      have : (ind : ℝ) ≤ n := by exact_mod_cast hn'
      nlinarith [(SyntaxTree.aux_shift_enclosesFloat (R := R) hP ind).1, hn.1]
    have hk' : (n : ℝ) ≤ ((ind - 1 : ℤ) : ℝ) := by exact_mod_cast hk
    refine le_trans ?_ (SyntaxTree.aux_shift_enclosesFloat (R := R) hP (ind - 1)).2
    nlinarith [hn.2]
  · exact hsb


-- =======================================  MAIN THEOREM  ======================================= --

/-- The result holds `s` and lies inside `prev`, for `s` in a shifted branch and in `prev`. -/
theorem SyntaxTree.periodicFloat_contains (p k : ℕ) {R₁ R₂ prev : Float.SyntaxTree.Dom 𝕋} {s : ℝ}
    (hs : prev.contains s) (n : ℤ)
    (hn : (toReal (R₁.inf 0) + n * (2 * Real.pi) ≤ s ∧
        s ≤ toReal (R₁.sup 0) + n * (2 * Real.pi)) ∨
      (toReal (R₂.inf 0) + n * (2 * Real.pi) ≤ s ∧
        s ≤ toReal (R₂.sup 0) + n * (2 * Real.pi))) : -- --- CONCL ---
    Float.SyntaxTree.Dom.contains (SyntaxTree.periodicFloat p k R₁ R₂ prev) s ∧
      Float.SyntaxTree.Dom.IsWithin (SyntaxTree.periodicFloat p k R₁ R₂ prev)
        prev := by -- --- PROOF ---
  have hπ := SyntaxTree.piFloat_contains (𝕋 := 𝕋) p k
  have hP : toReal (addDown (SyntaxTree.piFloat (𝕋 := 𝕋) p k).inf (SyntaxTree.piFloat p k).inf) ≤
        2 * Real.pi ∧ 2 * Real.pi ≤
      toReal (addUp (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup (SyntaxTree.piFloat p k).sup) := by
    have h1 := addDown_le_add (SyntaxTree.piFloat (𝕋 := 𝕋) p k).inf (SyntaxTree.piFloat p k).inf
    have h2 := add_le_addUp (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup (SyntaxTree.piFloat p k).sup
    constructor <;> linarith [hπ.1, hπ.2]
  have hpos : 0 < 2 * Real.pi := by positivity
  unfold SyntaxTree.periodicFloat
  dsimp only
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- the new lower bound is at most `s`
    simp only [toReal_maximum, toReal_minimum]
    refine max_le hs.1 ?_
    rcases hn with h | h
    · exact min_le_of_left_le (SyntaxTree.aux_lower_coreFloat hP hpos _ n h hs.1)
    · exact min_le_of_right_le (SyntaxTree.aux_lower_coreFloat hP hpos _ n h hs.1)
  · -- the new upper bound is at least `s`
    simp only [toReal_maximum, toReal_minimum]
    refine le_min hs.2 ?_
    rcases hn with h | h
    · exact le_max_of_le_left (SyntaxTree.aux_upper_coreFloat hP hpos _ n h hs.2)
    · exact le_max_of_le_right (SyntaxTree.aux_upper_coreFloat hP hpos _ n h hs.2)
  · simp only [toReal_maximum]; exact le_max_left _ _
  · simp only [toReal_minimum]; exact min_le_left _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
