module

public import CORALean.ContSet.Interval.Float.Theorems.AcoshOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanCoshFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat
public import CORALean.Specification.SyntaxTree.Theorems.SignedRootsFloatContains

@[expose] public section

/-!
# `aux_cosh_` over floats is sound

`SyntaxTree.funHanCoshFloat` keeps every solution of `cosh s ∈ int`: the absolute value of `s` is
the inverse hyperbolic cosine of `cosh s`, which lies in `int` cut to the reals from `1`, and
`Interval.acosh` encloses it; the sign `intPrev` allows is `signedRootsFloat_contains`. The cut
lower bound is within the range of the float logarithm because the target lies inside the node's
interval.

## Inputs
* `p` – precision of the logarithm
* `k` – bisection and root steps
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* `hv` – the value interval stays within the range of the logarithm

## Conclusion
* the float inverse of the hyperbolic cosine keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_cosh_` over floats is sound for `cosh`, within the logarithm's range. -/
theorem SyntaxTree.funHanCoshFloat_sound (p k : ℕ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (hv : 2 * toReal (v.sup 0) ≤ 2 ^ p / 2) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.cosh.fn prev v
      (SyntaxTree.funHanCoshFloat p k) := by -- --- PROOF ---
  intro int hw s hs hi
  have h : toReal (int.inf 0) ≤ Real.cosh s ∧ Real.cosh s ≤ toReal (int.sup 0) := hi
  have hc1 : 1 ≤ Real.cosh s := Real.one_le_cosh s
  have hnd : ¬ ltStrict (int.sup 0) one = true := fun hc => by
    have := toReal_lt_of_ltStrict hc
    rw [toReal_one] at this
    linarith [h.2]
  -- the target cut to `≥ 1` holds `cosh s`
  set cut : Float.SyntaxTree.Dom 𝕋 := ⟨fun _ => maximum (int.inf 0) one, fun _ => int.sup 0⟩
    with hcdef
  have hcut : cut.contains (Real.cosh s) :=
    ⟨by simp only [hcdef, toReal_maximum, toReal_one]; exact max_le h.1 hc1, h.2⟩
  -- its lower bound is within the range of the inverse hyperbolic cosine
  have hI : ∀ i, 1 ≤ toReal (cut.inf i) ∧ 2 * toReal (cut.inf i) ≤ 2 ^ p / 2 := fun i => by
    simp only [hcdef, toReal_maximum, toReal_one]
    refine ⟨le_max_right _ _, ?_⟩
    have : max (toReal (int.inf 0)) 1 ≤ toReal (v.sup 0) :=
      max_le (h.1.trans (h.2.trans hw.2)) (hc1.trans (h.2.trans hw.2))
    linarith
  -- `acosh` encloses the inverse hyperbolic cosine of `cosh s`
  have a := SyntaxTree.contains_of_outerFloat (f := Real.arcosh)
    (Float.Interval.acosh_outer p k cut hI) hcut
  rw [← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg s)] at a
  -- the sign `intPrev` allows keeps `s`
  unfold SyntaxTree.funHanCoshFloat
  dsimp only
  rw [if_neg hnd]
  exact ⟨_, rfl, SyntaxTree.meet_containsFloat hs (SyntaxTree.signedRootsFloat_contains hs a.1 a.2)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
