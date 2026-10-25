module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# Taylor models over an explicit box domain

[1, Def. 3]: a vector field `p : ℝⁿ → ℝⁿ`, a box domain `I` and a box remainder `B` denote
`{p(x) + b | x ∈ I, b ∈ B}`, the union over `x ∈ I` of [1]'s `T(x)`. Unlike `Taylm` the domain
is not normalized to `[-1, 1]ⁿ` — [1] keeps it so that its `Thm. 1` can reuse the box being
intersected as the domain. `p` is any function: being a polynomial matters for representing
the set, not for what it denotes. [1] writes `∅` for a model without remainder; that is the
zero box here, since read literally `∅` would make the set empty.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
      Sets". Proceedings of the 23rd International Conference on Hybrid Systems: Computation and
      Control, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- `⟨p(x), B, I⟩_TM`. -/
structure TaylorModelOn (n : ℕ) where
  p : Vec ℝ n → Vec ℝ n
  B : Interval (Vec ℝ n)
  I : Interval (Vec ℝ n)

/-- `{T(x) | x ∈ I}` with `T(x) = {p(x) + b | b ∈ B}`. -/
def TaylorModelOn.construct (T : TaylorModelOn n) : Set (Vec ℝ n) :=
  {y | ∃ x ∈ T.I.construct, ∃ b ∈ T.B.construct, y = T.p x + b}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
