import Mathlib.Analysis.Asymptotics.Defs

/-!
# Def. 1: superlinear decrease

[1, Def. 1]: the set-based evaluation of a continuous function decreases
superlinearly in the length of the interval it is evaluated over if shrinking
that length by any `φ ∈ (0,1)` shrinks the evaluation by at least that factor.

Stated at a function `F : ℝ → Set α` and one fixed length `Δt`, not
universally over every length: [1]'s own uses, `Lemma 1` and `Thm. 2`, each
name one specific `Δt` — a step's own size — under a side condition holding at
that `Δt` alone, which a "for every length" reading would have to smuggle in
as a second hypothesis. `t` in the paper's own `f(S([t,t+Δt]))` is this same
length, the interval's start playing no role in the inequality, so it carries
no argument here.

Generic over any real vector space, not a representation: `α` is `Mat ℝ n n`
at `Lemma 1`'s `E(Δt,η)` and would be `ℝ` itself at `Thm. 2`'s `ε_P`, on a par
with `Global/Radstrom.lean`.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 1]: `F`'s set-based evaluation decreases superlinearly at `Δt` if
scaling the length by any `φ ∈ (0,1)` shrinks it by at least that factor. -/
def SuperlinearDecrease (F : ℝ → Set α) (Δt : ℝ) : Prop :=
  ∀ φ ∈ Set.Ioo (0:ℝ) 1, F (φ * Δt) ⊆ φ • F Δt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
