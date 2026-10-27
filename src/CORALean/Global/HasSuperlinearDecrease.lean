module

public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

/-!
# Def. 1: superlinear decrease

[1, Def. 1]: the set-based evaluation of a continuous function decreases superlinearly in the
length of the interval it is evaluated over if shrinking that length by any `φ ∈ (0,1)` shrinks the
evaluation by at least that factor. Stated at a function `F : ℝ → Set α` and one fixed length `Δt`,
not universally: [1]'s own uses, `Lemma 1` and `Thm. 2`, each name one specific `Δt` under a side
condition holding at that `Δt` alone. `t` in the paper's `f(S([t,t+Δt]))` is this same length, the
interval's start playing no role, so it carries no argument here. Generic over any real vector
space, not a representation: `α` is `Mat ℝ n n` at `Lemma 1`'s `E(Δt,η)` and `ℝ` at `Thm. 2`'s
`ε_P`, on a par with `Global/Radstrom.lean`.

## Inputs
* `F` – set-valued evaluation as a function of interval length
* `Δt` – interval length

## Output
* the proposition that shrinking the length by any factor shrinks the evaluation by that factor

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 1]: `F`'s set-based evaluation decreases superlinearly at `Δt` if
scaling the length by any `φ ∈ (0,1)` shrinks it by at least that factor. -/
def HasSuperlinearDecrease (F : ℝ → Set α) (Δt : ℝ) : Prop :=
  ∀ φ ∈ Set.Ioo (0:ℝ) 1, F (φ * Δt) ⊆ φ • F Δt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
