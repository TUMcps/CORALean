module

public import CORALean.ContSet.Conversion.Float.Operations.Vec_to_ContSet
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# `plus` with a vector is outer for the translation

`Plus.plus s b`, with the vector `b` coerced to its one-point set (`OfInterval.ofVec`), holds
the set `s` denotes translated by the real point `b` denotes: CORA's `plus(S, b)`. Outer and not
exact, as `plus_outer` is.

## Inputs
* `s` – set
* `b` – vector of the scalar

## Hypotheses
* none

## Conclusion
* the set of `s`, translated by `b`, lies in the set of `Plus.plus s b`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.OfInterval

open ContSet ContSetLike Plus

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [OfInterval S 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem plus_ofVec_outer (s : S n) (b : Vec 𝕋 n) :
    (· + toRealVec b) '' toSet s ⊆ toSet (Plus.plus s (b : S n)) := by
  rintro _ ⟨x, hx, rfl⟩
  exact plus_outer _ _ (Set.add_mem_add hx (ofInterval_outer _ (Interval.mem_point b)))

end CORALean.Float.OfInterval


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
