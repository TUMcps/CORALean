module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.point`, over a floating-point scalar

Zero width, which is the singleton the stored value denotes. Nothing is
rounded: the point is whatever `𝕋`-valued `α` already holds. The membership
fact, `mem_point`, is `Theorems/MemPoint.lean`.

Generic over the ambient type, as `Real.Interval.point` is, so `matPow`'s
identity `Interval.point 1 : Interval (Mat 𝕋 n n)` reaches it too. Composed with
`plus`/`matPlus` this is a translation, so a layer needs no operation of its own
for a bias — which is how a linear layer's offset reaches a set here.

## Inputs
* `α` – carrier type
* `v` – the point

## Output
* degenerate interval at `v`
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.point {α : Type} (v : α) : Interval α := ⟨v, v⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
