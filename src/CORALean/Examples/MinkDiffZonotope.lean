import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffOrEmptyNeEmpty

/-!
# The Minkowski difference of zonotopes may be empty

A zonotope has no difference of its own to instantiate `MinkDiff` with, since `{0} ⊖ [-1, 1]`
is `∅` and no zonotope is: `OptEmpty` is where the instance lives. `[-1, 1]` less
`[-0.2, 0.2]`, one generator each, is a pair it answers with a zonotope rather than `∅`: the
subtrahend's generator written in the minuend's own certifies it, and one candidate certifying
is enough.

## Inputs
* none

## Output
* first example zonotope
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[-1, 1]` and `[-0.2, 0.2]`, one generator each. -/
def MDiff.Z1 : Zonotope (Vec ℝ 1) := ⟨1, ![(0:ℝ)], fun _ => ![(1:ℝ)]⟩

/-- The zonotope `[-0.2, 0.2]` with one generator. -/
def MDiff.Z2 : Zonotope (Vec ℝ 1) := ⟨1, ![(0:ℝ)], fun _ => ![(0.2:ℝ)]⟩

/-- The subtrahend's generator written in the minuend's own, which is the
candidate `minkDiffRep` checks — here it passes both halves of that check. -/
def MDiff.M : Fin MDiff.Z1.h → Fin MDiff.Z2.h → ℝ := fun _ _ => 0.2

/-- `minkDiffRep` accepts the candidate `M` and returns a zonotope. -/
theorem MDiff.certified : -- --- CONCL ---
    (MDiff.Z1.minkDiffRep MDiff.Z2 MDiff.M).isSome := by -- --- PROOF ---
  rw [Zonotope.minkDiffRep, if_pos]
  · rfl
  -- the representation first, the row budget `0.2 ≤ 1` second
  constructor
  · intro j
    funext i
    fin_cases i
    simp [MDiff.Z1, MDiff.Z2, MDiff.M]
  · intro i
    simp [MDiff.M, MDiff.Z2]
    norm_num

/-- One candidate certifying is enough: the operation answers with a zonotope,
not with the `∅` its inner obligation would have accepted just as readily. -/
example : MDiff.Z1.minkDiffOrEmpty MDiff.Z2 ≠ OptEmpty.empty :=
  Zonotope.minkDiffOrEmpty_ne_empty MDiff.Z1 MDiff.Z2 ⟨MDiff.M, MDiff.certified⟩

/-- The instance itself, which is what an algorithm asking for a difference
resolves — at the wrapper, and not at `Zonotope`. -/
noncomputable example : MinkDiff (OptEmpty (Zonotope (Vec ℝ 1))) (Vec ℝ 1) := inferInstance

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
