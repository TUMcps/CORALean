module

public import CORALean.ContSet.Conversion.Float.Interfaces
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# A stored vector as a set

The one-point set of a vector of the scalar, `ofInterval (Interval.point b)`: the box of zero
width, in any representation with `OfInterval`. A scoped coercion makes it implicit, so CORA's
`plus(S, b)` with a vector reads `Plus.plus s b` once `Float.OfInterval` is open; the
translation it gives is `Theorems/PlusOfVecOuter.lean`. Nothing rounds: the box is the stored value.

## Inputs
* `b` – vector of the scalar

## Output
* set holding the real point `b` denotes
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.OfInterval

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] [OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ofVec (b : Vec 𝕋 n) : S n := ofInterval (Interval.point b)

/-- A vector where a set is expected is its one-point set, `ofVec`. -/
scoped instance : CoeTail (Vec 𝕋 n) (S n) := ⟨ofVec⟩

end CORALean.Float.OfInterval


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
