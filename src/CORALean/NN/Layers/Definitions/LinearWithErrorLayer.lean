import CORALean.ContSet.Interval.Float.Interval

/-!
# The weights of a linear layer with an error box

CORA's `W h + b ⊕ E` as an `Enclose` kind. The function it encloses commits to the centre of
the box, which a box needs to be nonempty to have; the instance runs on `E.nonemptyHull`
rather than asking for a proof, since a reduction computes `E` at run time with none to hand.
The hull is `E` itself whenever `E` is nonempty, so nothing it computes changes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure LinearWithErrorLayer (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
    (n m : ℕ) where
  W : Mat 𝕋 m n
  b : Vec 𝕋 m
  E : Float.Interval (Vec 𝕋 m)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
