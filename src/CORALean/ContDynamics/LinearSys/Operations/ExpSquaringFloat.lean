module

public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContSet.Interval.Float.Operations.MatMul

@[expose] public section

/-!
# `[e^{At}]` by scaling and squaring, over a float time range

`e^{At} = (e^{A t/2^s})^{2^s}`: `expIntervalFloat` at the range `[tLo, tHi]`
halved `s` times — exact, `half` only moving the exponent — then `s` interval
squarings, each stored. Nothing else enters: the chain is `s` products of one
fresh enclosure, so what rounding and the Taylor remainder cost grows with the
`s ≈ log₂(t/Δt)` squarings a range needs, and does not depend on any other
range's enclosure. A squaring roughly doubles the relative width, so the
enclosure is about `2^s` times as wide, relatively, as the scaled one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[e^{At}]` for every `t ∈ [tLo, tHi]`: the order-`η` enclosure at
`[tLo, tHi]/2^s`, squared `s` times. -/
def LinearSys.expSquaringFloat (sys : LinearSys 𝕋 n) (tLo tHi : 𝕋) (η s : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let B := sys.expIntervalFloat (half^[s] tLo) (half^[s] tHi) η          -- [e^{A t/2^s}]
  (fun P => (Interval.matMul P P).materialiseMat)^[s] B                  -- squared s times

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
