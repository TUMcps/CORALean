import CORALean.Examples.Bench.NearestUnsound.API
import CORALean.Global.Float.Instances.Binary64.API
import CORALean.Examples.Oracle.Run

/-!
# `lake exe oracle-unsound`: the oracle with round-to-nearest, WITHOUT guarantees

`lake exe oracle`'s protocol and ops, plus the dtype `nearest`: native binary64 whose four rounded
operations are the machine's round-to-nearest, both directions alike (`NearestFloat`). It is what
CORA computes with, and it bounds nothing. Its use is to compare a CORA.cpp run bit for bit with the
same algorithm and arithmetic, so that a difference can only be an algorithmic one.

It lives here, and is a separate executable, because `NearestFloat`'s instances rest on the one
false axiom of `NearestUnsound/Axioms.lean`: only files under `Examples/Bench/` may import it, and
the sound `oracle` must never reach it. Every dtype of the sound oracle is served here too.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench.OracleUnsound

open CORALean CORALean.Float CORALean.Oracle CORALean.Bench.NearestUnsound


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `x` as an exact dyadic: the number its bits denote. -/
def aux_dyadicOf (x : Float) : ExactDyadic :=
  let d := Binary64.toDyadic x
  ⟨d.mantissa, d.exponent⟩

/-- `roundTo` is not offered for `nearest`, which has no exact rounding of its own. -/
def aux_nativeRoundTo {𝕋 : Type} : String → ExactScalar → Except String (𝕋 × 𝕋 × 𝕋) :=
  fun _ _ => throw "roundTo: not supported for nearest"

/-- The message for a negative decimal exponent: `1/50` is no binary number. -/
def aux_decNegRefused (field : String) (m : Int) (d : Nat) : String :=
  s!"field `{field}`: {m}*10^-{d} is a decimal fraction, not exactly representable in binary"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `nearest`: `NearestFloat` read and printed exactly; `roundTo` is not offered. -/
def nearestDtypeOps : DtypeOps NearestFloat where
  label := "nearest"
  readExact field
    | .dy d => (ExactDyadic.toFloat field d).map (⟨·⟩)
    | .decNeg m d => throw (aux_decNegRefused field m d)
  roundToScalar := aux_nativeRoundTo
  showExact x := showExactDyadic (aux_dyadicOf x.val)

/-- The dtypes of `oracle-unsound`: those of `oracle`, and `nearest`. -/
def dtypes : DtypeSet where
  forms := sounds.forms ++ ["nearest"]
  resolve := fun {_} dtypeStr k =>
    if dtypeStr = "nearest" then k (𝕋 := NearestFloat) nearestDtypeOps
    else sounds.resolve dtypeStr k

end CORALean.Bench.OracleUnsound

def main : IO Unit := CORALean.Oracle.run CORALean.Bench.OracleUnsound.dtypes


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
