import CORALean.Examples.Bench.Rational

/-!
# The exact scalar of the wire format

`ExactScalar` is a scalar off any grid in either of the two shapes the wire format reads: `m*2^e`,
or `m*10^e` at `e < 0`, kept apart from `CORALean.Bench.ExactDyadic` because the latter is
generally not a dyadic. `normalizeExact` and `showExactDyadic` normalise the binary shape on the
way in and out, since a precision check reads a mantissa's width literally. `Codec.lean` parses
and prints it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float CORALean.Bench

/-- `a - b`, exact: `Rational.lean` has `add`/`mul`/`neg`, not `sub`. -/
def ExactDyadic.sub (a b : ExactDyadic) : ExactDyadic := a.add b.neg

/-- `a` compared with `b`, exact: the smaller exponent aligned up, as `add` aligns. -/
def ExactDyadic.cmp (a b : ExactDyadic) : Ordering :=
  if a.exponent ≤ b.exponent then
    compare a.mantissa (b.mantissa * 2 ^ (b.exponent - a.exponent).toNat)
  else
    compare (a.mantissa * 2 ^ (a.exponent - b.exponent).toNat) b.mantissa

def ExactDyadic.isZero (a : ExactDyadic) : Bool := a.mantissa = 0

/-- `d`, its every trailing mantissa bit of zero moved into the exponent: `m` odd, or `⟨0,0⟩`
at zero -- run on the way in as well as the way out, see the module docstring for why. -/
def normalizeExact (d : ExactDyadic) : ExactDyadic :=
  if ExactDyadic.isZero d then ⟨0, 0⟩ else
    let (oddAbs, k) := stripTwos d.mantissa.natAbs
    ⟨if d.mantissa < 0 then -(oddAbs : Int) else (oddAbs : Int), d.exponent + (k : Int)⟩

/-- `d`, normalised: `m` odd, or `"0*2^0"` at zero -- every printed binary scalar. -/
def showExactDyadic (d : ExactDyadic) : String :=
  let d := normalizeExact d
  if ExactDyadic.isZero d then "0*2^0" else s!"{d.mantissa}*2^{d.exponent}"


-- ========================================  MAIN TYPE  ========================================= --

/-- A scalar off any grid, from either wire shape: `m*2^e` (`ExactDyadic`) or `m*10^e` at
`e < 0`, generally not a `.dy` -- see the module docstring. `e ≥ 0` normalises to `.dy` either
way, both being the same integer. -/
inductive ExactScalar where
  | dy (d : ExactDyadic)
  | decNeg (m : Int) (d : Nat)  -- `m * 10 ^ (-d)`, `d > 0`, `m` not a multiple of `10`
deriving Repr

/-- Whether a wire scalar is zero. -/
def ExactScalar.isZero : ExactScalar → Bool
  | .dy d => ExactDyadic.isZero d
  | .decNeg m _ => m = 0

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
