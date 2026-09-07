import CORALean.ContDynamics.LinearSysDT.Operations
import CORALean.ContDynamics.OutputEq.Operations
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.Examples.Demo.Decimal
import CORALean.Examples.Demo.Scalar

/-!
# `LinearSysDT.reach` at `Dyadic`, run

A damped rotation — `A`'s eigenvalues have modulus `≈ 0.9458` and the input box
is small — so nothing in the *exact* reachable set grows and everything the
tables show growing is the enclosure.

`Zonotope.interval` of the reachable set first, nominal part and error box
together, then the error box alone, which `reduce` never touches, then an
`OutputEq`, `y = x₁ + u₂`. Read the third against the first: every row is that
table's `x1` column widened by exactly the `0.015625` the input contributes on
each side, so a wider row is a widening in `outputSet` rather than in `reach`.

At `Dyadic 24` the error box reads zero throughout. A generator's mantissa gains
the four bits of an `A` entry every step and nothing overflows 24 bits this soon,
so every product and sum is exact and all the widening above is order reduction.
`main` therefore runs the system a second time at `Dyadic smallP`, where `smallP`
is `8`: `A`'s entries need 4 bits and `R₀`/`U`'s need 1, so the mantissa first
overflows on the third step and half the rows carry a rounded box.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Demo

open CORALean CORALean.Float

/-- The precision the second run rounds at. See the module docstring for why
`8` rather than some other value. -/
def smallP : ℕ := 8

variable (p : ℕ)

/-- `[[15/16, -1/8], [1/8, 15/16]]`, every entry exact in four bits. -/
def A : Mat (Dyadic p) 2 2 := !![dy 15 (-4), dy (-1) (-3); dy 1 (-3), dy 15 (-4)]

def sys : LinearSysDT (Dyadic p) 2 := ⟨A p⟩

/-- `[0.875, 1.125] × [-0.125, 0.125]`, as a zonotope with two generators. -/
def R₀ : Zonotope (Dyadic p) 2 where
  h := 2
  c := ![dy 1 0, dy 0 0]
  G := !![dy 1 (-3), dy 0 0; dy 0 0, dy 1 (-3)]
  E := zeroBox 2

/-- `[-1/64, 1/64]²`, the set every step's input is drawn from. -/
def U : Zonotope (Dyadic p) 2 where
  h := 2
  c := ![dy 0 0, dy 0 0]
  G := !![dy 1 (-6), dy 0 0; dy 0 0, dy 1 (-6)]
  E := zeroBox 2

/-- Maximum order: at most `3 * 2` generators survive a step. -/
def order : ℕ := 3

/-- Five: enough rows to carry `Dyadic 8` past the step where its mantissa first
overflows, and short enough that all three tables stay readable at once. -/
def steps : ℕ := 5

/-- The reachable set after `k` steps. Recomputed per row rather than folded, so
a table of `k` rows costs `k²/2` steps where a fold would cost `k`, and every
row is one call to the definition the theorems are about. -/
def R (k : ℕ) : Zonotope (Dyadic p) 2 :=
  (sys p).reach (S := Zonotope (Dyadic p)) order (by decide) (R₀ p) (U p) k

def reachRow (k : ℕ) : String :=
  let Z := R p k
  pad 4 (toString k) ++ pad 7 (toString Z.h) ++ "  " ++ showBox Z.interval

def errorRow (k : ℕ) : String :=
  let E := (R p k).E
  pad 4 (toString k) ++ "  " ++ pad 14 (showWidth E 0) ++ pad 15 (showWidth E 1)

/-- `y = x₁ + u₂`: a scalar sensor reading one state coordinate, with the second
input coordinate entering it directly. Both matrices are selection rows, so
nothing here rounds and the table is the enclosure alone. -/
def out : OutputEq (Dyadic p) 2 2 1 where
  C := !![dy 1 0, dy 0 0]
  D := !![dy 0 0, dy 1 0]

/-- The output set at step `k`, from the reachable set and the same input set
the step was taken with. -/
def Y (k : ℕ) : Zonotope (Dyadic p) 1 := (out p).outputSet (R p k) (U p)

def outputRow (k : ℕ) : String :=
  let Z := Y p k
  pad 4 (toString k) ++ pad 7 (toString Z.h) ++ "  " ++ showBox Z.interval


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The whole report, at whichever precision `p` is called with — `Dyadic 24` for
the exact run, and `Dyadic smallP` for the one that rounds. -/
def reachReport : String :=
  String.intercalate "\n" ([
    "== LinearSysDT.reach at Dyadic " ++ toString p ++ " ==",
    "",
    "A  = [ 15/16  -1/8 ; 1/8  15/16 ]   spectral radius ~ 0.9458",
    "R0 = [0.875, 1.125] x [-0.125, 0.125]",
    "U  = [-0.015625, 0.015625]^2",
    "order o = 3, so a step keeps at most 6 generators",
    "",
    "Zonotope.interval of the reachable set, nominal part and error box together:",
    "",
    "   k  gens  x1                              x2"] ++
    -- `steps + 1` rows, since step 0 is the initial set and is worth showing
    (List.range (steps + 1)).map (reachRow p) ++ [
    "",
    "the error box alone, as a width per coordinate:",
    "",
    "   k  width 1       width 2"] ++
    (List.range (steps + 1)).map (errorRow p) ++ [
    "",
    "OutputEq.outputSet for y = x1 + u2, as Zonotope.interval:",
    "",
    "   k  gens  y"] ++
    (List.range (steps + 1)).map (outputRow p))

end CORALean.Demo


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
