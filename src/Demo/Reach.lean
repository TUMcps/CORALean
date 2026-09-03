import CORALean.ContDynamics.LinearSysDT.Operations
import CORALean.ContDynamics.OutputEq.Operations
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Zonotope.Float.Instances
import Demo.Decimal
import Demo.Scalar

/-!
# `LinearSysDT.reach` at `Dyadic`, run

The system is a damped rotation, chosen so that nothing in the *exact* reachable
set grows: `A` has eigenvalues of modulus `√((15/16)² + (1/8)²) ≈ 0.9458`, and
the input set is a small box, so the true reachable sets converge to a bounded
attractor. Everything the table shows growing is therefore the enclosure and not
the system.

The first two tables are the two halves of what a float zonotope carries. The
first is `Zonotope.interval` of the reachable set — the nominal part and the
error box together, the box a specification would actually be checked against.
The second is the error box alone, which is what `reduce` never touches.

The third is an `OutputEq`: a one-dimensional sensor reading the first state
coordinate and the second input coordinate, `y = x₁ + u₂`. Read it against the
first table — every row is that table's `x1` column widened by exactly the
`0.015625` the input contributes on each side, `mtimes` at a row of a selection
matrix and `plus` on two zonotopes both being exact here. A row wider than that
would be a widening in `outputSet` rather than in `reach`.

The second table reads zero throughout, and that is a result rather than a bug:
at 24 bits and this horizon every product and sum is exact, so `mtimes` pays
nothing into the box and all the widening in the first table is order
reduction — Girard's rule boxing the generators it drops. Rounding starts to
bite where a generator's mantissa reaches 24 bits, which on this system is one
or two steps past the last row. A run that makes the box grow wants a smaller
`p`, and is the obvious thing to add next.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace Demo

open CORALean CORALean.Float

/-- `[[15/16, -1/8], [1/8, 15/16]]`, every entry exact in four bits. -/
def A : Mat D 2 2 := !![dy 15 (-4), dy (-1) (-3); dy 1 (-3), dy 15 (-4)]

def sys : Real.LinearSysDT D 2 := ⟨A⟩

/-- `[0.875, 1.125] × [-0.125, 0.125]`, as a zonotope with two generators. -/
def R₀ : Zonotope D 2 where
  h := 2
  c := ![dy 1 0, dy 0 0]
  G := !![dy 1 (-3), dy 0 0; dy 0 0, dy 1 (-3)]
  E := zeroBox 2

/-- `[-1/64, 1/64]²`, the set every step's input is drawn from. -/
def U : Zonotope D 2 where
  h := 2
  c := ![dy 0 0, dy 0 0]
  G := !![dy 1 (-6), dy 0 0; dy 0 0, dy 1 (-6)]
  E := zeroBox 2

/-- Maximum order: at most `3 * 2` generators survive a step. -/
def order : ℕ := 3

/-- Six, and the ceiling is evaluation cost rather than anything about the sets.
`Vec` and `Mat` are function types, so a generator entry of step `k` is a
closure over step `k-1` and nothing memoizes it: every use walks the whole
history again. Measured on this system, steps 0 to 6 print in well under a
second and steps 7 to 10 take five and three quarter minutes between them, the
cost roughly tripling per step. -/
def steps : ℕ := 6

/-- The reachable set after `k` steps. Recomputed per row rather than folded,
which costs `k²` steps of a twelve-step run and keeps the table one call to the
definition the theorems are about. -/
def R (k : ℕ) : Zonotope D 2 := sys.reach (S := Zonotope D) order R₀ U k

def reachRow (k : ℕ) : String :=
  let Z := R k
  pad 4 (toString k) ++ pad 7 (toString Z.h) ++ "  " ++ showBox Z.interval

def errorRow (k : ℕ) : String :=
  let E := (R k).E
  pad 4 (toString k) ++ "  " ++ pad 14 (showWidth E 0) ++ pad 15 (showWidth E 1)

/-- `y = x₁ + u₂`: a scalar sensor reading one state coordinate, with the second
input coordinate entering it directly. Both matrices are selection rows, so
nothing here rounds and the table is the enclosure alone. -/
def out : Real.OutputEq D 2 2 1 where
  C := !![dy 1 0, dy 0 0]
  D := !![dy 0 0, dy 1 0]

/-- The output set at step `k`, from the reachable set and the same input set
the step was taken with. -/
def Y (k : ℕ) : Zonotope D 1 := out.outputSet (R k) U

def outputRow (k : ℕ) : String :=
  let Z := Y k
  pad 4 (toString k) ++ pad 7 (toString Z.h) ++ "  " ++ showBox Z.interval

def reachReport : String :=
  String.intercalate "\n" ([
    "== LinearSysDT.reach at Dyadic 24 ==",
    "",
    "A  = [ 15/16  -1/8 ; 1/8  15/16 ]   spectral radius ~ 0.9458",
    "R0 = [0.875, 1.125] x [-0.125, 0.125]",
    "U  = [-0.015625, 0.015625]^2",
    "order o = 3, so a step keeps at most 6 generators",
    "",
    "Zonotope.interval of the reachable set, nominal part and error box together:",
    "",
    "   k  gens  x1                              x2"] ++
    (List.range (steps + 1)).map reachRow ++ [
    "",
    "the error box alone, as a width per coordinate:",
    "",
    "   k  width 1       width 2"] ++
    (List.range (steps + 1)).map errorRow ++ [
    "",
    "OutputEq.outputSet for y = x1 + u2, as Zonotope.interval:",
    "",
    "   k  gens  y"] ++
    (List.range (steps + 1)).map outputRow)

end Demo
