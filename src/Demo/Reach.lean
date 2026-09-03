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

At `Dyadic 24` the second table reads zero throughout: every product and sum
over this horizon is exact, so `mtimes` pays nothing into the box and all the
widening in the first table is order reduction — Girard's rule boxing the
generators it drops. That checks the algorithms and the reduction, but nothing
about directed rounding, which is the reason the float layer exists.

So `main` runs the same system twice, at `Dyadic 24` and at `Dyadic smallP`.
`smallP` is `8`: `A`'s entries need 4 bits and `R₀`/`U`'s need 1, so two steps
of products still fit, and the mantissa first overflows on the third — late
enough to see the exact algorithm run for a while, early enough that four of
the seven rows carry a genuinely rounded box. The error widths climb from
`0` to about `0.045` and `0.037` by the last row, a few percent of the box
itself and nowhere near swamping it, which is what keeps the run legible
rather than an explosion. Everything below is written once, at an implicit
precision `p`, and `reachReport` picks it by which `Dyadic p` it is called at.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace Demo

open CORALean CORALean.Float

/-- The precision the second run rounds at. See the module docstring for why
`8` rather than some other value. -/
def smallP : ℕ := 8

variable (p : ℕ)

/-- `[[15/16, -1/8], [1/8, 15/16]]`, every entry exact in four bits. -/
def A : Mat (Dyadic p) 2 2 := !![dy 15 (-4), dy (-1) (-3); dy 1 (-3), dy 15 (-4)]

def sys : Real.LinearSysDT (Dyadic p) 2 := ⟨A p⟩

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
def R (k : ℕ) : Zonotope (Dyadic p) 2 :=
  (sys p).reach (S := Zonotope (Dyadic p)) order (R₀ p) (U p) k

def reachRow (k : ℕ) : String :=
  let Z := R p k
  pad 4 (toString k) ++ pad 7 (toString Z.h) ++ "  " ++ showBox Z.interval

def errorRow (k : ℕ) : String :=
  let E := (R p k).E
  pad 4 (toString k) ++ "  " ++ pad 14 (showWidth E 0) ++ pad 15 (showWidth E 1)

/-- `y = x₁ + u₂`: a scalar sensor reading one state coordinate, with the second
input coordinate entering it directly. Both matrices are selection rows, so
nothing here rounds and the table is the enclosure alone. -/
def out : Real.OutputEq (Dyadic p) 2 2 1 where
  C := !![dy 1 0, dy 0 0]
  D := !![dy 0 0, dy 1 0]

/-- The output set at step `k`, from the reachable set and the same input set
the step was taken with. -/
def Y (k : ℕ) : Zonotope (Dyadic p) 1 := (out p).outputSet (R p k) (U p)

def outputRow (k : ℕ) : String :=
  let Z := Y p k
  pad 4 (toString k) ++ pad 7 (toString Z.h) ++ "  " ++ showBox Z.interval

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

end Demo
