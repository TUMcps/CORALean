import CORALean.Arithmetic.Float.ContSet.Zonotope.Helper.API

/-!
# Zonotopes over a floating-point scalar: the operations

CORA's `zonotope` operations over the structure in `Structure`. Each pays its
rounding into the error box rather than into new generators, except where a
diagonal block is being appended anyway.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n m h k q r : ℕ}

/-- What generators known only to within `G` entrywise cost: coefficients range
over `[-1, 1]`, so a row sums with no cancellation. -/
def Zonotope.generatorError (G : Mat 𝕋 n h) : Interval 𝕋 n := Interval.symmetric (radius G)

/-- Storing the lower of the two directed roundings leaves this much to pay. -/
def Zonotope.centerResidual (a b : Vec 𝕋 n) : Interval 𝕋 n :=
  Interval.residual (fun i => addDown (a i) (b i)) (fun i => addUp (a i) (b i))
    (fun i => addDown (a i) (b i))

/-- The box midpoint added to the centre, rounded each way. The exact midpoint
need not be a float — `[5, 6]` gives 5.5 — so the gap between the two roundings
is what `absorbError` leaves behind. -/
def Zonotope.shiftDown (Z : Zonotope 𝕋 n) : Vec 𝕋 n :=
  fun i => addDown (Z.c i) (half (addDown (Z.E.inf i) (Z.E.sup i)))

def Zonotope.shiftUp (Z : Zonotope 𝕋 n) : Vec 𝕋 n :=
  fun i => addUp (Z.c i) (half (addUp (Z.E.inf i) (Z.E.sup i)))

/-- The box radius, rounded up; halving is exact, so only the difference rounds. -/
def Zonotope.errorRadius (Z : Zonotope 𝕋 n) : Vec 𝕋 n :=
  fun i => half (subUp (Z.E.sup i) (Z.E.inf i))

/-- Trade the box for `n` generators about its own midpoint. Over ℝ this moves
nothing; here the shifted centre must be stored as a float, so the box is left
holding what that rounding still owes rather than becoming `[0, 0]`. -/
def Zonotope.absorbError (Z : Zonotope 𝕋 n) : Zonotope 𝕋 n where
  h := Z.h + n
  c := Z.shiftDown
  G := fun i => Fin.append (Z.G i) (diagonalBlock Z.errorRadius i)
  E := Interval.residual Z.shiftDown Z.shiftUp Z.shiftDown

/-- CORA's `reduce`: to a maximum order, by whichever rule the representation
sees fit. Girard's is the one here, as over ℝ, and which it is goes no further —
a caller names an order and gets an over-approximation. -/
def Zonotope.reduce (Z : Zonotope 𝕋 n) (o : ℕ) : Zonotope 𝕋 n :=
  Z.reduceGirard o

/-- `reduceBy` and `absorbError` in one pass, and the reason to prefer it.

Each alone ends in a diagonal block, and two merge into one with summed radii,
since per coordinate they are independent. Doing both therefore costs the `q + n`
generators `reduceBy` alone would; run separately they cost `q + n + n`. What
remains in the box is only what the rounded centre shift owes. -/
def Zonotope.reduceAndAbsorbBy (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) : Zonotope 𝕋 n where
  h := q + n
  c := Z.shiftDown
  G := fun i => Fin.append (fun l => Z.G i (part.left l))
                  (diagonalBlock (fun i => addUp (radius (fun i l => Z.G i (part.right l)) i)
                    (Z.errorRadius i)) i)
  E := Interval.residual Z.shiftDown Z.shiftUp Z.shiftDown

/-- CORA's `@zonotope/interval`: the hull `c ± radius G`, inflated by the box.
An `Interval` has no box, so the bounds themselves absorb every rounding. -/
def Zonotope.interval (Z : Zonotope 𝕋 n) : Interval 𝕋 n where
  inf := fun i => addDown (subDown (Z.c i) (radius Z.G i)) (Z.E.inf i)
  sup := fun i => addUp (addUp (Z.c i) (radius Z.G i)) (Z.E.sup i)

/-- What `mtimes` owes beyond its nominal part: the centre, and the generators. -/
def Zonotope.mtimesResidual (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) : Interval 𝕋 m :=
  (Interval.residual (mulVecDown M Z.c) (mulVecUp M Z.c) (mulVecDown M Z.c)).plus
    (Zonotope.generatorError (matMulDiff M Z.G))

/-- The generator count is untouched, the rounding being paid into the box; the
old box travels through the map as a box, by `Interval.mtimes`. -/
def Zonotope.mtimes (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) : Zonotope 𝕋 m where
  h := Z.h
  c := mulVecDown M Z.c
  G := matMulDown M Z.G
  E := (Interval.mtimes M Z.E).plus (Zonotope.mtimesResidual M Z)

/-- Generators concatenate exactly, so only the centre rounds and its `residual`
goes into the box, leaving the count at `h + k` as over ℝ. Paying into new
generators instead would cost `n` more on every addition. -/
def Zonotope.plus (Z₁ Z₂ : Zonotope 𝕋 n) : Zonotope 𝕋 n where
  h := Z₁.h + Z₂.h
  c := fun i => addDown (Z₁.c i) (Z₂.c i)
  G := fun i => Fin.append (Z₁.G i) (Z₂.G i)
  E := (Z₁.E.plus Z₂.E).plus (Zonotope.centerResidual Z₁.c Z₂.c)

end CORALean.Arithmetic.Float
