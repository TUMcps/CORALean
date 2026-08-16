import CORALean.Arithmetic.Float.ContSet.InflatedContSet.Theorems
import CORALean.Arithmetic.Real.ContSet.Zonotope.Theorems

/-!
# Zonotopes over a floating-point scalar

CORA's `zonotope` with its centre and generator matrix, plus the error box that
makes it a `InflatedContSet`. The nominal part is the zonotope those stored
floats describe; the box holds what rounding has cost.

`plus` is where the design pays. Generators concatenate exactly — appending two
lists invents no digits — so only the centre rounds, and its `residual` goes
into the box. The generator count is therefore `h + k`, exactly as over ℝ.
Routing the rounding into new generators instead would make every addition cost
`n` more of them, and generator count is what reachability costs.

`absorbError` goes the other way, moving the box into generators about its own
midpoint. The shift is exact over ℝ but its stored centre is not — a box like
`[5, 6]` has midpoint 5.5, which need not be a float — so what the rounded shift
still owes stays behind as a residual rather than vanishing.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

open FloatOps SoundFloatArithmetic

variable {F : Type} [FloatOps F] {n m h k q r : ℕ}

structure Zonotope (F : Type) (n h : ℕ) where
  c : Vec F n
  G : Mat F n h
  E : Interval F n

instance [SoundFloatArithmetic F] :
    InflatedContSet (Zonotope F n h) (CORALean.Arithmetic.Real.Zonotope n h) F n where
  nominal Z := ⟨toRealVec Z.c, toRealMat Z.G⟩
  error Z := Z.E

/-! The nominal zonotope's fields, so proofs can see through the instance. -/

theorem Zonotope.nominal_c [SoundFloatArithmetic F] (Z : Zonotope F n h) :
    (InflatedContSet.nominal Z).c = toRealVec Z.c := rfl

theorem Zonotope.nominal_G [SoundFloatArithmetic F] (Z : Zonotope F n h) :
    (InflatedContSet.nominal Z).G = toRealMat Z.G := rfl

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev Zonotope.construct [SoundFloatArithmetic F] (Z : Zonotope F n h) : Set (Vec ℝ n) :=
  InflatedContSet.construct Z

/-- Generators known only to within `G` entrywise cost this symmetric box: their
coefficients range over `[-1, 1]`, so each row sums with no cancellation and
every generator can conspire.

It is the interval hull of the zonotope centred at zero with generators `G`,
which is why `radius` is the right bound here and in `reduce` alike. -/
def Zonotope.generatorError (G : Mat F n h) : Interval F n := Interval.symmetric (radius G)

/-- The centre sum is bracketed by its two directed roundings; storing the lower
one leaves this much to pay. -/
def Zonotope.centerResidual (a b : Vec F n) : Interval F n :=
  Interval.residual (fun i => addDown (a i) (b i)) (fun i => addUp (a i) (b i))
    (fun i => addDown (a i) (b i))

/-- One generator per coordinate. Spelt out rather than `Matrix.diagonal`, which
needs `Zero F`: giving `F` one would collide with ℝ's on the instance that reads
this layer back as exact arithmetic. -/
def diagonalBlock (v : Vec F n) : Mat F n n := fun i l => if i = l then v i else zero

/-- Read as reals, a diagonal block is Mathlib's `Matrix.diagonal`, which is what
lets the exact layer's lemmas about it apply. -/
theorem toReal_diagonalBlock [SoundFloatArithmetic F] (v : Vec F n) (i l : Fin n) :
    toReal (diagonalBlock v i l) = Matrix.diagonal (toRealVec v) i l := by
  by_cases hil : i = l
  · rw [diagonalBlock, if_pos hil, hil, Matrix.diagonal_apply_eq]
    rfl
  · rw [diagonalBlock, if_neg hil, Matrix.diagonal_apply_ne _ hil, toReal_zero]


/-- The box midpoint added to the centre, rounded each way. The exact midpoint
need not be a float — `[5, 6]` has midpoint 5.5 — so both roundings are kept and
the gap between them is what `absorbError` leaves behind. -/
def Zonotope.shiftDown (Z : Zonotope F n h) : Vec F n :=
  fun i => addDown (Z.c i) (half (addDown (Z.E.inf i) (Z.E.sup i)))

def Zonotope.shiftUp (Z : Zonotope F n h) : Vec F n :=
  fun i => addUp (Z.c i) (half (addUp (Z.E.inf i) (Z.E.sup i)))

/-- The box radius, rounded up. Halving is exact, so only the difference
rounds. -/
def Zonotope.errorRadius (Z : Zonotope F n h) : Vec F n :=
  fun i => half (subUp (Z.E.sup i) (Z.E.inf i))

/-- Trade the box for `n` generators. The set is unchanged over ℝ, but the
shifted centre must be stored as a float, so what the rounding still owes stays
behind rather than the box becoming `[0, 0]`. -/
def Zonotope.absorbError (Z : Zonotope F n h) : Zonotope F n (h + n) where
  c := Z.shiftDown
  G := fun i => Fin.append (Z.G i) (diagonalBlock Z.errorRadius i)
  E := Interval.residual Z.shiftDown Z.shiftUp Z.shiftDown

/-- CORA's `reduce`, unchanged in shape: the partition names the `q` generators
kept and the `r` absorbed into a diagonal block, and soundness holds for every
partition, so selection carries no proof obligation here either.

Nothing is charged to the box. The centre is untouched and the kept generators
are copied, both exact; the diagonal block rounds *up*, which only enlarges a
result that was already an over-approximation. Rounding is free whenever it goes
the way the operation was already going — the same reason `Interval.plus` needs
no box. -/
def Zonotope.reduce (Z : Zonotope F n h) (part : Split (Fin h) into (Fin q) and (Fin r)) :
    Zonotope F n (q + n) where
  c := Z.c
  G := fun i => Fin.append (fun l => Z.G i (part.left l))
                  (diagonalBlock (radius fun i l => Z.G i (part.right l)) i)
  E := Z.E

/-- `reduce` and `absorbError` in one pass, and the reason to prefer it.

Each alone ends in a diagonal block, and two diagonal blocks merge into one with
summed radii — per coordinate they are independent, so `diag a` then `diag b`
reaches exactly what `diag (a + b)` reaches. Doing both therefore costs the
`q + n` generators that `reduce` alone would, and the box is emptied for free.
Running them separately would cost `q + n + n`.

What remains in the box is only what the rounded centre shift still owes, as in
`absorbError`; the radii round up, which is free. -/
def Zonotope.reduceAndAbsorb (Z : Zonotope F n h)
    (part : Split (Fin h) into (Fin q) and (Fin r)) : Zonotope F n (q + n) where
  c := Z.shiftDown
  G := fun i => Fin.append (fun l => Z.G i (part.left l))
                  (diagonalBlock (fun i => addUp (radius (fun i l => Z.G i (part.right l)) i)
                    (Z.errorRadius i)) i)
  E := Interval.residual Z.shiftDown Z.shiftUp Z.shiftDown

/-- CORA's `@zonotope/interval`: the hull `c ± radius G`, then inflated by the
box, since the result has nowhere else to keep it.

Every rounding goes outward and none is charged anywhere — an `Interval` has no
box, so the bounds themselves absorb it. `radius` rounding up widens both ends
at once, which is why the same `radius` serves here as in `reduce`. -/
def Zonotope.interval (Z : Zonotope F n h) : Interval F n where
  inf := fun i => addDown (subDown (Z.c i) (radius Z.G i)) (Z.E.inf i)
  sup := fun i => addUp (addUp (Z.c i) (radius Z.G i)) (Z.E.sup i)

/-! ## Rounded linear algebra

Each entry is a dot product, so a matrix-vector product and a matrix product
differ only in which vector is fed in. Both directions are kept: the stored
value is the lower one, and the gap to the upper is what the box is charged. -/

def mulVecDown (M : Mat F m n) (v : Vec F n) : Vec F m := fun i => dotDown (M i) v
def mulVecUp (M : Mat F m n) (v : Vec F n) : Vec F m := fun i => dotUp (M i) v

def matMulDown (M : Mat F m n) (G : Mat F n h) : Mat F m h :=
  fun i j => dotDown (M i) (fun k => G k j)
def matMulUp (M : Mat F m n) (G : Mat F n h) : Mat F m h :=
  fun i j => dotUp (M i) (fun k => G k j)

/-- How far a stored generator entry can be from the exact product. -/
def matMulDiff (M : Mat F m n) (G : Mat F n h) : Mat F m h :=
  fun i j => subUp (matMulUp M G i j) (matMulDown M G i j)

/-- What `mtimes` owes beyond its nominal part: the centre it could not store
exactly, and the generators it could not either. -/
def Zonotope.mtimesResidual (M : Mat F m n) (Z : Zonotope F n h) : Interval F m :=
  (Interval.residual (mulVecDown M Z.c) (mulVecUp M Z.c) (mulVecDown M Z.c)).plus
    (Zonotope.generatorError (matMulDiff M Z.G))

/-- The generator count is untouched: a linear map neither adds nor removes
generators, and its rounding is paid into the box. The old box travels through
the map as a box, by `Interval.mtimes`. -/
def Zonotope.mtimes (M : Mat F m n) (Z : Zonotope F n h) : Zonotope F m h where
  c := mulVecDown M Z.c
  G := matMulDown M Z.G
  E := (Interval.mtimes M Z.E).plus (Zonotope.mtimesResidual M Z)

def Zonotope.plus (Z₁ : Zonotope F n h) (Z₂ : Zonotope F n k) : Zonotope F n (h + k) where
  c := fun i => addDown (Z₁.c i) (Z₂.c i)
  G := fun i => Fin.append (Z₁.G i) (Z₂.G i)
  E := (Z₁.E.plus Z₂.E).plus (Zonotope.centerResidual Z₁.c Z₂.c)

end CORALean.Arithmetic.Float
