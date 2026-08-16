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

variable {F : Type} [FloatOps F] {n m h k : ℕ}

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

/-- The centre sum is bracketed by its two directed roundings; storing the lower
one leaves this much to pay. -/
def Zonotope.centerResidual (a b : Vec F n) : Interval F n :=
  Interval.residual (fun i => addDown (a i) (b i)) (fun i => addUp (a i) (b i))
    (fun i => addDown (a i) (b i))

/-- One generator per coordinate. Spelt out rather than `Matrix.diagonal`, which
needs `Zero F`: giving `F` one would collide with ℝ's on the instance that reads
this layer back as exact arithmetic. -/
def diagonalBlock (v : Vec F n) : Mat F n n := fun i l => if i = l then v i else zero

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
    (Interval.generatorError (matMulDiff M Z.G))

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
