import CORALean.Arithmetic.Float.ContSet.InflatedContSet.Theorems
import CORALean.Arithmetic.Real.ContSet.Zonotope.Instance

/-!
# Zonotopes over a floating-point scalar

CORA's `zonotope` with its centre and generator matrix, plus the error box that
makes it an `InflatedContSet`. The nominal part is the zonotope those stored
floats describe; the box holds what rounding has cost.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n m h k q r : ℕ}

structure Zonotope (𝕋 : Type) (n : ℕ) where
  h : ℕ
  c : Vec 𝕋 n
  G : Mat 𝕋 n h
  E : Interval 𝕋 n

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (Zonotope 𝕋 n) (CORALean.Arithmetic.Real.Zonotope n) 𝕋 n where
  nominal Z := ⟨Z.h, toRealVec Z.c, toRealMat Z.G⟩
  error Z := Z.E

/-! The nominal zonotope's fields, so proofs can see through the instance. -/

theorem Zonotope.nominal_h [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).h = Z.h := rfl

theorem Zonotope.nominal_c [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).c = toRealVec Z.c := rfl

theorem Zonotope.nominal_G [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).G = toRealMat Z.G := rfl

/-- The nominal set spelt in this zonotope's own fields. Definitional, and the
reason proofs never mention `nominal`: through it every count is `Z.h`, where
going via the instance gives the equal-but-distinct `(nominal Z).h` that `rw`,
`ring` and `linarith` all read as a different term. -/
theorem Zonotope.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {Z : Zonotope 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet Z ↔ ∃ β : Vec ℝ Z.h, (∀ j, |β j| ≤ 1) ∧
      ∀ i, x i = toReal (Z.c i) + ∑ j, toReal (Z.G i j) * β j :=
  Iff.rfl

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev Zonotope.construct [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct Z

/-- What generators known only to within `G` entrywise cost: coefficients range
over `[-1, 1]`, so a row sums with no cancellation. -/
def Zonotope.generatorError (G : Mat 𝕋 n h) : Interval 𝕋 n := Interval.symmetric (radius G)

/-- Storing the lower of the two directed roundings leaves this much to pay. -/
def Zonotope.centerResidual (a b : Vec 𝕋 n) : Interval 𝕋 n :=
  Interval.residual (fun i => addDown (a i) (b i)) (fun i => addUp (a i) (b i))
    (fun i => addDown (a i) (b i))

/-- One generator per coordinate. Not `Matrix.diagonal`, which needs `Zero 𝕋`,
and giving `𝕋` one would collide with ℝ's on the `SoundFloatArithmetic ℝ`
instance. -/
def diagonalBlock (v : Vec 𝕋 n) : Mat 𝕋 n n := fun i l => if i = l then v i else zero

/-- Read as reals it is `Matrix.diagonal`, so the exact layer's lemmas apply. -/
theorem toReal_diagonalBlock [SoundFloatArithmetic 𝕋] (v : Vec 𝕋 n) (i l : Fin n) :
    toReal (diagonalBlock v i l) = Matrix.diagonal (toRealVec v) i l := by
  by_cases hil : i = l
  · rw [diagonalBlock, if_pos hil, hil, Matrix.diagonal_apply_eq]
    rfl
  · rw [diagonalBlock, if_neg hil, Matrix.diagonal_apply_ne _ hil, toReal_zero]

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

/-- CORA's `reduce`, unchanged in shape, and sound for every partition.

Nothing is charged to the box: the centre and the kept generators are copied
exactly, and the diagonal block rounds *up*, which only enlarges a result that
was already an over-approximation. -/
def Zonotope.reduce (Z : Zonotope 𝕋 n) (part : Split (Fin Z.h) into (Fin q) and (Fin r)) :
    Zonotope 𝕋 n where
  h := q + n
  c := Z.c
  G := fun i => Fin.append (fun l => Z.G i (part.left l))
                  (diagonalBlock (radius fun i l => Z.G i (part.right l)) i)
  E := Z.E

/-- Reduce to order `o`, at most `o * n` generators; see the exact layer's
`reduceOrder`, of which this is the rounded twin. -/
def Zonotope.reduceOrder (o : ℕ) (Z : Zonotope 𝕋 n) : Zonotope 𝕋 n :=
  if hlt : o * n < Z.h then
    have hle : (o - 1) * n ≤ Z.h :=
      le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
    Z.reduce ((Partition.split ((o - 1) * n) (Z.h - (o - 1) * n)).reindex
      (finCongr (Nat.add_sub_cancel' hle).symm))
  else Z

/-- `reduce` and `absorbError` in one pass, and the reason to prefer it.

Each alone ends in a diagonal block, and two merge into one with summed radii,
since per coordinate they are independent. Doing both therefore costs the `q + n`
generators `reduce` alone would; run separately they cost `q + n + n`. What
remains in the box is only what the rounded centre shift owes. -/
def Zonotope.reduceAndAbsorb (Z : Zonotope 𝕋 n)
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
