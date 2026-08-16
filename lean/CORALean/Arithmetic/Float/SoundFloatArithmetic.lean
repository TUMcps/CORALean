import CORALean.Arithmetic.Float.FloatOps

/-!
# Sound floating-point arithmetic

What the floating-point layer assumes of its scalar: a real interpretation
`toReal`, and `FloatOps` that rounds in the direction its name claims — `addUp`
never returns less than the exact sum, `addDown` never more. Nothing here fixes
a format, so the proofs above it hold for binary64, for any other precision, and
for the exact arithmetic of `Arithmetic.Real`.

Deliberately not IEEE 754. Rounding *to nearest* is not enough to bound anything
in a stated direction, and the axioms say nothing about how the bound is
achieved: an implementation may set the hardware rounding mode, or round to
nearest and step one ulp outward. Either discharges these obligations.

Since `toReal` is total and lands in ℝ, no instance can represent NaN or an
infinity. Overflow is thereby assumed away rather than modelled, and an
implementation owes a range argument for that. It is the one gap between these
axioms and a machine.

A mixin over `FloatOps` rather than an extension of it: as a parent field the
operations would sit inside a structure that `toReal` makes noncomputable, and
nothing reached through the class could run.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

open FloatOps

class SoundFloatArithmetic (F : Type) [FloatOps F] where
  toReal : F → ℝ
  toReal_neg (a : F) : toReal (neg a) = -toReal a
  toReal_zero : toReal (zero : F) = 0
  add_le_addUp (a b : F) : toReal a + toReal b ≤ toReal (addUp a b)
  addDown_le_add (a b : F) : toReal (addDown a b) ≤ toReal a + toReal b
  mul_le_mulUp (a b : F) : toReal a * toReal b ≤ toReal (mulUp a b)
  mulDown_le_mul (a b : F) : toReal (mulDown a b) ≤ toReal a * toReal b
  toReal_minimum (a b : F) : toReal (minimum a b) = min (toReal a) (toReal b)
  toReal_maximum (a b : F) : toReal (maximum a b) = max (toReal a) (toReal b)
  toReal_half (a : F) : toReal (half a) = toReal a / 2

open SoundFloatArithmetic

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n m h : ℕ}

/-! ## Reading arrays

Pointwise, so a representation's fields denote the real array they describe and
nothing else has to be said about shape. -/

def toRealVec (v : Vec F n) : Vec ℝ n := fun i => toReal (v i)
def toRealMat (M : Mat F m n) : Mat ℝ m n := fun i j => toReal (M i j)

/-! ## What the derived operations inherit -/

theorem toReal_absolute (a : F) : toReal (absolute a) = |toReal a| := by
  rw [absolute, toReal_maximum, toReal_neg]
  exact (abs_eq_max_neg).symm

theorem sub_le_subUp (a b : F) : toReal a - toReal b ≤ toReal (subUp a b) := by
  rw [sub_eq_add_neg, ← toReal_neg b, subUp]
  exact add_le_addUp a (neg b)

theorem subDown_le_sub (a b : F) : toReal (subDown a b) ≤ toReal a - toReal b := by
  rw [sub_eq_add_neg, ← toReal_neg b, subDown]
  exact addDown_le_add a (neg b)

theorem sum_le_sumUp (f : Fin n → F) : ∑ i, toReal (f i) ≤ toReal (sumUp f) := by
  induction n with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, sumUp, toReal_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, sumUp]
    exact le_trans (add_le_add (le_refl _) (ih _)) (add_le_addUp _ _)

theorem sumDown_le_sum (f : Fin n → F) : toReal (sumDown f) ≤ ∑ i, toReal (f i) := by
  induction n with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, sumDown, toReal_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, sumDown]
    exact le_trans (addDown_le_add _ _) (add_le_add (le_refl _) (ih _))

/-- A rounded dot product brackets the exact one: products then sum, each
direction preserved through both steps. -/
theorem dotDown_le (a b : Vec F n) :
    toReal (dotDown a b) ≤ ∑ k, toReal (a k) * toReal (b k) :=
  le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun _ _ => mulDown_le_mul _ _)

theorem le_dotUp (a b : Vec F n) :
    ∑ k, toReal (a k) * toReal (b k) ≤ toReal (dotUp a b) :=
  le_trans (Finset.sum_le_sum fun _ _ => mul_le_mulUp _ _) (sum_le_sumUp _)

/-- What a matrix can reach on the unit ball, which is what `radius` bounds. The
matrix is given only to within `d` entrywise, so this covers both an exact
matrix and one known by enclosure. -/
theorem abs_sum_le_radius {d : Mat F n h} {Δ : Mat ℝ n h} {β : Vec ℝ h}
    (hd : ∀ i j, |Δ i j| ≤ |toReal (d i j)|) (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ j, Δ i j * β j| ≤ toReal (radius d i) :=
  calc |∑ j, Δ i j * β j|
      ≤ ∑ j, |Δ i j * β j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |toReal (d i j)| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact le_trans (mul_le_of_le_one_right (abs_nonneg _) (hβ j)) (hd i j)
    _ = ∑ j, toReal (absolute (d i j)) :=
        Finset.sum_congr rfl fun j _ => (toReal_absolute _).symm
    _ ≤ toReal (radius d i) := sum_le_sumUp _

end CORALean.Arithmetic.Float
