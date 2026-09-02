import CORALean.Global.Float.FloatOps
import CORALean.Global.Scalar

/-!
# Sound floating-point arithmetic

What the layer assumes of its scalar: a real interpretation `toReal`, and
`FloatOps` rounding in the direction its name claims. No format is fixed, so the
proofs hold for binary64, for any other precision, and for ℝ itself.

Not IEEE 754 — rounding *to nearest* bounds nothing in a stated direction. How
the direction is achieved is left open: a hardware rounding mode and nearest
plus one ulp outward both discharge these obligations.

`toReal` is total into ℝ, so no instance has NaN or an infinity. Overflow is
assumed away rather than modelled, and an implementation owes a range argument;
that is the one gap between these axioms and a machine.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

class SoundFloatArithmetic (𝕋 : Type) [FloatOps 𝕋] where
  toReal : 𝕋 → ℝ
  toReal_neg (a : 𝕋) : toReal (neg a) = -toReal a
  toReal_zero : toReal (zero : 𝕋) = 0
  add_le_addUp (a b : 𝕋) : toReal a + toReal b ≤ toReal (addUp a b)
  addDown_le_add (a b : 𝕋) : toReal (addDown a b) ≤ toReal a + toReal b
  mul_le_mulUp (a b : 𝕋) : toReal a * toReal b ≤ toReal (mulUp a b)
  mulDown_le_mul (a b : 𝕋) : toReal (mulDown a b) ≤ toReal a * toReal b
  toReal_minimum (a b : 𝕋) : toReal (minimum a b) = min (toReal a) (toReal b)
  toReal_maximum (a b : 𝕋) : toReal (maximum a b) = max (toReal a) (toReal b)
  toReal_half (a : 𝕋) : toReal (half a) = toReal a / 2

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m h : ℕ}

/-! ## Reading arrays -/

def toRealVec (v : Vec 𝕋 n) : Vec ℝ n := fun i => toReal (v i)
def toRealMat (M : Mat 𝕋 m n) : Mat ℝ m n := fun i j => toReal (M i j)

/-- What the exact layer needs of the scalar, and all it needs. -/
instance : Scalar 𝕋 where
  toRealMat M := CORALean.Float.toRealMat M

/-! ## What the derived operations inherit -/

theorem toReal_absolute (a : 𝕋) : toReal (absolute a) = |toReal a| := by
  rw [absolute, toReal_maximum, toReal_neg]
  exact (abs_eq_max_neg).symm

/-- Read as reals it is `Matrix.diagonal`, so the exact layer's lemmas apply. -/
theorem toReal_diagonalBlock (v : Vec 𝕋 n) (i l : Fin n) :
    toReal (diagonalBlock v i l) = Matrix.diagonal (toRealVec v) i l := by
  by_cases hil : i = l
  · rw [diagonalBlock, if_pos hil, hil, Matrix.diagonal_apply_eq]
    rfl
  · rw [diagonalBlock, if_neg hil, Matrix.diagonal_apply_ne _ hil, toReal_zero]

theorem sub_le_subUp (a b : 𝕋) : toReal a - toReal b ≤ toReal (subUp a b) := by
  rw [sub_eq_add_neg, ← toReal_neg b, subUp]
  exact add_le_addUp a (neg b)

theorem subDown_le_sub (a b : 𝕋) : toReal (subDown a b) ≤ toReal a - toReal b := by
  rw [sub_eq_add_neg, ← toReal_neg b, subDown]
  exact addDown_le_add a (neg b)

/-- `maximumOver` bounds every entry, which is what lets one box cover a whole
list of roundings. -/
theorem le_maximumOver : ∀ {k : ℕ} (f : Fin k → 𝕋) (l : Fin k),
    toReal (f l) ≤ toReal (maximumOver f) := by
  intro k
  induction k with
  | zero => exact fun _ l => absurd l.isLt (Nat.not_lt_zero _)
  | succ m ih =>
    intro f l
    rw [maximumOver, toReal_maximum]
    refine Fin.cases ?_ (fun l' => ?_) l
    · exact le_max_left _ _
    · exact le_trans (ih (fun i => f i.succ) l') (le_max_right _ _)

theorem sum_le_sumUp (f : Fin n → 𝕋) : ∑ i, toReal (f i) ≤ toReal (sumUp f) := by
  induction n with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, sumUp, toReal_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, sumUp]
    exact le_trans (add_le_add (le_refl _) (ih _)) (add_le_addUp _ _)

theorem sumDown_le_sum (f : Fin n → 𝕋) : toReal (sumDown f) ≤ ∑ i, toReal (f i) := by
  induction n with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, sumDown, toReal_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, sumDown]
    exact le_trans (addDown_le_add _ _) (add_le_add (le_refl _) (ih _))

/-- Products then sum, the direction preserved through both steps. -/
theorem dotDown_le (a b : Vec 𝕋 n) :
    toReal (dotDown a b) ≤ ∑ k, toReal (a k) * toReal (b k) :=
  le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun _ _ => mulDown_le_mul _ _)

theorem le_dotUp (a b : Vec 𝕋 n) :
    ∑ k, toReal (a k) * toReal (b k) ≤ toReal (dotUp a b) :=
  le_trans (Finset.sum_le_sum fun _ _ => mul_le_mulUp _ _) (sum_le_sumUp _)

theorem sum_abs_le_radius {d : Mat 𝕋 n h} (i : Fin n) :
    ∑ j, |toReal (d i j)| ≤ toReal (radius d i) :=
  calc ∑ j, |toReal (d i j)|
      = ∑ j, toReal (absolute (d i j)) :=
        Finset.sum_congr rfl fun _ _ => (toReal_absolute _).symm
    _ ≤ toReal (radius d i) := sum_le_sumUp _

/-- What a matrix known only to within `d` entrywise can reach on the unit ball;
`d` exact is the special case. -/
theorem abs_sum_le_radius {d : Mat 𝕋 n h} {Δ : Mat ℝ n h} {β : Vec ℝ h}
    (hd : ∀ i j, |Δ i j| ≤ |toReal (d i j)|) (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ j, Δ i j * β j| ≤ toReal (radius d i) :=
  calc |∑ j, Δ i j * β j|
      ≤ ∑ j, |Δ i j * β j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |toReal (d i j)| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact le_trans (mul_le_of_le_one_right (abs_nonneg _) (hβ j)) (hd i j)
    _ ≤ toReal (radius d i) := sum_abs_le_radius i

end CORALean.Float
