module

public import CORALean.Global.Float.FloatOps
public import CORALean.Global.Interfaces
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Matrix.Diagonal

@[expose] public section

/-!
# What sound floating-point arithmetic gives

The consequences of `SoundFloatArithmetic` (in `Interfaces.lean`): the exact layer's `Scalar` at a
float scalar, with `0`, `1` and negation exact (`ExactScalar`, `NegScalar`), the reading of a stored
ambient type as a real one (`RealImage`) at vectors and matrices, and the bounds the derived
operations inherit: a directed sum, product, extremum or dot product encloses the real one.

## Inputs
* `v` – vector of stored scalars

## Output
* the real vector it reads as, entry by entry
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-! ## Reading arrays -/

def toRealVec (v : Vec 𝕋 n) : Vec ℝ n := fun i => toReal (v i)
/-- A float matrix read entrywise as a real matrix. -/
def toRealMat (M : Mat 𝕋 m n) : Mat ℝ m n := fun i j => toReal (M i j)

/-- `toReal_neg`, for the `-a` that a float vector or matrix negates its entries with. -/
theorem toReal_neg' (a : 𝕋) : toReal (-a) = -toReal a := toReal_neg a

/-- Negating a float vector entrywise reads as negating the real vector. Stated at `Fin n → 𝕋`
rather than `Vec 𝕋 n` so that `simp` indexes it. -/
theorem toRealVec_neg (v : Fin n → 𝕋) : toRealVec (-v) = -toRealVec v :=
  funext fun i => toReal_neg' (v i)

/-- Negating a float matrix entrywise reads as negating the real matrix. -/
theorem toRealMat_neg (M : Mat 𝕋 m n) : toRealMat (-M) = -toRealMat M :=
  funext fun i => funext fun j => toReal_neg' (M i j)

/-- What the exact layer needs of the scalar, and all it needs. The fields are written out
rather than naming `toRealMat`, so that at `𝕋 := ℝ` instance search sees this is ℝ's own. -/
instance : Scalar 𝕋 where
  toRealMat M := fun i j => toReal (M i j)
  toRealVec v := fun i => toReal (v i)
  toReal := toReal
  toRealMat_apply _ _ _ := rfl
  toRealVec_apply _ _ := rfl

/-- The float scalar's own `0` and `1`, which are exact in every format: `Dyadic p`,
`NearestDyadic p`, the IEEE formats and `Float` all go through this one instance. -/
instance : ExactScalar 𝕋 where
  zero := FloatOps.zero
  one := FloatOps.one
  toReal_zero := SoundFloatArithmetic.toReal_zero
  toReal_one := SoundFloatArithmetic.toReal_one

/-- The float scalar's own `neg`, exact in every format. -/
instance : NegScalar 𝕋 where
  toReal_neg := SoundFloatArithmetic.toReal_neg

/-- A float vector denotes the real vector of its entries. -/
instance : RealImage (Vec 𝕋 n) (Vec ℝ n) := ⟨toRealVec⟩

/-- A float matrix denotes the real matrix of its entries. -/
instance : RealImage (Mat 𝕋 m n) (Mat ℝ m n) := ⟨toRealMat⟩

/-- The reading at `Vec`, by name, for a proof that unfolds a generic `nominal`. -/
theorem realImage_vec (v : Vec 𝕋 n) : RealImage.realImage v = toRealVec v := rfl

/-- The reading at `Mat`, by name, for a proof that unfolds a generic `nominal`. -/
theorem realImage_mat (M : Mat 𝕋 m n) : RealImage.realImage M = toRealMat M := rfl

/-! ## What the derived operations inherit -/

/-- The strict margin is positive as a real. -/
theorem toReal_strictMargin_pos : -- --- CONCL ---
    0 < toReal (strictMargin : 𝕋) := by -- --- PROOF ---
  have h : ∀ k : ℕ, 0 < toReal (half^[k] (one : 𝕋)) := by
    intro k
    induction k with
    | zero => rw [Function.iterate_zero_apply, toReal_one]; exact one_pos
    | succ k ih => rw [Function.iterate_succ_apply', toReal_half]; exact half_pos ih
  exact h 64

/-- The margin is positive, so `ltStrict`'s `true` is strict. -/
theorem toReal_lt_of_ltStrict {a b : 𝕋} (h : ltStrict a b = true) : toReal a < toReal b :=
  lt_of_lt_of_le (lt_add_of_pos_right _ toReal_strictMargin_pos)
    (le_trans (add_le_addUp a strictMargin) (toReal_le_of_le h))

/-- `absolute` reads as the absolute value. -/
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

/-- `subUp` is an upper bound of the real difference. -/
theorem sub_le_subUp (a b : 𝕋) : toReal a - toReal b ≤ toReal (subUp a b) := by
  rw [sub_eq_add_neg, ← toReal_neg b, subUp]
  exact add_le_addUp a (neg b)

/-- `subDown` is a lower bound of the real difference. -/
theorem subDown_le_sub (a b : 𝕋) : toReal (subDown a b) ≤ toReal a - toReal b := by
  rw [sub_eq_add_neg, ← toReal_neg b, subDown]
  exact addDown_le_add a (neg b)

/-- An underestimated positive denominator gives an overestimated reciprocal,
and the rounding only grows it further. -/
theorem one_div_le_divUp {d : 𝕋} {y : ℝ} (h1 : 1 ≤ toReal d) (h2 : toReal d ≤ y) :
    1 / y ≤ toReal (divUp one d) := by
  have hd : (0:ℝ) < toReal d := lt_of_lt_of_le zero_lt_one h1
  have hdiv := div_le_divUp one d hd
  rw [toReal_one] at hdiv
  exact le_trans (one_div_le_one_div_of_le hd h2) hdiv

/-- `maximumOver` bounds every entry, which is what lets one box cover a whole
list of roundings. -/
theorem le_maximumOver : -- --- CONCL ---
    ∀ {k : ℕ} (f : Fin k → 𝕋) (l : Fin k),
    toReal (f l) ≤ toReal (maximumOver f) := by -- --- PROOF ---
  intro k
  induction k with
  | zero => exact fun _ l => absurd l.isLt (Nat.not_lt_zero _)
  | succ m ih =>
    intro f l
    cases m with
    | zero => rw [Fin.fin_one_eq_zero l]; exact le_rfl
    | succ m =>
      rw [maximumOver, toReal_maximum]
      refine Fin.cases ?_ (fun l' => ?_) l
      · exact le_max_left _ _
      · exact le_trans (ih (fun i => f i.succ) l') (le_max_right _ _)

/-- And `minimumOver` is under every entry, the reflection of the same fold. -/
theorem minimumOver_le {k : ℕ} (f : Fin k → 𝕋) (l : Fin k) :
    toReal (minimumOver f) ≤ toReal (f l) := by
  rw [minimumOver, toReal_neg, neg_le]
  rw [← toReal_neg]
  exact le_maximumOver (-f) l

/-- A fold of `addUp`, so each partial sum pays one rounding in the same direction. -/
theorem sum_le_sumUp (f : Fin n → 𝕋) : -- --- CONCL ---
    ∑ i, toReal (f i) ≤ toReal (sumUp f) := by -- --- PROOF ---
  induction n with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, sumUp, toReal_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, sumUp]
    exact le_trans (add_le_add (le_refl _) (ih _)) (add_le_addUp _ _)

/-- `sumDown` is a lower bound of the real sum. -/
theorem sumDown_le_sum (f : Fin n → 𝕋) : -- --- CONCL ---
    toReal (sumDown f) ≤ ∑ i, toReal (f i) := by -- --- PROOF ---
  induction n with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, sumDown, toReal_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, sumDown]
    exact le_trans (addDown_le_add _ _) (add_le_add (le_refl _) (ih _))

/-- A count of copies, each addition rounding the way the fold does. -/
theorem le_nsmulUp (k : ℕ) (a : 𝕋) : -- --- CONCL ---
    (k : ℝ) * toReal a ≤ toReal (nsmulUp k a) := by -- --- PROOF ---
  induction k with
  | zero => rw [nsmulUp, toReal_zero, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [nsmulUp, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact le_trans (by linarith) (add_le_addUp a (nsmulUp k a))

/-- `nsmulDown k a` is a lower bound of `k · a`. -/
theorem nsmulDown_le (k : ℕ) (a : 𝕋) : -- --- CONCL ---
    toReal (nsmulDown k a) ≤ (k : ℝ) * toReal a := by -- --- PROOF ---
  induction k with
  | zero => rw [nsmulDown, toReal_zero, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [nsmulDown, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact le_trans (addDown_le_add a (nsmulDown k a)) (by linarith)

/-- Products then sum, the direction preserved through both steps. -/
theorem dotDown_le (a b : Vec 𝕋 n) :
    toReal (dotDown a b) ≤ ∑ k, toReal (a k) * toReal (b k) :=
  le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun _ _ => mulDown_le_mul _ _)

/-- `dotUp` is an upper bound of the real dot product. -/
theorem le_dotUp (a b : Vec 𝕋 n) :
    ∑ k, toReal (a k) * toReal (b k) ≤ toReal (dotUp a b) :=
  le_trans (Finset.sum_le_sum fun _ _ => mul_le_mulUp _ _) (sum_le_sumUp _)

/-- The sum of the absolute entries of row `i` is at most `radius d i`. -/
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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
