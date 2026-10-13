module

public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.MeasurableSpace.Pi

@[expose] public section

/-!
# A measurable member of a box mapping a measurable vector to a measurable one

Where some member of the box maps `y(s)` to `w(s)`, one does measurably in `s`:
chosen by a formula rather than by choice. Row by row, the least and greatest
value a row of the box takes against `y(s)` are attained at the corner rows, each
entry at the endpoint the sign of `y(s)`'s coordinate picks; `w(s)` lies between
them, so it is one convex combination of the two corner rows, with a weight that
is a quotient of measurable functions. Off the set where a member exists, any
fixed member of the box serves.

What lets a time-varying parameter that `Trajectory` asks nothing of be replaced
by one an integral can take.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The endpoint of entry `(i, l)` that minimises its product with `y l`. -/
noncomputable def aux_cornerLo (B : Interval (Mat ℝ n n)) (y : Vec ℝ n) (i l : Fin n) : ℝ :=
  if 0 ≤ y l then B.inf i l else B.sup i l

/-- The endpoint that maximises it. -/
noncomputable def aux_cornerHi (B : Interval (Mat ℝ n n)) (y : Vec ℝ n) (i l : Fin n) : ℝ :=
  if 0 ≤ y l then B.sup i l else B.inf i l

/-- Where `w i` sits between the two corner rows' values against `y`. -/
noncomputable def aux_weight (B : Interval (Mat ℝ n n)) (y w : Vec ℝ n) (i : Fin n) : ℝ :=
  if ∑ l, aux_cornerHi B y i l * y l = ∑ l, aux_cornerLo B y i l * y l then 0
  else (w i - ∑ l, aux_cornerLo B y i l * y l)
    / (∑ l, aux_cornerHi B y i l * y l - ∑ l, aux_cornerLo B y i l * y l)

/-- The selected member: each row the weighted combination of its corner rows. -/
noncomputable def aux_select (B : Interval (Mat ℝ n n)) (y w : Vec ℝ n) : Mat ℝ n n :=
  fun i l => aux_cornerLo B y i l
    + aux_weight B y w i * (aux_cornerHi B y i l - aux_cornerLo B y i l)

/-- Every member's row lies between the corner rows against `y`. -/
theorem aux_corner_between {B : Interval (Mat ℝ n n)} {M : Mat ℝ n n} (hM : M ∈ B.construct)
    (y : Vec ℝ n) (i : Fin n) :
    ∑ l, aux_cornerLo B y i l * y l ≤ (M *ᵥ y) i ∧
      (M *ᵥ y) i ≤ ∑ l, aux_cornerHi B y i l * y l := by -- --- PROOF ---
  have h := Interval.mem_mat_iff.mp hM
  simp only [Matrix.mulVec, dotProduct]
  constructor <;> refine Finset.sum_le_sum fun l _ => ?_ <;>
    simp only [aux_cornerLo, aux_cornerHi] <;> split_ifs with hy
  · exact mul_le_mul_of_nonneg_right (h i l).1 hy
  · exact mul_le_mul_of_nonpos_right (h i l).2 (le_of_lt (not_le.mp hy))
  · exact mul_le_mul_of_nonneg_right (h i l).2 hy
  · exact mul_le_mul_of_nonpos_right (h i l).1 (le_of_lt (not_le.mp hy))

/-- The weight lies in `[0, 1]` whenever `w i` lies between the corner values. -/
theorem aux_weight_mem {B : Interval (Mat ℝ n n)} {y w : Vec ℝ n} {i : Fin n}
    (hlo : ∑ l, aux_cornerLo B y i l * y l ≤ w i)
    (hhi : w i ≤ ∑ l, aux_cornerHi B y i l * y l) :
    0 ≤ aux_weight B y w i ∧ aux_weight B y w i ≤ 1 := by -- --- PROOF ---
  unfold aux_weight
  split_ifs with heq
  · exact ⟨le_rfl, zero_le_one⟩
  · have hpos : 0 < ∑ l, aux_cornerHi B y i l * y l - ∑ l, aux_cornerLo B y i l * y l :=
      sub_pos.mpr (lt_of_le_of_ne (hlo.trans hhi) (Ne.symm heq))
    exact ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).mpr (by linarith)⟩

/-- The selection maps `y` to `w`, `w` between the corner values row by row. -/
theorem aux_select_mulVec {B : Interval (Mat ℝ n n)} {y w : Vec ℝ n}
    (hw : ∀ i, ∑ l, aux_cornerLo B y i l * y l ≤ w i ∧ w i ≤ ∑ l, aux_cornerHi B y i l * y l) :
    aux_select B y w *ᵥ y = w := by -- --- PROOF ---
  funext i
  have hsum : (aux_select B y w *ᵥ y) i = ∑ l, aux_cornerLo B y i l * y l
      + aux_weight B y w i
        * (∑ l, aux_cornerHi B y i l * y l - ∑ l, aux_cornerLo B y i l * y l) := by
    simp only [Matrix.mulVec, dotProduct, aux_select, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
  rw [hsum]
  unfold aux_weight
  split_ifs with heq
  · -- the two corner values agree, and `w i` is squeezed onto them
    linarith [(hw i).1, (hw i).2]
  · have hne : ∑ l, aux_cornerHi B y i l * y l - ∑ l, aux_cornerLo B y i l * y l ≠ 0 :=
      sub_ne_zero.mpr heq
    field_simp
    ring

/-- The selection lies in the box, the box being non-empty. -/
theorem aux_select_mem {B : Interval (Mat ℝ n n)} {M : Mat ℝ n n} (hM : M ∈ B.construct)
    {y w : Vec ℝ n}
    (hw : ∀ i, ∑ l, aux_cornerLo B y i l * y l ≤ w i ∧ w i ≤ ∑ l, aux_cornerHi B y i l * y l) :
    aux_select B y w ∈ B.construct := by -- --- PROOF ---
  have hB : ∀ i l, B.inf i l ≤ B.sup i l := fun i l =>
    (Interval.mem_mat_iff.mp hM i l).1.trans (Interval.mem_mat_iff.mp hM i l).2
  refine Interval.mem_mat_iff.mpr fun i l => ?_
  obtain ⟨h0, h1⟩ := aux_weight_mem (hw i).1 (hw i).2
  -- a convex combination of the two endpoints, in whichever order the sign gives
  simp only [aux_select, aux_cornerLo, aux_cornerHi]
  split_ifs
  · constructor <;> nlinarith [hB i l]
  · constructor <;> nlinarith [hB i l]

/-- Measurable in time, given measurable `y` and `w`. -/
theorem aux_select_measurable (B : Interval (Mat ℝ n n)) {y w : ℝ → Vec ℝ n}
    (hy : Measurable y) (hw : Measurable w) (i l : Fin n) :
    Measurable fun s => aux_select B (y s) (w s) i l := by -- --- PROOF ---
  have hyl : ∀ l, Measurable fun s => y s l := fun l => (measurable_pi_apply l).comp hy
  have hwi : ∀ i, Measurable fun s => w s i := fun i => (measurable_pi_apply i).comp hw
  have hlo : ∀ i l, Measurable fun s => aux_cornerLo B (y s) i l := fun i l =>
    Measurable.ite (measurableSet_le measurable_const (hyl l)) measurable_const measurable_const
  have hhi : ∀ i l, Measurable fun s => aux_cornerHi B (y s) i l := fun i l =>
    Measurable.ite (measurableSet_le measurable_const (hyl l)) measurable_const measurable_const
  have hLo : ∀ i, Measurable fun s => ∑ l, aux_cornerLo B (y s) i l * y s l := fun i =>
    Finset.measurable_fun_sum _ fun l _ => (hlo i l).mul (hyl l)
  have hHi : ∀ i, Measurable fun s => ∑ l, aux_cornerHi B (y s) i l * y s l := fun i =>
    Finset.measurable_fun_sum _ fun l _ => (hhi i l).mul (hyl l)
  -- the weight branches on a measurable set, and each branch is measurable
  have hwt : Measurable fun s => aux_weight B (y s) (w s) i :=
    Measurable.ite (measurableSet_eq_fun (hHi i) (hLo i)) measurable_const
      (((hwi i).sub (hLo i)).div ((hHi i).sub (hLo i)))
  exact (hlo i l).add (hwt.mul ((hhi i l).sub (hlo i l)))


-- =======================================  MAIN THEOREM  ======================================= --

/-- On a measurable set where some member of `B` maps `y s` to `w s`, a member
measurable entry by entry does, and it lies in `B` everywhere. -/
theorem Interval.exists_measurable_mulVec_eq {B : Interval (Mat ℝ n n)} {M₀ : Mat ℝ n n}
    (hM₀ : M₀ ∈ B.construct) {y w : ℝ → Vec ℝ n} (hy : Measurable y) (hw : Measurable w)
    {S : Set ℝ} (hS : MeasurableSet S) (hex : ∀ s ∈ S, ∃ M ∈ B.construct, M *ᵥ y s = w s) :
    ∃ Â : ℝ → Mat ℝ n n, (∀ i j, Measurable fun s => Â s i j) ∧
      (∀ s, Â s ∈ B.construct) ∧ ∀ s ∈ S, Â s *ᵥ y s = w s := by -- --- PROOF ---
  classical
  -- the run's own member puts `w` between the corner values
  have hcorner : ∀ s ∈ S, ∀ i,
      ∑ l, aux_cornerLo B (y s) i l * y s l ≤ w s i ∧
        w s i ≤ ∑ l, aux_cornerHi B (y s) i l * y s l := fun s hs i => by
    obtain ⟨M, hM, hMy⟩ := hex s hs
    rw [← hMy]
    exact aux_corner_between hM (y s) i
  -- the selection on the set, the fixed member off it
  refine ⟨fun s => if s ∈ S then aux_select B (y s) (w s) else M₀,
    fun i j => ?_, fun s => ?_, fun s hs => ?_⟩
  · have he : (fun s => (if s ∈ S then aux_select B (y s) (w s) else M₀) i j)
        = fun s => if s ∈ S then aux_select B (y s) (w s) i j else M₀ i j := by
      funext s; split_ifs <;> rfl
    rw [he]
    exact Measurable.ite hS (aux_select_measurable B hy hw i j) measurable_const
  · dsimp only
    split_ifs with hs
    · exact aux_select_mem hM₀ (hcorner s hs)
    · exact hM₀
  · simp only [hs, if_true]
    exact aux_select_mulVec (hcorner s hs)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
