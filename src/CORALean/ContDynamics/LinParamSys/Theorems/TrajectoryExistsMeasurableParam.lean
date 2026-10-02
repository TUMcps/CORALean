import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.Order.ProjIcc

/-!
# A time-varying run is driven by a measurable member of the box

`Trajectory` asks nothing of `t ↦ A t` beyond `A t ∈ sys.A`, and only `A t x(t)`
enters the flow, so a run's parameter can be as wild as a choice per instant.
For an input-free run over `[0, t)` it can be replaced by a measurable one
driving the same flow: at every instant, a member of the box that maps `x(s)`
to the same velocity, chosen by a formula rather than by choice.

Row by row: the least and the greatest value a row of the box can take against
`x(s)` are attained at the corner rows, each entry at the endpoint the sign of
`x(s)`'s coordinate picks; the velocity lies between them, so it is one convex
combination of the two corner rows, and the weight is a quotient of measurable
functions. The velocity itself is measurable as a one-sided derivative, which
every function has measurably (`stronglyMeasurable_derivWithin_Ici`).

With an input it would be the velocity minus `u(s)`, which `Trajectory` does not
make measurable; this is the input-free case only.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet MeasureTheory

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


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

/-- An input-free run over `[0, t)` is driven by a measurable member of the box:
the same velocity at every instant, from a parameter measurable entry by entry. -/
theorem LinParamSys.Trajectory.exists_measurable_param {sys : LinParamSys ℐ n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n} (traj : sys.Trajectory T R₀ U x u A)
    {t : ℝ} (ht : 0 ≤ t) (hT : Set.Icc 0 t ⊆ T) (hu : ∀ s ∈ Set.Ico 0 t, u s = 0) :
    ∃ Â : ℝ → Mat ℝ n n, (∀ i j, Measurable fun s => Â s i j) ∧
      (∀ s, Â s ∈ construct sys.A) ∧
      ∀ s ∈ Set.Ico 0 t, Â s *ᵥ x s = A s *ᵥ x s := by -- --- PROOF ---
  have h0 : (0:ℝ) ∈ T := hT ⟨le_rfl, ht⟩
  -- the state, extended constantly past the window so that it is continuous everywhere
  have hxc : ContinuousOn x (Set.Icc 0 t) := fun s hs =>
    ((traj.flow s (hT hs)).continuousWithinAt).mono hT
  set y : ℝ → Vec ℝ n := Set.IccExtend ht (Set.restrict (Set.Icc 0 t) x) with hy
  have hyc : Continuous y := (continuousOn_iff_continuous_restrict.mp hxc).Icc_extend'
  have hyx : ∀ s ∈ Set.Icc 0 t, y s = x s := fun s hs => by
    rw [hy, Set.IccExtend_of_mem ht _ hs]; rfl
  -- the velocity, as a one-sided derivative, which is measurable for every function
  set w : ℝ → Vec ℝ n := fun s => derivWithin x (Set.Ici s) s with hw
  have hwm : Measurable w := (stronglyMeasurable_derivWithin_Ici x).measurable
  have hwA : ∀ s ∈ Set.Ico 0 t, w s = A s *ᵥ x s := fun s hs => by
    have hd := (traj.flow s (hT ⟨hs.1, hs.2.le⟩)).mono_of_mem_nhdsWithin
      (mem_nhdsGE_iff_exists_Ico_subset.mpr
        ⟨t, hs.2, fun _ hr => hT ⟨le_trans hs.1 hr.1, hr.2.le⟩⟩)
    rw [hu s hs, add_zero] at hd
    exact hd.derivWithin (uniqueDiffWithinAt_Ici s)
  -- the run's own member puts the velocity between the corner values
  have hcorner : ∀ s ∈ Set.Ico 0 t, ∀ i,
      ∑ l, aux_cornerLo sys.A (y s) i l * y s l ≤ w s i ∧
        w s i ≤ ∑ l, aux_cornerHi sys.A (y s) i l * y s l := fun s hs i => by
    rw [hwA s hs, hyx s ⟨hs.1, hs.2.le⟩]
    exact aux_corner_between (traj.param s (hT ⟨hs.1, hs.2.le⟩)) (x s) i
  -- the selection on the window, a fixed member outside it
  refine ⟨fun s => if s ∈ Set.Ico 0 t then aux_select sys.A (y s) (w s) else A 0,
    fun i j => ?_, fun s => ?_, fun s hs => ?_⟩
  · have he : (fun s => (if s ∈ Set.Ico 0 t then aux_select sys.A (y s) (w s) else A 0) i j)
        = fun s => if s ∈ Set.Ico 0 t then aux_select sys.A (y s) (w s) i j else A 0 i j := by
      funext s; split_ifs <;> rfl
    rw [he]
    exact Measurable.ite measurableSet_Ico (aux_select_measurable sys.A hyc.measurable hwm i j)
      measurable_const
  · dsimp only
    split_ifs with hs
    · exact aux_select_mem (traj.param 0 h0) (hcorner s hs)
    · exact traj.param 0 h0
  · simp only [hs, if_true]
    rw [← hwA s hs, ← hyx s ⟨hs.1, hs.2.le⟩]
    exact aux_select_mulVec (hcorner s hs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
