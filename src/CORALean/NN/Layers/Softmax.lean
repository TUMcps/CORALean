import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.NN.Layer

/-!
# The softmax layer

CORA's `nnSoftmaxLayer`: `x i ↦ exp(x i) / ∑ⱼ exp(x j)`.

The first layer whose output coordinate depends on *every* input coordinate, and
through a normalization. `Relaxation` cannot express that: it relaxes a scalar
`σ : ℝ → ℝ` over one neuron's interval, where the denominator is shared by all
`n` outputs. So this layer is written directly, with no slope.

The outputs sum to one, and no representation this layer can name is closed under
intersecting a hyperplane, so the constraint cannot be kept. Its shadow on each
coordinate can, and is exact for a box: from `∑ⱼ y j = 1` and raw bounds
`rl ≤ y ≤ ru`, `y i ∈ [1 - ∑_{j≠i} ru j, 1 - ∑_{j≠i} rl j]`, and intersecting
that with `[rl i, ru i]` is `softmaxBox`, tight where the raw bounds are.

The raw bounds come from `softmax_eq_inv`, which divides through by `exp (x i)`
and leaves `1 + ∑_{j≠i} exp(x j - x i)`, every term of which the box bounds
directly — tighter than bounding numerator and denominator apart.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [IntervalOuter S] [OfInterval S]
  {n : ℕ}

noncomputable def softmax (x : Vec ℝ n) : Vec ℝ n :=
  fun i => Real.exp (x i) / ∑ j, Real.exp (x j)

/-- A coordinate is what makes the denominator positive, so every statement here
takes one rather than a `NeZero`: at `n = 0` there is nothing to say and the
layer's obligation is vacuous. -/
theorem exp_sum_pos (x : Vec ℝ n) (i : Fin n) : 0 < ∑ j, Real.exp (x j) :=
  Finset.sum_pos (fun j _ => Real.exp_pos (x j)) ⟨i, Finset.mem_univ i⟩

theorem softmax_nonneg (x : Vec ℝ n) (i : Fin n) : 0 ≤ softmax x i :=
  div_nonneg (Real.exp_pos (x i)).le (exp_sum_pos x i).le

/-- The constraint the enclosure below is built to keep, and a fact about `eval`
that a specification may use directly. -/
theorem softmax_sum_eq_one (x : Vec ℝ n) (i : Fin n) : ∑ j, softmax x j = 1 := by
  show ∑ j, Real.exp (x j) / (∑ k, Real.exp (x k)) = 1
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (exp_sum_pos x i))

/-- Dividing through by `exp (x i)`: the `j = i` term becomes exactly `1`, which
is what makes this tighter than bounding numerator and denominator apart. -/
theorem softmax_eq_inv (x : Vec ℝ n) (i : Fin n) :
    softmax x i = (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (x j - x i))⁻¹ := by
  have hE0 : Real.exp (x i) ≠ 0 := ne_of_gt (Real.exp_pos (x i))
  have hsplit : ∑ j, Real.exp (x j)
      = Real.exp (x i) + ∑ j ∈ Finset.univ.erase i, Real.exp (x j) :=
    (Finset.add_sum_erase Finset.univ (fun j => Real.exp (x j)) (Finset.mem_univ i)).symm
  have hratio : ∑ j ∈ Finset.univ.erase i, Real.exp (x j - x i)
      = (∑ j ∈ Finset.univ.erase i, Real.exp (x j)) / Real.exp (x i) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => Real.exp_sub (x j) (x i)
  have hone : 1 + (∑ j ∈ Finset.univ.erase i, Real.exp (x j)) / Real.exp (x i)
      = (Real.exp (x i) + ∑ j ∈ Finset.univ.erase i, Real.exp (x j)) / Real.exp (x i) := by
    field_simp
  show Real.exp (x i) / (∑ j, Real.exp (x j)) = _
  rw [hsplit, hratio, hone, inv_div]

/-! ## The raw bounds

Each ratio `x j - x i` lies in `[lo j - hi i, hi j - lo i]`, and the denominator
is monotone in every one of them. -/


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_one_add_exp_sum_pos (v : Vec ℝ n) (i : Fin n) (a : ℝ) :
    0 < 1 + ∑ j ∈ Finset.univ.erase i, Real.exp (v j - a) := by
  have h : (0:ℝ) ≤ ∑ j ∈ Finset.univ.erase i, Real.exp (v j - a) :=
    Finset.sum_nonneg fun j _ => (Real.exp_pos (v j - a)).le
  linarith

/-- The denominator is smallest when every ratio is, which is the box's corner. -/
theorem softmax_le_raw {lo hi x : Vec ℝ n} (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i) (i : Fin n) :
    softmax x i ≤ (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (lo j - hi i))⁻¹ := by
  have hmono : ∑ j ∈ Finset.univ.erase i, Real.exp (lo j - hi i)
      ≤ ∑ j ∈ Finset.univ.erase i, Real.exp (x j - x i) :=
    Finset.sum_le_sum fun j _ =>
      Real.exp_le_exp.mpr (by linarith [(hx j).1, (hx i).2])
  rw [softmax_eq_inv x i, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le (aux_one_add_exp_sum_pos lo i (hi i)) (by linarith)

/-- And largest at the opposite corner, which is the lower bound on `softmax`. -/
theorem raw_le_softmax {lo hi x : Vec ℝ n} (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i) (i : Fin n) :
    (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (hi j - lo i))⁻¹ ≤ softmax x i := by
  have hmono : ∑ j ∈ Finset.univ.erase i, Real.exp (x j - x i)
      ≤ ∑ j ∈ Finset.univ.erase i, Real.exp (hi j - lo i) :=
    Finset.sum_le_sum fun j _ =>
      Real.exp_le_exp.mpr (by linarith [(hx j).2, (hx i).1])
  rw [softmax_eq_inv x i, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le
    (aux_one_add_exp_sum_pos x i (x i)) (by linarith)

/-! ## What the normalization buys -/

/-- The outputs sum to one, so each is what the others leave over. Stated for
arbitrary raw bounds because the float layer passes `0` below, where the
normalization is not a tightening but the only lower bound available. -/
theorem softmax_mem_tightened (x rl ru : Vec ℝ n)
    (hl : ∀ i, rl i ≤ softmax x i) (hu : ∀ i, softmax x i ≤ ru i) (i : Fin n) :
    max (rl i) (1 - ∑ j ∈ Finset.univ.erase i, ru j) ≤ softmax x i ∧
      softmax x i ≤ min (ru i) (1 - ∑ j ∈ Finset.univ.erase i, rl j) := by
  have hsplit : softmax x i + ∑ j ∈ Finset.univ.erase i, softmax x j = 1 := by
    rw [Finset.add_sum_erase Finset.univ (softmax x) (Finset.mem_univ i)]
    exact softmax_sum_eq_one x i
  have hru : ∑ j ∈ Finset.univ.erase i, softmax x j ≤ ∑ j ∈ Finset.univ.erase i, ru j :=
    Finset.sum_le_sum fun j _ => hu j
  have hrl : ∑ j ∈ Finset.univ.erase i, rl j ≤ ∑ j ∈ Finset.univ.erase i, softmax x j :=
    Finset.sum_le_sum fun j _ => hl j
  exact ⟨max_le (hl i) (by linarith), le_min (hu i) (by linarith)⟩

/-! ## The layer -/

noncomputable def softmaxRawLower (I : Interval (Vec ℝ n)) (i : Fin n) : ℝ :=
  (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (I.sup j - I.inf i))⁻¹

noncomputable def softmaxRawUpper (I : Interval (Vec ℝ n)) (i : Fin n) : ℝ :=
  (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (I.inf j - I.sup i))⁻¹

/-- The raw bounds cut down by what the other coordinates leave over. -/
noncomputable def softmaxBox (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i =>
    max (softmaxRawLower I i) (1 - ∑ j ∈ Finset.univ.erase i, softmaxRawUpper I j)
  sup := fun i =>
    min (softmaxRawUpper I i) (1 - ∑ j ∈ Finset.univ.erase i, softmaxRawLower I j)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A box and nothing else: the slope is zero, so no `mtimes` and no `plus`
appear, and this is the only layer here asking for neither. -/
noncomputable def Layer.softmax : Layer S n n where
  eval := _root_.CORALean.Real.softmax
  propagate s := ofInterval (softmaxBox (interval s))
  propagate_outer s x hx := by
    have hbox : ∀ i, (interval s).inf i ≤ x i ∧ x i ≤ (interval s).sup i :=
      interval_outer s hx
    refine ofInterval_outer _ fun i => ?_
    exact softmax_mem_tightened x (softmaxRawLower (interval s))
      (softmaxRawUpper (interval s)) (fun i => raw_le_softmax hbox i)
      (fun i => softmax_le_raw hbox i) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
