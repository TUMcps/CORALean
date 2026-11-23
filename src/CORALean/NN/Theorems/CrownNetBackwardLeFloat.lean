module

public import CORALean.NN.Operations.CrownBackwardFloat
public import CORALean.NN.Layers.Theorems.Real.CrownActivationStep
public import CORALean.NN.Layers.Theorems.Real.CrownAffineStep
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# CROWN's backward pass in floats is a lower bound

The float pass's row `μ`, constant `c`, slack `s` and gap `g` bound the exact network from below
at every input `x` where it is `Holds`: `μ · x + c - s - g · |x| ≤ Λ · N(x)`, with `g ≥ 0`. One
induction over the layers. Through a map: `crown_affine_step`, the row's rounding error at most
its gap, and the gap received charged at `|W x + b| ≤ |W| |x| + |b|`. Through an activation:
`crown_activation_step` on the lines, the row's rounding error at `|t| ≤ max(|l|, |u|)`, and the
gap received at `|σ t|`, which lies between the lines.

## Inputs
* `F` – the float network
* `R` – the exact network
* `Λ` – the row on the outputs
* `x` – the network's input, where the bound is read

## Hypotheses
* `hF` – `R` has `F`'s data, read as reals
* `hv` – every activation's input lies in its box, and the lines hold there

## Conclusion
* the gap is not negative, and the row at `x` plus the constant, less the slack and the gap at
  `|x|`, is at most the row on the outputs at `N(x)`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row rounded down within its gap moves the row at `x` by at most the gap at `|x|`. -/
private theorem aux_row_le {T μ e x : ℝ} (hlo : μ ≤ T) (he : T - μ ≤ e) :
    μ * x - e * |x| ≤ T * x := by
  have h1 : 0 ≤ (e - (T - μ)) * |x| := mul_nonneg (by linarith) (abs_nonneg x)
  have h2 : 0 ≤ (T - μ) * (x + |x|) := mul_nonneg (by linarith) (by linarith [neg_abs_le x])
  nlinarith

/-- `|z| ≤ |W| |x| + |b|` for `z = W x + b`, weighed by a gap `g ≥ 0`, the sums swapped. -/
private theorem aux_gap_affine {m n : ℕ} (g : Vec ℝ m) (W : Mat ℝ m n) (b : Vec ℝ m)
    (x : Vec ℝ n) (hg : ∀ i, 0 ≤ g i) : -- --- CONCL ---
    ∑ i, g i * |∑ j, W i j * x j + b i|
      ≤ ∑ j, (∑ i, g i * |W i j|) * |x j| + ∑ i, g i * |b i| := by -- --- PROOF ---
  have hrow : ∀ i, g i * |∑ j, W i j * x j + b i| ≤ ∑ j, g i * |W i j| * |x j| + g i * |b i| := by
    intro i
    have h1 : |∑ j, W i j * x j + b i| ≤ ∑ j, |W i j| * |x j| + |b i| := by
      have h0 : |∑ j, W i j * x j| ≤ ∑ j, |W i j| * |x j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [abs_mul]))
      linarith [abs_add_le (∑ j, W i j * x j) (b i)]
    have h2 := mul_le_mul_of_nonneg_left h1 (hg i)
    simpa [mul_add, Finset.mul_sum, mul_assoc] using h2
  refine (Finset.sum_le_sum fun i _ => hrow i).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.sum_mul]


-- =======================================  MAIN THEOREM  ======================================= --

theorem CrownNet.backward_le {F : CrownNet 𝕋 n k} {R : Real.CrownNet n k} (hF : F.Images R)
    (Λ : Vec 𝕋 k) (x : Vec ℝ n) (hv : R.Holds x) : -- --- CONCL ---
    (∀ j, 0 ≤ toReal ((F.backward Λ).gap j)) ∧
      ∑ j, toReal ((F.backward Λ).row j) * x j + toReal (F.backward Λ).const
        - toReal (F.backward Λ).slack - ∑ j, toReal ((F.backward Λ).gap j) * |x j|
        ≤ ∑ i, toReal (Λ i) * R.eval x i := by -- --- PROOF ---
  induction hF with
  | nil =>
    refine ⟨fun _ => by simp [CrownNet.backward, toReal_zero], ?_⟩
    simp [CrownNet.backward, Real.CrownNet.eval, toReal_zero]
  | @linear n m k W b rest R hrest ih =>
    -- the layers after the map, at its outputs `z`
    obtain ⟨hg', hih⟩ := ih Λ _ hv
    set ρ := rest.backward Λ with hρ
    set z : Vec ℝ m := fun i => ∑ j, toReal (W i j) * x j + toReal (b i) with hz
    -- the exact row `T = Wᵀ ν` between the row rounded down and up
    set T : Vec ℝ n := fun j => ∑ i, toReal (ρ.row i) * toReal (W i j) with hT
    set A : Vec ℝ n := fun j => ∑ i, toReal (ρ.gap i) * |toReal (W i j)| with hA
    have hstep := CORALean.Real.crown_affine_step (fun i => toReal (ρ.row i))
      (fun i j => toReal (W i j)) (fun i => toReal (b i)) x
    -- the row rounded down and up, and its gap
    set D : Vec 𝕋 n := fun j => dotDown ρ.row fun i => W i j with hD
    set U : Vec 𝕋 n := fun j => dotUp ρ.row fun i => W i j with hU
    set e : Vec 𝕋 n := fun j => subUp (U j) (D j) with he'
    set g : Vec 𝕋 n := fun j => addUp (dotUp ρ.gap fun i => absolute (W i j)) (e j) with hg''
    have hlo : ∀ j, toReal (D j) ≤ T j := fun j => dotDown_le _ _
    have hhi : ∀ j, T j ≤ toReal (U j) := fun j => le_dotUp _ _
    have he : ∀ j, T j - toReal (D j) ≤ toReal (e j) := fun j => by
      linarith [hhi j, sub_le_subUp (U j) (D j)]
    -- the new gap is at least `A + e`
    have hg : ∀ j, A j + toReal (e j) ≤ toReal (g j) := by
      intro j
      have h1 := le_dotUp ρ.gap fun i => absolute (W i j)
      simp only [toReal_absolute] at h1
      linarith [add_le_addUp (dotUp ρ.gap fun i => absolute (W i j)) (e j)]
    have hA0 : ∀ j, 0 ≤ A j := fun j =>
      Finset.sum_nonneg fun i _ => mul_nonneg (hg' i) (abs_nonneg _)
    refine ⟨fun j => ?_, ?_⟩
    · show 0 ≤ toReal (g j)
      linarith [hg j, hA0 j, hlo j, he j]
    -- the row: rounded down within its gap, then the gap received through `|W|`
    have hrow : ∑ j, toReal (D j) * x j - ∑ j, toReal (g j) * |x j|
        ≤ ∑ j, T j * x j - ∑ j, A j * |x j| := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have h1 := aux_row_le (x := x j) (hlo j) (he j)
      have h2 := mul_le_mul_of_nonneg_right (hg j) (abs_nonneg (x j))
      nlinarith
    -- the constant, rounded down, and the slack, rounded up
    have hc : toReal (addDown ρ.const (dotDown ρ.row b))
        ≤ toReal ρ.const + ∑ i, toReal (ρ.row i) * toReal (b i) := by
      linarith [addDown_le_add ρ.const (dotDown ρ.row b), dotDown_le ρ.row b]
    have hs : toReal ρ.slack + ∑ i, toReal (ρ.gap i) * |toReal (b i)|
        ≤ toReal (addUp ρ.slack (dotUp ρ.gap fun i => absolute (b i))) := by
      have h1 := le_dotUp ρ.gap fun i => absolute (b i)
      simp only [toReal_absolute] at h1
      linarith [add_le_addUp ρ.slack (dotUp ρ.gap fun i => absolute (b i))]
    have hzg := aux_gap_affine (fun i => toReal (ρ.gap i)) (fun i j => toReal (W i j))
      (fun i => toReal (b i)) x hg'
    show ∑ j, toReal (D j) * x j + toReal (addDown ρ.const (dotDown ρ.row b))
        - toReal (addUp ρ.slack (dotUp ρ.gap fun i => absolute (b i)))
        - ∑ j, toReal (g j) * |x j| ≤ ∑ i, toReal (Λ i) * R.eval z i
    linarith
  | @act n k l u sl bl su bu rest R σ hrest ih =>
    set z := x with hzx
    obtain ⟨hbox, hlines, hv'⟩ := hv
    -- the layers after the activation, at its outputs `h`
    obtain ⟨hg', hih⟩ := ih Λ _ hv'
    set ρ := rest.backward Λ with hρ
    set h : Vec ℝ n := fun i => σ (z i) with hh
    set p : Vec 𝕋 n := fun i => maximum (ρ.row i) zero with hp
    set q : Vec 𝕋 n := fun i => minimum (ρ.row i) zero with hq
    have hpR : ∀ i, toReal (p i) = max (toReal (ρ.row i)) 0 := fun i => by
      simp [hp, toReal_maximum, toReal_zero]
    have hqR : ∀ i, toReal (q i) = min (toReal (ρ.row i)) 0 := fun i => by
      simp [hq, toReal_minimum, toReal_zero]
    have hlo : ∀ i, toReal (sl i) * z i + toReal (bl i) ≤ h i := fun i =>
      (hlines i (z i) (hbox i).1 (hbox i).2).1
    have hhi : ∀ i, h i ≤ toReal (su i) * z i + toReal (bu i) := fun i =>
      (hlines i (z i) (hbox i).1 (hbox i).2).2
    have hstep := CORALean.Real.crown_activation_step (fun i => toReal (ρ.row i))
      (fun i => toReal (sl i)) (fun i => toReal (bl i)) (fun i => toReal (su i))
      (fun i => toReal (bu i)) z h hlo hhi
    simp only [← hpR, ← hqR] at hstep
    -- the exact row `T = ν⁺ s_l + ν⁻ s_u` between the row rounded down and up
    set T : Vec ℝ n := fun i => toReal (p i) * toReal (sl i) + toReal (q i) * toReal (su i)
      with hT
    set μ : Vec 𝕋 n := fun i => addDown (mulDown (p i) (sl i)) (mulDown (q i) (su i)) with hμ
    set e : Vec 𝕋 n := fun i => subUp (addUp (mulUp (p i) (sl i)) (mulUp (q i) (su i))) (μ i)
      with he
    have hTlo : ∀ i, toReal (μ i) ≤ T i := fun i => by
      linarith [addDown_le_add (mulDown (p i) (sl i)) (mulDown (q i) (su i)),
        mulDown_le_mul (p i) (sl i), mulDown_le_mul (q i) (su i)]
    have hTe : ∀ i, T i - toReal (μ i) ≤ toReal (e i) := fun i => by
      linarith [add_le_addUp (mulUp (p i) (sl i)) (mulUp (q i) (su i)),
        mul_le_mulUp (p i) (sl i), mul_le_mulUp (q i) (su i),
        sub_le_subUp (addUp (mulUp (p i) (sl i)) (mulUp (q i) (su i))) (μ i)]
    -- `|t| ≤ m` on the box, `|σ t| ≤ hb` between the lines
    set m : Vec 𝕋 n := fun i => maximum (absolute (l i)) (absolute (u i)) with hm
    have hzm : ∀ i, |z i| ≤ toReal (m i) := fun i => by
      simp only [hm, toReal_maximum, toReal_absolute]
      exact abs_le_max_abs_abs (hbox i).1 (hbox i).2
    set hb : Vec 𝕋 n := fun i => maximum (addUp (mulUp (absolute (sl i)) (m i))
      (absolute (bl i))) (addUp (mulUp (absolute (su i)) (m i)) (absolute (bu i))) with hhb
    have hline : ∀ (s c : 𝕋) (i : Fin n), |toReal s * z i + toReal c|
        ≤ toReal (addUp (mulUp (absolute s) (m i)) (absolute c)) := by
      intro s c i
      have h1 : |toReal s * z i| ≤ |toReal s| * toReal (m i) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hzm i) (abs_nonneg _)
      have h2 := mul_le_mulUp (absolute s) (m i)
      have h3 := add_le_addUp (mulUp (absolute s) (m i)) (absolute c)
      rw [toReal_absolute] at h2 h3
      linarith [abs_add_le (toReal s * z i) (toReal c)]
    have hhb' : ∀ i, |h i| ≤ toReal (hb i) := fun i => by
      simp only [hhb, toReal_maximum]
      exact (abs_le_max_abs_abs (hlo i) (hhi i)).trans
        (max_le_max (hline (sl i) (bl i) i) (hline (su i) (bu i) i))
    refine ⟨fun _ => by simp [CrownNet.backward, toReal_zero], ?_⟩
    -- the row, rounded down within its gap, at `|t| ≤ m`
    have hrow : ∑ i, toReal (μ i) * z i - ∑ i, toReal (e i) * toReal (m i) ≤ ∑ i, T i * z i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 := aux_row_le (x := z i) (hTlo i) (hTe i)
      have he0 : 0 ≤ toReal (e i) := by linarith [hTlo i, hTe i]
      have h2 := mul_le_mul_of_nonneg_left (hzm i) he0
      linarith
    -- the gap received, at `|σ t| ≤ hb`
    have hgh : ∑ i, toReal (ρ.gap i) * |h i| ≤ ∑ i, toReal (ρ.gap i) * toReal (hb i) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hhb' i) (hg' i)
    -- the constant, rounded down, and the slack, rounded up
    have hc : toReal (addDown (addDown ρ.const (dotDown p bl)) (dotDown q bu))
        ≤ toReal ρ.const + ∑ i, toReal (p i) * toReal (bl i)
          + ∑ i, toReal (q i) * toReal (bu i) := by
      linarith [addDown_le_add (addDown ρ.const (dotDown p bl)) (dotDown q bu),
        addDown_le_add ρ.const (dotDown p bl), dotDown_le p bl, dotDown_le q bu]
    have hs : toReal ρ.slack + ∑ i, toReal (ρ.gap i) * toReal (hb i)
        + ∑ i, toReal (e i) * toReal (m i)
        ≤ toReal (addUp (addUp ρ.slack (dotUp ρ.gap hb)) (dotUp e m)) := by
      linarith [add_le_addUp (addUp ρ.slack (dotUp ρ.gap hb)) (dotUp e m),
        add_le_addUp ρ.slack (dotUp ρ.gap hb), le_dotUp ρ.gap hb, le_dotUp e m]
    have hsplit : ∑ i, (toReal (p i) * toReal (bl i) + toReal (q i) * toReal (bu i))
        = ∑ i, toReal (p i) * toReal (bl i) + ∑ i, toReal (q i) * toReal (bu i) :=
      Finset.sum_add_distrib
    show ∑ i, toReal (μ i) * z i
        + toReal (addDown (addDown ρ.const (dotDown p bl)) (dotDown q bu))
        - toReal (addUp (addUp ρ.slack (dotUp ρ.gap hb)) (dotUp e m))
        - ∑ i, toReal (zero : 𝕋) * |z i| ≤ ∑ i, toReal (Λ i) * R.eval h i
    simp only [toReal_zero, zero_mul, Finset.sum_const_zero, sub_zero]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
