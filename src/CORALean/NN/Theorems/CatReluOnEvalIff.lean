module

public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.NN.Operations.CatReluOn
public import Mathlib.Data.List.FinRange

@[expose] public section

/-!
# The CAT form of ReLU is ReLU

[1, Sec. II (ReLU to CAT)]: `ReLUₙ ∘ … ∘ ReLU₁` maps `x` to `max(x, 0)` coordinatewise, and to
nothing else. Each `ReLUᵢ` replaces coordinate `i` by `max(xᵢ, 0)`: the first case when
`xᵢ ≥ 0`, the zeroed row when `xᵢ < 0`, the two guards excluding each other. Over a list, the
coordinates it names are replaced and the rest kept, a repeated coordinate costing nothing,
`max(max(t, 0), 0) = max(t, 0)`.

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A `0`/`1` matrix read into ℝ, times `x`: the coordinates its diagonal keeps. -/
theorem aux_mulVec_diag (p : Fin n → Prop) [DecidablePred p] (x : Vec ℝ n) :
    toRealMat (fun r c => if r = c ∧ p r then (one : 𝕋) else zero) *ᵥ x
      = fun j => if p j then x j else 0 := by -- --- PROOF ---
  funext j
  show ∑ c, toReal (if j = c ∧ p j then (one : 𝕋) else zero) * x c = _
  rw [Finset.sum_eq_single j (fun c _ hc => by
      rw [if_neg (fun h => hc h.1.symm), toReal_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ j) h)]
  by_cases hp : p j <;> simp [hp, toReal_one, toReal_zero]

/-- One `ReLUᵢ` replaces coordinate `i` by `max(xᵢ, 0)`. -/
theorem aux_eval_step_iff (i : Fin n) (x y : Vec ℝ n) : -- --- STMT ---
    Cat.Eval (𝕋 := 𝕋) (.cases 2 ![.nonneg i, .neg i]
      ![.affine (fun r c => if r = c then one else zero) (fun _ => zero),
        .affine (fun r c => if r = c ∧ r ≠ i then one else zero) (fun _ => zero)]) x y
      ↔ y = Function.update x i (Real.relu (x i)) := by -- --- PROOF ---
  have hb : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := funext fun _ => toReal_zero
  have hid : toRealMat (fun r c : Fin n => if r = c then (one : 𝕋) else zero) *ᵥ x = x := by
    have := aux_mulVec_diag (𝕋 := 𝕋) (fun _ : Fin n => True) x
    simp only [and_true, if_true] at this
    exact this
  have hzero := aux_mulVec_diag (𝕋 := 𝕋) (fun r : Fin n => r ≠ i) x
  constructor
  · rintro (_ | ⟨E, f, k, hk, hfirst, hy⟩)
    revert hk hfirst hy
    refine Fin.cases ?_ (fun k' => ?_) k
    · -- `xᵢ ≥ 0`: the identity, and ReLU keeps the coordinate
      intro hk _ hy
      cases hy
      rw [hb, add_zero, hid]
      have h0 : (0:ℝ) ≤ x i := hk
      funext j
      by_cases hj : j = i
      · subst hj; simp [Real.relu, max_eq_left h0]
      · simp [hj]
    · -- `xᵢ < 0`: row `i` zeroed, and ReLU sends the coordinate to `0`
      refine Fin.cases ?_ (fun k'' => k''.elim0) k'
      intro hk _ hy
      cases hy
      rw [hb, add_zero, hzero]
      have h0 : x i < 0 := hk
      funext j
      by_cases hj : j = i
      · subst hj; simp [Real.relu, max_eq_right h0.le]
      · simp [hj]
  · rintro rfl
    rcases le_or_gt 0 (x i) with h0 | h0
    · -- `xᵢ ≥ 0`: the first case applies, and it is the identity
      refine Cat.Eval.cases _ _ 0 (by exact h0) (fun j hj => absurd hj (Fin.not_lt_zero j)) ?_
      have hy : Function.update x i (Real.relu (x i)) = toRealMat (fun r c : Fin n =>
          if r = c then (one : 𝕋) else zero) *ᵥ x + toRealVec (fun _ : Fin n => (zero : 𝕋)) := by
        rw [hb, add_zero, hid]
        funext j
        by_cases hj : j = i
        · subst hj; simp [Real.relu, max_eq_left h0]
        · simp [hj]
      rw [hy]
      exact Cat.Eval.affine _ _ x
    · -- `xᵢ < 0`: the first guard fails, and the second case zeroes the row
      refine Cat.Eval.cases _ _ 1 (by exact h0) (fun j hj => ?_) ?_
      · have hj0 : j = 0 := Fin.ext (by have := hj; simp [Fin.lt_def] at this; omega)
        subst hj0
        exact fun h => absurd (show (0:ℝ) ≤ x i from h) (not_le.mpr h0)
      · have hy : Function.update x i (Real.relu (x i)) = toRealMat (fun r c : Fin n =>
            if r = c ∧ r ≠ i then (one : 𝕋) else zero) *ᵥ x
            + toRealVec (fun _ : Fin n => (zero : 𝕋)) := by
          rw [hb, add_zero, hzero]
          funext j
          by_cases hj : j = i
          · subst hj; simp [Real.relu, max_eq_right h0.le]
          · simp [hj]
        rw [hy]
        exact Cat.Eval.affine _ _ x

/-- Over a list, the coordinates it names. -/
theorem aux_reluOn_eval_iff (l : List (Fin n)) (x y : Vec ℝ n) :
    (Cat.reluOn (𝕋 := 𝕋) l).Eval x y
      ↔ y = fun j => if j ∈ l then Real.relu (x j) else x j := by -- --- PROOF ---
  induction l generalizing x y with
  | nil =>
    have hb : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := funext fun _ => toReal_zero
    have hid := aux_mulVec_diag (𝕋 := 𝕋) (fun _ : Fin n => True) x
    simp only [and_true, if_true] at hid
    constructor
    · rintro (_ | _)
      rw [hb, add_zero, hid]
      simp
    · rintro rfl
      have hy : (fun j => if j ∈ ([] : List (Fin n)) then Real.relu (x j) else x j)
          = toRealMat (fun r c : Fin n => if r = c then (one : 𝕋) else zero) *ᵥ x
            + toRealVec (fun _ : Fin n => (zero : 𝕋)) := by
        rw [hb, add_zero, hid]
        simp
      rw [hy]
      exact Cat.Eval.affine _ _ x
  | cons i is ih =>
    -- the step on coordinate `i`, then the rest of the list on its result
    have key : (fun j => if j ∈ is then Real.relu (Function.update x i (Real.relu (x i)) j)
          else Function.update x i (Real.relu (x i)) j)
        = fun j => if j ∈ i :: is then Real.relu (x j) else x j := by
      funext j
      by_cases hj : j = i
      · subst hj
        by_cases hm : j ∈ is <;> simp [hm, Real.relu]
      · by_cases hm : j ∈ is <;> simp [hm, hj]
    constructor
    · rintro (_ | _ | ⟨_, _, z, h₁, h₂⟩)
      rw [(aux_eval_step_iff i x z).mp h₁] at h₂
      rw [(ih _ y).mp h₂, key]
    · rintro rfl
      refine Cat.Eval.comp _ _ (Function.update x i (Real.relu (x i)))
        ((aux_eval_step_iff i x _).mpr rfl) ?_
      rw [← key]
      exact (ih _ _).mpr rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem Cat.reluOn_finRange_eval_iff (x y : Vec ℝ n) :
    (Cat.reluOn (𝕋 := 𝕋) (List.finRange n)).Eval x y ↔ y = fun j => Real.relu (x j) := by
  rw [aux_reluOn_eval_iff]
  simp [List.mem_finRange]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
