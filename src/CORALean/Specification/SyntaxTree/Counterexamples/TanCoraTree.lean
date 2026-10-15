module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Counterexamples.TanCora
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.Atan
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.ContSet.Interval.Real.Operations.Tan
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Backpropagation
public import CORALean.Specification.SyntaxTree.Theorems.BackpropagationBinaryOk
public import CORALean.Specification.SyntaxTree.Theorems.BackpropagationUnaryOk
public import CORALean.Specification.SyntaxTree.Theorems.BackpropagationVarOk

@[expose] public section

/-!
# The tree `tan(x₁) - x₂`, with `tan` as printed

The leaves over `[0,π/3] × [0,2]`, combined as `tan(x₁) - x₂`: the tree of `tanCora_counterexample`.

# CORA's `tan` node loses a solution

`aux_tan_` of `syntaxTree.m` begins with `int = int & interval(-1,1)`, copied from `aux_sin_`; `tan`
takes every real value. For `tan(x₁) - x₂ = 0` over `[0,π/3] × [0,2]`, with the root target
`[0,0]`, the
target of the `tan` node is `[0,√3]`, cut to `[0,1]`, and `x₁` is narrowed to `[0, π/4]`: the zero
`(π/3, √3)` is lost. See `SyntaxTree.funHanTanCora` and `SyntaxTree.funHanTan`, which is sound
(`tan_sound`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- The model: CORA's code as printed, kept only to be refuted.
/-- The tree of `tan(x₁) - x₂` over `[0,π/3] × [0,2]`, with the printed `aux_tan_`. -/
noncomputable def SyntaxTree.tanCoraTree : SyntaxTree 2 :=
  .minus (.tanCora (.var 0 (interval 0 (Real.pi / 3)))) (.var 1 (interval 0 2))

end CORALean

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The upper bound the printed `aux_tan_` returns for the target `[0,√3]` over `[0,π/3]` is at
most `π/4`. -/
private theorem SyntaxTree.funHanTanCora_sup_le :
    ∃ val, funHanTanCora (interval 0 (Real.sqrt 3)) (interval 0 (Real.pi / 3)) = .ok val ∧
      val.sup 0 ≤ Real.pi / 4 := by -- --- PROOF ---
  refine ⟨_, rfl, ?_⟩
  have hp := Real.pi_pos
  have h3 : 1 ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have e₁ : Real.Interval.atan (Real.Interval.intersection (interval 0 (Real.sqrt 3))
      (interval (-1) 1)) = interval 0 (Real.pi / 4) := by
    simp only [Real.Interval.atan, Real.Interval.intersection, interval]
    congr 1 <;> funext i <;> simp [h3, Real.arctan_one]
  simp only [e₁]
  have i₁ : ⌈(Real.pi / 3 - Real.pi / 4) / (2 * Real.pi)⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    constructor <;> (field_simp; norm_num)
  have i₂ : ⌈(Real.pi / 3 - (Real.pi / 4 + Real.pi)) / (2 * Real.pi)⌉ = 0 := by
    rw [Int.ceil_eq_iff]
    constructor <;> (field_simp; norm_num; try nlinarith)
  unfold periodic
  simp only [interval, Real.Interval.intersection, zero_add, i₁, i₂, Int.cast_one, Int.cast_zero]
  refine (min_le_right _ _).trans ?_
  split_ifs with h h'
  · -- neither shifted branch contains `π/3`
    exfalso
    rcases h with ⟨a, _⟩ | ⟨a, _⟩ <;> linarith
  · linarith
  · exfalso
    apply h'
    linarith

/-- `backpropagation` of the printed `tan` loses the zero `(π/3, √3)`. -/
theorem SyntaxTree.tanCora_counterexample :
    ∃ (x : Fin 2 → ℝ) (B : Real.Interval (Vec ℝ 2)),
      InBox B x ∧ Dom.contains (interval 0 0) (tanCoraTree.eval x) ∧
      ¬ ∃ r, backpropagation tanCoraTree (interval 0 0) B = .ok r ∧ InBox r x := by -- --- PROOF ---
  have hp := Real.pi_pos
  have h3 : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  refine ⟨![Real.pi / 3, Real.sqrt 3], ⟨fun _ => 0, ![Real.pi / 3, 2]⟩, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp
      positivity
    · simp
      exact h3
  · simp [tanCoraTree, SyntaxTree.minus, SyntaxTree.tanCora, eval, Binary.fn, Unary.fn,
      interval, Dom.contains, Real.tan_pi_div_three]
  · rintro ⟨r, hr, hxr⟩
    -- the root asks its first operand, `tan(x₁)`, for the target `(funHanMinus ...).left`
    obtain ⟨r₁, h₁, hx₁⟩ := backpropagation_binary_ok hr
    obtain ⟨val, hval, h₂⟩ := backpropagation_unary_ok h₁
    have hfirst : (funHanMinus (interval 0 0)
        (value (SyntaxTree.tanCora (SyntaxTree.var (0 : Fin 2) (interval 0 (Real.pi / 3)))))
        (value (SyntaxTree.var (1 : Fin 2) (interval 0 2)))).left =
        interval 0 (Real.sqrt 3) := by
      simp only [funHanMinus, SyntaxTree.tanCora, value, Real.Interval.intersection,
        Real.Interval.tan, Real.Interval.plus, interval]
      congr 1 <;> funext i <;> simp [Real.tan_pi_div_three, h3]
    rw [hfirst] at hval
    obtain ⟨val', hval', hle⟩ := funHanTanCora_sup_le
    rw [show value (SyntaxTree.var (0 : Fin 2) (interval 0 (Real.pi / 3))) =
      interval 0 (Real.pi / 3) from rfl, hval'] at hval
    cases hval
    -- the coordinate `x₁` is cut to `π/4 < π/3`
    have hsup := backpropagation_var_ok h₂
    have hx0 := (hx₁ _ hxr 0).2
    rw [hsup] at hx0
    have : Real.pi / 3 ≤ Real.pi / 4 := by
      simpa using hx0.trans ((min_le_left _ _).trans hle)
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
