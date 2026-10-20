module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Counterexamples.SinhCora
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.ContSet.Interval.Real.Operations.Sinh
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Backpropagation
public import CORALean.Specification.SyntaxTree.Theorems.BackpropagationBinaryOk
public import CORALean.Specification.SyntaxTree.Theorems.BackpropagationUnaryOk
public import CORALean.Specification.SyntaxTree.Theorems.BackpropagationVarOk
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The tree `sinh(x₁) - x₂`, with `sinh` as printed

`syntaxTree(dom(1))` and `syntaxTree(dom(2))` over `[0,3] × [0,3/2]`, combined as `sinh(x₁) - x₂`:
the
function `contractForwardBackward` is given in `sinhCora_counterexample`.

# CORA's `sinh` node loses a solution

`aux_sinh_` of `syntaxTree.m` begins with `int = int & interval(-1,1)`, copied from the circular
functions; `sinh` takes every real value. For `sinh(x₁) - x₂ = 0` over `[0,3] × [0,3/2]`, with the
root
target `[0,0]`, the target of the `sinh` node is `[0,3/2]`, cut to `[0,1]`, and `x₁` is narrowed to
`[0, asinh 1]`: the zero `(1, sinh 1)` is lost. See `SyntaxTree.funHanSinhCora` and
`SyntaxTree.funHanSinh`, which is sound (`funHanSinh_sound`).

## Inputs
* `int` – target interval
* `prev` – previous interval

## Hypotheses
* `h` – the target starts at most at one

## Conclusion
* the printed upper bound is at most the inverse sinh of one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- The model: CORA's code as printed, kept only to be refuted.
/-- The tree of `sinh(x₁) - x₂` over `[0,3] × [0,3/2]`, with the printed `aux_sinh_`. -/
noncomputable def SyntaxTree.sinhCoraTree : SyntaxTree 2 :=
  .minus (.sinhCora (.var 0 (interval 0 3))) (.var 1 (interval 0 (3 / 2)))

end CORALean

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The upper bound `aux_sinhCora_` returns is at most `asinh 1` for a target starting at most at
`1`. -/
private theorem SyntaxTree.funHanSinhCora_sup_le {int prev : Dom}
    (h : int.inf 0 ≤ 1) : -- --- CONCL ---
    ∃ val, funHanSinhCora int prev = .ok val ∧ val.sup 0 ≤ Real.arsinh 1 := by -- --- PROOF ---
  refine ⟨_, rfl, ?_⟩
  simp only [Real.Interval.intersection, interval]
  refine (min_le_right _ _).trans (max_le ?_ ?_)
  · exact Real.arsinh_le_arsinh.2 (max_le h (by norm_num))
  · exact Real.arsinh_le_arsinh.2 (min_le_right _ _)

/-- `backpropagation` of the printed `sinh` loses the zero `(1, sinh 1)`. -/
theorem SyntaxTree.sinhCora_counterexample : -- --- CONCL ---
    ∃ (x : Fin 2 → ℝ) (B : Real.Interval (Vec ℝ 2)),
      InBox B x ∧ Dom.contains (interval 0 0) (sinhCoraTree.eval x) ∧
      ¬ ∃ r, backpropagation sinhCoraTree (interval 0 0) B = .ok r ∧ InBox r
        x := by -- --- PROOF ---
  have hs1 : Real.sinh 1 < 3 / 2 := by
    have h3 := Real.exp_one_lt_three
    have h0 : 0 < Real.exp (-1) := Real.exp_pos _
    rw [Real.sinh_eq]
    linarith
  have hs2 : 1 < Real.sinh 1 := Real.self_lt_sinh_iff.2 one_pos
  have ha : Real.arsinh 1 < 1 := by
    have := Real.arsinh_lt_arsinh.2 hs2
    rwa [Real.arsinh_sinh] at this
  refine ⟨![1, Real.sinh 1], ⟨fun _ => 0, ![3, 3 / 2]⟩, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp
    · simp
      exact hs1.le
  · simp [sinhCoraTree, SyntaxTree.minus, SyntaxTree.sinhCora, eval, Binary.fn, Unary.fn,
      interval, Dom.contains]
  · rintro ⟨r, hr, hxr⟩
    -- the root asks its first operand, `sinh(x₁)`, for the target `(funHanMinus ...).left`
    obtain ⟨r₁, h₁, hx₁⟩ := backpropagation_binary_ok hr
    obtain ⟨val, hval, h₂⟩ := backpropagation_unary_ok h₁
    have key : ∀ int prev val, int.inf 0 ≤ 1 → funHanSinhCora int prev = .ok val →
        val.sup 0 ≤ Real.arsinh 1 := fun int prev val h hv => by
      obtain ⟨v', hv', hle⟩ := funHanSinhCora_sup_le (prev := prev) h
      rw [hv'] at hv
      cases hv
      exact hle
    have hle := key _ _ _ (by
      simp [funHanMinus, SyntaxTree.sinhCora, value, Real.Interval.intersection, Real.Interval.sinh,
        Real.Interval.plus, interval]) hval
    -- the coordinate `x₁` is cut to `asinh 1 < 1`
    have hsup := backpropagation_var_ok h₂
    have hx0 := (hx₁ _ hxr 0).2
    rw [hsup] at hx0
    have : (1 : ℝ) ≤ Real.arsinh 1 := by
      simpa using hx0.trans ((min_le_left _ _).trans hle)
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
