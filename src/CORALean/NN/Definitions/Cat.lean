module

public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Conditional affine transformations

[1, Fig. 3]'s CAT functions, the form AI2 writes a network in before it abstracts it: an affine
map `W x + b`, a list of guarded cases, or a composition. A condition is a conjunction of the
atoms `xᵢ ≥ xⱼ`, `xᵢ ≥ 0` and `xᵢ < 0`, and `cases` returns the function of the first condition
the point satisfies.

The weights are stored in the scalar `𝕋` and read through `toReal`, so one CAT function is both
the network a machine runs and the exact function it denotes; the conditions mention no
scalar. `Eval` is a relation rather than a function: a point no case accepts has no value, as
in the paper, where `case` is defined by its first satisfied condition and by nothing else.
`image` is the concrete transformer `T_f` of [1, Sec. III (transformers)].

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- A guard: `E ∧ E`, `xᵢ ≥ xⱼ`, `xᵢ ≥ 0` or `xᵢ < 0`. -/
inductive CatCond (n : ℕ) where
  | and (E₁ E₂ : CatCond n)
  | ge (i j : Fin n)
  | nonneg (i : Fin n)
  | neg (i : Fin n)

/-- A point satisfies a guard. -/
def CatCond.Holds {n : ℕ} : CatCond n → Vec ℝ n → Prop
  | .and E₁ E₂, x => E₁.Holds x ∧ E₂.Holds x
  | .ge i j, x => x j ≤ x i
  | .nonneg i, x => 0 ≤ x i
  | .neg i, x => x i < 0

/-- `W x + b`, `k` guarded cases, or `f₂ ∘ f₁`. -/
inductive Cat (𝕋 : Type) : ℕ → ℕ → Type where
  | affine {m n : ℕ} (W : Mat 𝕋 n m) (b : Vec 𝕋 n) : Cat 𝕋 m n
  | cases {m n : ℕ} (k : ℕ) (E : Fin k → CatCond m) (f : Fin k → Cat 𝕋 m n) : Cat 𝕋 m n
  | comp {m l n : ℕ} (f₂ : Cat 𝕋 l n) (f₁ : Cat 𝕋 m l) : Cat 𝕋 m n

/-- `Eval f x y`: `f` maps `x` to `y`. A case applies when its guard holds and no earlier one
does. -/
inductive Cat.Eval : {m n : ℕ} → Cat 𝕋 m n → Vec ℝ m → Vec ℝ n → Prop where
  | affine {m n : ℕ} (W : Mat 𝕋 n m) (b : Vec 𝕋 n) (x : Vec ℝ m) :
      Cat.Eval (.affine W b) x (toRealMat W *ᵥ x + toRealVec b)
  | cases {m n k : ℕ} (E : Fin k → CatCond m) (f : Fin k → Cat 𝕋 m n) (i : Fin k)
      {x : Vec ℝ m} {y : Vec ℝ n} (hi : (E i).Holds x) (hfirst : ∀ j < i, ¬ (E j).Holds x)
      (hy : Cat.Eval (f i) x y) : Cat.Eval (.cases k E f) x y
  | comp {m l n : ℕ} (f₂ : Cat 𝕋 l n) (f₁ : Cat 𝕋 m l) {x : Vec ℝ m} (z : Vec ℝ l)
      {y : Vec ℝ n} (h₁ : Cat.Eval f₁ x z) (h₂ : Cat.Eval f₂ z y) : Cat.Eval (.comp f₂ f₁) x y

/-- The concrete transformer `T_f(X) = {f(x) | x ∈ X}`. -/
def Cat.image {m n : ℕ} (f : Cat 𝕋 m n) (X : Set (Vec ℝ m)) : Set (Vec ℝ n) :=
  {y | ∃ x ∈ X, f.Eval x y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
