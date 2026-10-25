module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.LevelSet.Real.LevelSet
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Conditional affine transformations

[1, Fig. 3]'s CAT functions, the form AI2 writes a network in before it abstracts it: an affine map
`W x + b`, a list of guarded cases, or a composition; `cases` returns the function of the first
condition the point satisfies. A condition is a level set (`CatCond`): [1]'s atoms are its affine
rows (`CatCond.ge`, `nonneg`, `neg`), a conjunction is two stacked (`LevelSet.and_`). A guard is
unbounded, so a `LevelSet`, not a `PolyLevelSet`.

`Evaluates` is a relation: a point no case accepts has no value, as in the paper. `image` is the
concrete transformer `T_f` of [1, Sec. III (transformers)].

## Inputs
* `n` – input dimension

## Output
* guard, a level set in the input space

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A guard: the points of a level set on the input, affine `≤`/`<` rows for the conjunctions of
[1]'s atoms. -/
abbrev CatCond (n : ℕ) : Type := Real.LevelSet n

/-- `W x + b`, `k` guarded cases, or `f₂ ∘ f₁`. -/
inductive Cat (𝕋 : Type) : ℕ → ℕ → Type where
  | affine {m n : ℕ} (W : Mat 𝕋 n m) (b : Vec 𝕋 n) : Cat 𝕋 m n
  | cases {m n : ℕ} (k : ℕ) (E : Fin k → CatCond m) (f : Fin k → Cat 𝕋 m n) : Cat 𝕋 m n
  | comp {m l n : ℕ} (f₂ : Cat 𝕋 l n) (f₁ : Cat 𝕋 m l) : Cat 𝕋 m n

/-- `Evaluates f x y`: `f` maps `x` to `y`. A case applies when its guard holds and no earlier one
does. -/
inductive Cat.Evaluates : {m n : ℕ} → Cat 𝕋 m n → Vec ℝ m → Vec ℝ n → Prop where
  | affine {m n : ℕ} (W : Mat 𝕋 n m) (b : Vec 𝕋 n) (x : Vec ℝ m) :
      Cat.Evaluates (.affine W b) x (toRealMat W *ᵥ x + toRealVec b)
  | cases {m n k : ℕ} (E : Fin k → CatCond m) (f : Fin k → Cat 𝕋 m n) (i : Fin k)
      {x : Vec ℝ m} {y : Vec ℝ n} (hi : x ∈ (E i).construct)
      (hfirst : ∀ j < i, x ∉ (E j).construct)
      (hy : Cat.Evaluates (f i) x y) : Cat.Evaluates (.cases k E f) x y
  | comp {m l n : ℕ} (f₂ : Cat 𝕋 l n) (f₁ : Cat 𝕋 m l) {x : Vec ℝ m} (z : Vec ℝ l)
      {y : Vec ℝ n} (h₁ : Cat.Evaluates f₁ x z) (h₂ : Cat.Evaluates f₂ z y) : Cat.Evaluates (.comp
          f₂ f₁) x y

/-- The concrete transformer `T_f(X) = {f(x) | x ∈ X}`. -/
def Cat.image {m n : ℕ} (f : Cat 𝕋 m n) (X : Set (Vec ℝ m)) : Set (Vec ℝ n) :=
  {y | ∃ x ∈ X, f.Evaluates x y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
