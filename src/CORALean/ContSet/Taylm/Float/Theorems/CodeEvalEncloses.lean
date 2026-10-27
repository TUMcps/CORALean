module

public import CORALean.ContSet.Taylm.Float.Operations.CodeEval
public import CORALean.ContSet.Taylm.Float.Theorems.IntrinsicEncloses
public import CORALean.ContSet.Taylm.Real.Operations.CodeListMap
public import CORALean.ContSet.Taylm.Float.Theorems.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.PlusOuter
public import CORALean.ContSet.Taylm.Float.Theorems.TimesOuter
public import CORALean.ContSet.Taylm.Float.Theorems.UminusOuter

@[expose] public section

/-!
# The Taylor model enclosure theorem

[1, Thm. 3]: executing a code list for `g` in floating-point Taylor model arithmetic, from
models enclosing `f`, gives an enclosure of `g ∘ f` — of the code list read with its float
constants as reals. By induction over the code list, as the source proves it; the rounding is
paid inside each operation, so `P` is not the Taylor polynomial, only an enclosure's. As for
[1, Thm. 2], the statement is for a run that returns a model.

## Inputs
* `m` – number of variables
* `p` – precision of the exponential
* `q` – precision of the logarithm
* `s` – precision of the trigonometric functions
* `N` – expansion order
* `F` – variable models
* `f` – variable functions

## Hypotheses
* `hF` – each model encloses its function

## Conclusion
* any evaluated model encloses the code list's function

## References

* [1] [K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics,
      2003.](../../../../../../references/2003/makino-ijpam-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.codeEval_encloses {m : ℕ} (p q s N : ℕ) {F : Fin m → Taylm 𝕋 n}
    {f : Fin m → Vec ℝ n → ℝ} (hF : ∀ i, (F i).Encloses (f i)) : -- --- CONCL ---
    ∀ (e : Real.Taylm.CodeList 𝕋 m) {T : Taylm 𝕋 n}, Taylm.codeEval p q s N F e = some T →
      T.Encloses fun t => (e.map toReal).eval fun i => f i t := by -- --- PROOF ---
  intro e
  induction e with
  | var i =>
    intro T hT
    simp only [Taylm.codeEval, Option.some.injEq] at hT
    exact hT ▸ hF i
  | const c =>
    intro T hT
    simp only [Taylm.codeEval, Option.some.injEq] at hT
    exact hT ▸ Taylm.const_outer c N
  | add a b iha ihb =>
    intro T hT
    simp only [Taylm.codeEval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hT
    obtain ⟨A, hA, B, hB, rfl⟩ := hT
    exact Taylm.plus_outer (iha hA) (ihb hB)
  | mul a b iha ihb =>
    intro T hT
    simp only [Taylm.codeEval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hT
    obtain ⟨A, hA, B, hB, rfl⟩ := hT
    exact Taylm.times_outer (iha hA) (ihb hB)
  -- negation, then an intrinsic of a model the induction already has
  | neg a iha =>
    intro T hT
    simp only [Taylm.codeEval, Option.map_eq_some_iff] at hT
    obtain ⟨A, hA, rfl⟩ := hT
    exact Taylm.uminus_outer (iha hA)
  | intr k a iha =>
    intro T hT
    simp only [Taylm.codeEval, Option.bind_eq_some_iff] at hT
    obtain ⟨A, hA, hk⟩ := hT
    exact Taylm.intrinsic_encloses p q s (iha hA) k _ hk

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
