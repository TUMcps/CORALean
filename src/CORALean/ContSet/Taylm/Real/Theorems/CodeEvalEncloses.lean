module

public import CORALean.ContSet.Taylm.Real.Operations.CodeEval
public import CORALean.ContSet.Taylm.Real.Theorems.IntrinsicEncloses
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.PlusOuter
public import CORALean.ContSet.Taylm.Real.Theorems.TimesOuter
public import CORALean.ContSet.Taylm.Real.Theorems.UminusOuter

@[expose] public section

/-!
# The fundamental theorem of Taylor model arithmetic

[1, Thm. 2]: executing a code list for `g` from models of `f` gives a model of `g ∘ f`. The proof
is the source's, "by induction over the code list of `g` from the elementary properties of the
Taylor model arithmetic". The source's hypothesis, `g` defined over the range of `P_f + I_f`, does
not make the list executable: an intrinsic's condition is checked on the model it is handed,
whose bound may be wider than the range. So the theorem is stated for a run that returns a model,
and `codeEval` returns `none` exactly where an intrinsic's condition fails.

## Inputs
* `m` – number of variables
* `N` – expansion order
* `F` – variable models
* `f` – variable functions

## Hypotheses
* `hF` – each model encloses its function

## Conclusion
* any evaluated model encloses the code list's function

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.codeEval_encloses {m : ℕ} {N : ℕ} {F : Fin m → Taylm n}
    {f : Fin m → Vec ℝ n → ℝ} (hF : ∀ i, (F i).Encloses (f i)) : -- --- CONCL ---
    ∀ (e : Taylm.CodeList ℝ m) {T : Taylm n}, Taylm.codeEval N F e = some T →
      T.Encloses fun t => e.eval fun i => f i t := by -- --- PROOF ---
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
  | intr s a iha =>
    intro T hT
    simp only [Taylm.codeEval, Option.bind_eq_some_iff] at hT
    obtain ⟨A, hA, hs⟩ := hT
    exact Taylm.intrinsic_encloses (iha hA) s _ hs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
