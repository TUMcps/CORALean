module

public import CORALean.ContSet.Taylm.Float.Operations.Intrinsic
public import CORALean.ContSet.Taylm.Float.Theorems.ToRealLeOfBelowPow
public import CORALean.ContSet.Taylm.Float.Theorems.ExpOuter
public import CORALean.ContSet.Taylm.Float.Theorems.LogOuter
public import CORALean.ContSet.Taylm.Float.Theorems.SinOuter
public import CORALean.ContSet.Taylm.Float.Theorems.CosOuter
public import CORALean.ContSet.Taylm.Float.Theorems.SinhOuter
public import CORALean.ContSet.Taylm.Float.Theorems.CoshOuter

@[expose] public section

/-!
# A float intrinsic encloses its function

Whenever the float `Taylm.intrinsic` returns a model, its check passed, so the operation's outer
theorem applies: the source's intrinsics in admissible floating-point arithmetic, one intrinsic
at a time, as the induction of [1, Thm. 3] uses it.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
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

theorem Taylm.intrinsic_encloses (p q s : ℕ) {T T' : Taylm 𝕋 n} {f : Vec ℝ n → ℝ}
    (h : T.Encloses f) (k : Real.Taylm.Intrinsic) (hk : T.intrinsic p q s k = some T') :
    T'.Encloses fun t => k.fn (f t) := by -- --- PROOF ---
  -- an unguarded intrinsic returns its model
  have hu : ∀ {U : Taylm 𝕋 n}, some U = some T' → U.Encloses (fun t => k.fn (f t)) →
      T'.Encloses fun t => k.fn (f t) := fun hU hE => by
    rw [Option.some.injEq] at hU; exact hU ▸ hE
  -- a guarded one returned a model, so its check passed
  have hg : ∀ {b : Bool} {U : Taylm 𝕋 n}, (if b = true then some U else none) = some T' →
      (b = true → U.Encloses (fun t => k.fn (f t))) → T'.Encloses fun t => k.fn (f t) := by
    intro b U hU hE
    split_ifs at hU with hb
    exact hu hU (hE hb)
  cases k <;> simp only [Taylm.intrinsic, reduceCtorEq] at hk
  · exact hg hk fun hc => Taylm.exp_outer p h (Taylm.toReal_le_of_belowPow hc)
  · exact hg hk fun hc => Taylm.log_outer q s h (by
      have := toReal_lt_of_ltStrict hc; rwa [toReal_zero] at this)
  · exact hu hk (Taylm.sin_outer p h)
  · exact hu hk (Taylm.cos_outer p h)
  · exact hg hk fun hc => Taylm.sinh_outer p h (Taylm.toReal_le_of_belowPow hc)
  · exact hg hk fun hc => Taylm.cosh_outer p h (Taylm.toReal_le_of_belowPow hc)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
