module

public import CORALean.ContSet.Taylm.Float.Operations.Intrinsic
public import CORALean.ContSet.Taylm.Float.Operations.Basic
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

## Inputs
* `p` – precision of the exponential
* `q` – precision of the logarithm
* `s` – precision of the trigonometric functions
* `T` – Taylor model
* `f` – enclosed function
* `k` – intrinsic

## Hypotheses
* `h` – the model encloses the function

## Conclusion
* any returned model encloses the intrinsic of the function

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What `belowPow` certifies. -/
theorem Taylm.aux_toReal_le_of_belowPow {p : ℕ} {x : 𝕋}
    (h : Taylm.belowPow p x = true) : -- --- CONCL ---
    toReal x ≤ 2 ^ p / 2 := by -- --- PROOF ---
  have hit : ∀ k : ℕ, toReal (half^[k] x) = toReal x / 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', toReal_half, ih, pow_succ, div_div]
  have := toReal_le_of_le h
  rw [hit, toReal_half, toReal_one] at this
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  rw [div_le_iff₀ h2] at this
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.intrinsic_encloses (p q s : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (k : Real.Taylm.Intrinsic) : -- --- CONCL ---
    ∀ T' ∈ T.intrinsic p q s k,
      T'.Encloses fun t => k.fn (f t) := by -- --- PROOF ---
  intro T' (hk : T.intrinsic p q s k = some T')
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
  · exact hg hk fun hc => Taylm.exp_outer p h (Taylm.aux_toReal_le_of_belowPow hc)
  · exact hg hk fun hc => Taylm.log_outer q s h (by
      have := toReal_lt_of_ltStrict hc; rwa [toReal_zero] at this)
  · exact hu hk (Taylm.sin_outer p h)
  · exact hu hk (Taylm.cos_outer p h)
  · exact hg hk fun hc => Taylm.sinh_outer p h (Taylm.aux_toReal_le_of_belowPow hc)
  · exact hg hk fun hc => Taylm.cosh_outer p h (Taylm.aux_toReal_le_of_belowPow hc)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
