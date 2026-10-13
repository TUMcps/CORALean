import CORALean.Specification.STL.Definitions.DiscreteFormula

/-!
# The values the MILP encodings force

[1, Sec. IV-B]: every subformula `φ` gets a variable `z^φ_t`, tied by constraints to the values of
its operands, so that `z^φ_t = 1` iff `φ` holds at `t`; [1, Sec. V] does the same with `r^φ_t` and
`ρ`. Each gadget forces its variable to a function of the operands' values — the theorems
`STL.pred_encoding_iff`, `STL.conj_encoding_iff`, `STL.disj_encoding_iff` and
`STL.robust_conj_encoding` — and these are those values: `zEnc` and `rEnc` along the printed
recursion over the horizon `N`, `[t+a, t+b]` truncated to `[min(t+a, N), min(t+b, N)]`
[1, Sec. IV-B.3 (temporal)], and until
as `□[0,a] φ₁ ∧ ◇[a,b] φ₂ ∧ ◇[a,a](φ₁ U φ₂)` [1, Sec. IV-B.3 (until)], the unbounded until by
`z_t = z^{φ₂}_t ∨ (z^{φ₁}_t ∧ z_{t+1})`, `z_N = z^{φ₂}_N` (printed for `t = 1, …, N-1`, read from
`t = 0`). `nonstrict` replaces `z^{φ₂}_t` by `z^{φ₂}_t ∧ z^{φ₁}_t`, the recursion of the printed
semantics, where `φ₁` holds through the step `φ₂` does.

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `z^{φ₁ U φ₂}_i` of the operands' values `P`, `Q` over the horizon `N`. -/
def STL.untilEnc (N : ℕ) (nonstrict : Bool) (P Q : ℕ → Prop) (i : ℕ) : Prop :=
  if i < N then
    (if nonstrict then Q i ∧ P i else Q i) ∨ (P i ∧ STL.untilEnc N nonstrict P Q (i + 1))
  else (if nonstrict then Q i ∧ P i else Q i)
termination_by N - i

/-- `r^{φ₁ U φ₂}_i`, the same recursion with `max` and `min`. -/
noncomputable def STL.untilRob (N : ℕ) (nonstrict : Bool) (A B : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i < N then
    max (if nonstrict then min (B i) (A i) else B i)
      (min (A i) (STL.untilRob N nonstrict A B (i + 1)))
  else (if nonstrict then min (B i) (A i) else B i)
termination_by N - i

/-- `z^φ_t = 1`, [1, Sec. IV-B]. -/
def STL.DFormula.zEnc (N : ℕ) (nonstrict : Bool) : STL.DFormula X → (ℕ → X) → ℕ → Prop
  | .pred μ, x, t => 0 < μ (x t)
  | .npred μ, x, t => ¬ 0 < μ (x t)
  | .and φ ψ, x, t => φ.zEnc N nonstrict x t ∧ ψ.zEnc N nonstrict x t
  | .or φ ψ, x, t => φ.zEnc N nonstrict x t ∨ ψ.zEnc N nonstrict x t
  | .always a b _ φ, x, t =>
      ∀ i ∈ Finset.Icc (min (t + a) N) (min (t + b) N), φ.zEnc N nonstrict x i
  | .eventually a b _ φ, x, t =>
      ∃ i ∈ Finset.Icc (min (t + a) N) (min (t + b) N), φ.zEnc N nonstrict x i
  | .until a b _ φ ψ, x, t =>
      (∀ i ∈ Finset.Icc (min t N) (min (t + a) N), φ.zEnc N nonstrict x i) ∧       -- □[0,a] φ₁
      (∃ i ∈ Finset.Icc (min (t + a) N) (min (t + b) N), ψ.zEnc N nonstrict x i) ∧ -- ◇[a,b] φ₂
      STL.untilEnc N nonstrict (φ.zEnc N nonstrict x) (ψ.zEnc N nonstrict x)       -- ◇[a,a] U
        (min (t + a) N)

/-- `r^φ_t`, [1, Sec. V]. -/
noncomputable def STL.DFormula.rEnc (N : ℕ) (nonstrict : Bool) :
    STL.DFormula X → (ℕ → X) → ℕ → ℝ
  | .pred μ, x, t => μ (x t)
  | .npred μ, x, t => -μ (x t)
  | .and φ ψ, x, t => min (φ.rEnc N nonstrict x t) (ψ.rEnc N nonstrict x t)
  | .or φ ψ, x, t => max (φ.rEnc N nonstrict x t) (ψ.rEnc N nonstrict x t)
  | .always a b hab φ, x, t =>
      (Finset.Icc (min (t + a) N) (min (t + b) N)).inf'
        (Finset.nonempty_Icc.mpr (min_le_min_right N (by omega))) (φ.rEnc N nonstrict x)
  | .eventually a b hab φ, x, t =>
      (Finset.Icc (min (t + a) N) (min (t + b) N)).sup'
        (Finset.nonempty_Icc.mpr (min_le_min_right N (by omega))) (φ.rEnc N nonstrict x)
  | .until a b hab φ ψ, x, t =>
      min (min ((Finset.Icc (min t N) (min (t + a) N)).inf'                         -- □[0,a] φ₁
          (Finset.nonempty_Icc.mpr (min_le_min_right N (by omega))) (φ.rEnc N nonstrict x))
        ((Finset.Icc (min (t + a) N) (min (t + b) N)).sup'                          -- ◇[a,b] φ₂
          (Finset.nonempty_Icc.mpr (min_le_min_right N (by omega))) (ψ.rEnc N nonstrict x)))
        (STL.untilRob N nonstrict (φ.rEnc N nonstrict x) (ψ.rEnc N nonstrict x)    -- ◇[a,a] U
          (min (t + a) N))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
