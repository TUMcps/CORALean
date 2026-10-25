module

public import CORALean.ContDynamics.LinearSys.Definitions.InputLawsOver
public import CORALean.ContDynamics.LinearSys.Theorems.InputLawsAdd

@[expose] public section

/-!
# The input solution over `[kr, (k+1)r]` from the one over `[0, r]`

`[1, Prop. 4]`: `R̄([kr, (k+1)r]) = e^{A kr} R̄([0, r]) + R̄(kr)`. With `R̄(t)` the family of
Gaussian laws of the input solution (`LinearSys.inputLaws`), and the hull over an interval the
family over its times, the laws over `[kr, (k+1)r]` are exactly the laws of `e^{Akr} X + Y`,
`X` a law over `[0, r]` and `Y` an independent law at `kr`: the point statement
(`LinearSys.inputLaws_add`) at `a = s`, `b = kr`, for every `s ∈ [0, r]`. `r ≥ 0`, and the
input set is bounded.

## Inputs
* `sys` – linear system
* `C` – noise matrix
* `U` – input set
* `r` – step length
* `k` – step index

## Hypotheses
* `hr` – step length nonnegative
* `hbdd` – input set bounded

## Conclusion
* the laws over a later step are convolutions of the first step's laws and the earlier laws

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory ProbabilityTheory WithLp

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.inputLawsOver_add (sys : LinearSys 𝕋 n) (C : Mat ℝ n m) {U : S n} {r : ℝ}
    (hr : 0 ≤ r) (k : ℕ) (hbdd : Bornology.IsBounded (construct U)) : -- --- CONCL ---
    sys.inputLawsOver C U (k * r) ((k + 1) * r)
      = {ν | ∃ ν₁ ∈ sys.inputLawsOver C U 0 r, ∃ ν₂ ∈ sys.inputLaws C U (k * r),
          ν = (ν₁.map fun x => toLp 2 (exp ((k * r) • toRealMat sys.A) *ᵥ ofLp x))
            ∗ ν₂} := by -- --- PROOF ---
  have hk : 0 ≤ (k : ℝ) * r := mul_nonneg (Nat.cast_nonneg k) hr
  ext ν
  constructor
  · rintro ⟨t, ⟨ht1, ht2⟩, hν⟩
    -- the time `t = s + kr` with `s ∈ [0, r]`
    have hs : t = (t - k * r) + k * r := by ring
    rw [hs, LinearSys.inputLaws_add sys C (by linarith) hk hbdd] at hν
    obtain ⟨ν₁, hν₁, ν₂, hν₂, rfl⟩ := hν
    exact ⟨ν₁, ⟨t - k * r, ⟨by linarith, by linarith⟩, hν₁⟩, ν₂, hν₂, rfl⟩
  · rintro ⟨ν₁, ⟨s, ⟨hs0, hsr⟩, hν₁⟩, ν₂, hν₂, rfl⟩
    refine ⟨s + k * r, ⟨by linarith, by linarith⟩, ?_⟩
    rw [LinearSys.inputLaws_add sys C hs0 hk hbdd]
    exact ⟨ν₁, hν₁, ν₂, hν₂, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
