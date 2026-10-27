module

public import CORALean.NN.Layers.Operations.PolyRelaxationPadTo
public import CORALean.NN.Layers.Definitions.EvalPoly
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.SuccPred
public import CORALean.NN.Layers.Operations.PadCoeffs
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A padded relaxation is sound

Where the degree bound is spent: the padded polynomial is the original one.

## Inputs
* `P` – polynomial relaxation

## Hypotheses
* `h` – the degree is at most the higher degree
* `hP` – relaxation is sound for the activation

## Conclusion
* the padded relaxation is sound for the activation
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {k M : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k : ℕ}

/-- Padded coefficients read back as the exact padding. -/
private theorem aux_toReal_padCoeffs (c : Fin (k + 1) → 𝕋) (M : ℕ)
    (j : Fin (M + 1)) : -- --- CONCL ---
    toReal (padCoeffs c M j) = Real.padCoeffs (fun i => toReal (c i)) M j := by -- --- PROOF ---
  show toReal (if h : (j : ℕ) < k + 1 then c ⟨(j : ℕ), h⟩ else zero)
    = if h : (j : ℕ) < k + 1 then toReal (c ⟨(j : ℕ), h⟩) else 0
  -- the padded slot is the only one that moves, and `zero` reads as `0`
  by_cases h : (j : ℕ) < k + 1
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, toReal_zero]

end


namespace Real
/-- Padding changes no value of a polynomial. -/
private theorem aux_evalPoly_padCoeffs {k M : ℕ} (c : Fin (k + 1) → ℝ) (h : k ≤ M)
    (t : ℝ) : -- --- CONCL ---
    evalPoly (padCoeffs c M) t = evalPoly c t := by -- --- PROOF ---
  -- both sides are one sum over ℕ, cut at a different length
  have hL : evalPoly (padCoeffs c M) t
      = ∑ j ∈ Finset.range (M + 1), (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j := by
    show (∑ i : Fin (M + 1), (if hj : (i : ℕ) < k + 1 then c ⟨(i : ℕ), hj⟩ else 0) * t ^ (i : ℕ))
      = _
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j) (M + 1)
  have hfin : (∑ i : Fin (k + 1),
        (if hj : (i : ℕ) < k + 1 then c ⟨(i : ℕ), hj⟩ else 0) * t ^ (i : ℕ))
      = ∑ j ∈ Finset.range (k + 1), (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j :=
    Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j) (k + 1)
  have hR : (∑ j ∈ Finset.range (k + 1), (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j)
      = evalPoly c t := by
    rw [← hfin]
    -- inside `k + 1` the padding branch is never taken
    show _ = ∑ i : Fin (k + 1), c i * t ^ (i : ℕ)
    exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.isLt]
  rw [hL, ← hR]
  -- and past `k + 1` the padded coefficient is zero, so the term drops out
  have hsub : Finset.range (k + 1) ⊆ Finset.range (M + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  refine (Finset.sum_subset hsub ?_).symm
  intro j _ hj
  rw [dif_neg (by simpa using hj), zero_mul]
end Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxation.padTo_encloses {P : PolyRelaxation 𝕋 k} (h : k ≤ M)
    (hP : P.Encloses σ) : -- --- CONCL ---
    (P.padTo M).Encloses σ := by -- --- PROOF ---
  refine ⟨fun {l u _t} hl hu => ?_⟩
  have hco : (fun j => toReal ((P.padTo M).coeffs l u j))
      = Real.padCoeffs (fun i => toReal (P.coeffs l u i)) M := by
    funext j
    exact aux_toReal_padCoeffs (P.coeffs l u) M j
  rw [hco, Real.aux_evalPoly_padCoeffs _ h]
  exact hP.sound hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
