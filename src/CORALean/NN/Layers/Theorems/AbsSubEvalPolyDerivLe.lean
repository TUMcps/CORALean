module

public import CORALean.NN.Layers.Operations.PolyDerivBoundUp
public import CORALean.NN.Layers.Theorems.AbsSubLeSpread
public import CORALean.NN.Layers.Definitions.PolyDerivBound
public import CORALean.NN.Layers.Operations.PolyDerivRadiusUp
public import CORALean.NN.Layers.Theorems.PowRangeBounds
public import Mathlib.Tactic.Positivity
public import CORALean.NN.Layers.Theorems.Real.AbsEvalPolyDerivSubCenterLe
public import CORALean.NN.Layers.Operations.PolyDerivCenter
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The stored derivative bound a bracket for σ' buys

The difference splits at the center: the bracket's spread, then the radius, each rounded up.

## Inputs
* `c` – fit coefficients
* `σ'` – derivative of the activation
* `loD` – lower end of the derivative bracket
* `hiD` – upper end of the derivative bracket
* `l` – lower end of the box
* `u` – upper end of the box
* `x` – point in the box

## Hypotheses
* `hlo` – bracket's lower end is below the derivative
* `hhi` – bracket's upper end is above the derivative
* `hl` – point is above the lower end
* `hu` – point is below the upper end

## Conclusion
* the derivative differs from the fit's by at most the stored bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A stored center reads back exactly. -/
theorem aux_toReal_polyDerivCenter (c : Fin (n + 1) → 𝕋) : -- --- CONCL ---
    toReal (polyDerivCenter c)
      = Real.polyDerivCenter (fun k => toReal (c k)) := by -- --- PROOF ---
  show toReal (if h : 1 < n + 1 then c ⟨1, h⟩ else zero)
    = ∑ i : Fin (n + 1), if (i : ℕ) = 1 then toReal (c i) else 0
  by_cases h : 1 < n + 1
  · -- one index carries the linear term and every other contributes nothing
    have hsum : (∑ i : Fin (n + 1), if (i : ℕ) = 1 then toReal (c i) else 0)
        = toReal (c ⟨1, h⟩) := by
      rw [Finset.sum_eq_single (⟨1, h⟩ : Fin (n + 1))]
      · rw [if_pos rfl]
      · exact fun b _ hb => if_neg fun hb1 => hb (Fin.ext hb1)
      · exact fun hmem => absurd (Finset.mem_univ _) hmem
    rw [dif_pos h, hsum]
  · have hn : n = 0 := by omega
    subst hn
    rw [dif_neg h, toReal_zero, Fin.sum_univ_one, if_neg (by norm_num)]


/-- A stored radius bounds the exact one. -/
theorem aux_polyDerivRadius_le (c : Fin (n + 1) → 𝕋) (l u : 𝕋) : -- --- CONCL ---
    Real.polyDerivRadius (fun k => toReal (c k)) (toReal l) (toReal u)
      ≤ toReal (polyDerivRadiusUp c l u) := by -- --- PROOF ---
  show (∑ i : Fin (n + 1), if (i : ℕ) = 1 then (0 : ℝ)
    else |toReal (c i)| * (i : ℕ) * max |toReal l| |toReal u| ^ ((i : ℕ) - 1)) ≤ _
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
  by_cases hi : (i : ℕ) = 1
  · rw [if_pos hi, if_pos hi, toReal_zero]
  · rw [if_neg hi, if_neg hi]
    -- the box's worse end, the degree count from above, and the coefficient exactly
    have hm : toReal (maximum (absolute l) (absolute u)) = max |toReal l| |toReal u| := by
      rw [toReal_maximum, toReal_absolute, toReal_absolute]
    have hp := (powRange_bounds (maximum (absolute l) (absolute u)) ((i : ℕ) - 1)).2
    rw [hm] at hp
    have hnat : ((i : ℕ) : ℝ) ≤ toReal (nsmulUp (i : ℕ) (one : 𝕋)) := by
      have hn := le_nsmulUp (i : ℕ) (one : 𝕋)
      rwa [toReal_one, mul_one] at hn
    have h1 : |toReal (c i)| * ((i : ℕ) : ℝ)
        ≤ toReal (mulUp (absolute (c i)) (nsmulUp (i : ℕ) one)) := by
      refine le_trans ?_ (mul_le_mulUp _ _)
      rw [toReal_absolute]
      exact mul_le_mul_of_nonneg_left hnat (abs_nonneg _)
    have h0 : (0 : ℝ) ≤ |toReal (c i)| * ((i : ℕ) : ℝ) :=
      mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
    refine le_trans (mul_le_mul h1 hp (by positivity) (le_trans h0 h1)) (mul_le_mulUp _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem abs_sub_evalPolyDeriv_le {c : Fin (n + 1) → 𝕋} {σ' : ℝ → ℝ} {loD hiD l u : 𝕋}
    {x : ℝ} (hlo : toReal loD ≤ σ' x) (hhi : σ' x ≤ toReal hiD)
    (hl : toReal l ≤ x) (hu : x ≤ toReal u) : -- --- CONCL ---
    |σ' x - Real.evalPolyDeriv (fun k => toReal (c k)) x|
      ≤ toReal (polyDerivBoundUp c loD hiD l u) := by -- --- PROOF ---
  have h1 := abs_sub_le_spread (c := polyDerivCenter c) hlo hhi
  have h2 := Real.abs_evalPolyDeriv_sub_center_le (fun k => toReal (c k)) hl hu
  have h3 := aux_polyDerivRadius_le c l u
  have h4 := add_le_addUp (maximum (subUp hiD (polyDerivCenter c))
    (subUp (polyDerivCenter c) loD)) (polyDerivRadiusUp c l u)
  rw [aux_toReal_polyDerivCenter] at h1
  rw [polyDerivBoundUp]
  -- the difference splits at the center: the bracket's spread, then the radius
  calc |σ' x - Real.evalPolyDeriv (fun k => toReal (c k)) x|
      ≤ |σ' x - Real.polyDerivCenter (fun k => toReal (c k))|
        + |Real.polyDerivCenter (fun k => toReal (c k))
          - Real.evalPolyDeriv (fun k => toReal (c k)) x| := abs_sub_le _ _ _
    _ ≤ toReal (addUp (maximum (subUp hiD (polyDerivCenter c))
        (subUp (polyDerivCenter c) loD)) (polyDerivRadiusUp c l u)) := by
      rw [abs_sub_comm (Real.polyDerivCenter fun k => toReal (c k))]
      linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
