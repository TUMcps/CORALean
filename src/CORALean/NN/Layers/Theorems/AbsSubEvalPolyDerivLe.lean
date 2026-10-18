module

public import CORALean.NN.Layers.Operations.PolyDerivBoundUp
public import CORALean.NN.Layers.Theorems.AbsSubLeSpread
public import CORALean.NN.Layers.Theorems.PolyDerivRadiusLe
public import CORALean.NN.Layers.Theorems.Real.AbsEvalPolyDerivSubCenterLe
public import CORALean.NN.Layers.Theorems.ToRealPolyDerivCenter

@[expose] public section

/-!
# The stored derivative bound a bracket for σ' buys

The difference splits at the center: the bracket's spread, then the radius, each rounded up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem abs_sub_evalPolyDeriv_le {c : Fin (n + 1) → 𝕋} {σ' : ℝ → ℝ} {loD hiD l u : 𝕋}
    {x : ℝ} (hlo : toReal loD ≤ σ' x) (hhi : σ' x ≤ toReal hiD)
    (hl : toReal l ≤ x) (hu : x ≤ toReal u) : -- --- STMT ---
    |σ' x - Real.evalPolyDeriv (fun k => toReal (c k)) x|
      ≤ toReal (polyDerivBoundUp c loD hiD l u) := by -- --- PROOF ---
  have h1 := abs_sub_le_spread (c := polyDerivCenter c) hlo hhi
  have h2 := Real.abs_evalPolyDeriv_sub_center_le (fun k => toReal (c k)) hl hu
  have h3 := polyDerivRadius_le c l u
  have h4 := add_le_addUp (maximum (subUp hiD (polyDerivCenter c))
    (subUp (polyDerivCenter c) loD)) (polyDerivRadiusUp c l u)
  rw [toReal_polyDerivCenter] at h1
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
