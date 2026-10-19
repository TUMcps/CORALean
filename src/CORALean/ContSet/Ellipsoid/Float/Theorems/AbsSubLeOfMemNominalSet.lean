module

public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Ellipsoid.Real.Theorems.AbsSubLeSqrtDiag
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic

@[expose] public section

/-!
# The nominal part lies in the box `q ± √max(0, diag Q)`

CORA's `interval(E)`, `q ± √diag(Q)`, read at the stored floats: where `Q` is positive
semi-definite this is `Real.Ellipsoid.abs_sub_le_sqrt_diag`, and where it is not the nominal part
is the center alone. The `max` with `0` makes the bound hold for any stored `Q`, which is what
lets an operation fall back to the box without first certifying `Q`.

## Inputs
* `E` – ellipsoid
* `x` – point
* `i` – coordinate

## Hypotheses
* `hx` – `x` in the nominal part

## Conclusion
* `x` is within `√max(0, Qᵢᵢ)` of the center in coordinate `i`
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the nominal part is within `√max(0, Qᵢᵢ)` of the center in coordinate `i`. -/
theorem Ellipsoid.abs_sub_le_of_mem_nominalSet {E : Ellipsoid 𝕋 n} {x : Vec ℝ n}
    (hx : x ∈ nominalSet E) (i : Fin n) :
    |x i - toReal (E.q i)| ≤ Real.sqrt (max 0 (toReal (E.Q i i))) := by -- --- PROOF ---
  by_cases hpsd : (toRealMat E.Q).PosSemidef
  · -- the ellipsoid of `Q`, in its box
    have hx' : x ∈ (⟨toRealMat E.Q, toRealVec E.q, hpsd⟩ : Real.Ellipsoid n).construct := by
      have : x ∈ (nominal E).ellipsoid.construct := hx
      rwa [Ellipsoid.nominal_of_psd hpsd] at this
    have h := Real.Ellipsoid.abs_sub_le_sqrt_diag _ hx' i
    exact h.trans (Real.sqrt_le_sqrt (le_max_right _ _))
  · -- refused: the center alone
    obtain ⟨u, -, rfl⟩ := Ellipsoid.mem_nominalSet_iff.mp hx
    have hG : (nominal E).ellipsoid.G = 0 := by
      rw [Real.Ellipsoid.G_eq_zero_iff, Ellipsoid.nominal_Q_eq, if_neg hpsd]
    rw [hG, zero_mulVec, add_zero]
    simp [toRealVec]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
