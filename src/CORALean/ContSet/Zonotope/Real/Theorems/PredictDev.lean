module

public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# A point of the prediction, from a point of the old estimate and the disturbance

[1, Eq. 2]: the prediction `A X̂ ⊕ F Bᵐ` has, around its center, the points `A θ + F γ`, with
`p + θ` a point of the old estimate `X̂` (center `p`) and `γ` in the unit box. The first step of
every P-radius bound of [1, Eq. 4] to [1, Alg. 2].

## Inputs
* `A` – state matrix
* `F` – noise matrix
* `X` – state zonotope
* `z` – point of the prediction

## Hypotheses
* `hz` – `z` lies in the predicted zonotope

## Conclusion
* `z` is the center plus a state deviation and bounded noise

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of `A X ⊕ F Bᵐ` is its center plus `A θ + F γ`. -/
theorem Zonotope.predict_dev (A : Mat ℝ n n) (F : Mat ℝ n m) (X : Zonotope (Vec ℝ n))
    {z : Vec ℝ n}
    (hz : z ∈ ((X.mtimes A).plus (⟨m, 0, fun j i => F i j⟩ : Zonotope (Vec ℝ n))).construct) :
    ∃ θ : Vec ℝ n, ∃ γ : Vec ℝ m, X.c + θ ∈ X.construct ∧ (∀ j, |γ j| ≤ 1) ∧
      z - ((X.mtimes A).plus (⟨m, 0, fun j i => F i j⟩ : Zonotope (Vec ℝ n))).c
        = A *ᵥ θ + F *ᵥ γ := by -- --- PROOF ---
  -- the sum of the two zonotopes, named once
  set Zp : Zonotope (Vec ℝ n) :=
    (X.mtimes A).plus (⟨m, 0, fun j i => F i j⟩ : Zonotope (Vec ℝ n))
  obtain ⟨b, hb, rfl⟩ : ∃ b : Fin (X.h + m) → ℝ, (∀ j, |b j| ≤ 1) ∧
      z = Zp.c + ∑ j : Fin (X.h + m), b j • Zp.G j := hz
  -- the coefficients of the old estimate and of the disturbance
  refine ⟨∑ j : Fin X.h, b (Fin.castAdd m j) • X.G j, fun j => b (Fin.natAdd X.h j),
    ⟨fun j => b (Fin.castAdd m j), fun j => hb _, rfl⟩, fun j => hb _, ?_⟩
  rw [add_sub_cancel_left, Fin.sum_univ_add]
  simp only [Zp, Zonotope.plus, Zonotope.mtimes, Fin.append_left, Fin.append_right,
    Matrix.mulVec_sum, Matrix.mulVec_smul]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
