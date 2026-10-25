module

public import CORALean.ContDynamics.Conform.Definitions.TemplateZono

@[expose] public section

/-!
# Zono-conformal predictors

[1, Eq. 13] with [1, Eq. 15]: the prediction set `Y_ZCP(x) = {f(x) + D̄(x) u | u ∈ U}` of a
point predictor `f`, `D̄(x)` the derivative of the augmented predictor in the uncertainties at
`0`, and `U = ⟨0, G_u diag(α)⟩`; `classesSet` and `classesVec` are [1, Eq. 11]'s `classes`,
`classMat c` the `Tₘ` of [1, Eq. 21] for a point of class `c`. CORA's `confPredictor` holds these.

The constraints of [1, Thm. 6] and [1, Thm. 7] are, per data point, a convex set `C` of
coefficient vectors `β` and `|β| ≤ α`: `FitsUnder C α`. [1, Sec. 5.1.1]'s boundary point is
one where some `αⱼ > 0` cannot be reduced without losing the point: `IsBoundaryPoint`.

## Inputs
* `fx` – prediction at the point
* `D` – derivative in the uncertainties
* `Gu` – uncertainty generators
* `α` – generator scaling

## Output
* the zonotope of predictions around the point prediction

## References

* [1] L. Lützow, M. Eichelbeck, M. J. Kochenderfer and M. Althoff. "Zono-Conformal Prediction:
      Zonotope-Based Uncertainty Quantification for Regression and Classification Tasks". Journal of
      Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {ny nu : ℕ} {ι : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 13]: `{f(x) + D̄(x) u | u ∈ ⟨0, G_u diag(α)⟩}`. -/
def Conform.zcpSet [Fintype ι] (fx : Vec ℝ ny) (D : Mat ℝ ny nu) (Gu : ι → Vec ℝ nu)
    (α : ι → ℝ) : Set (Vec ℝ ny) :=
  {y | ∃ u ∈ Conform.templateZono 0 Gu α, y = fx + D *ᵥ u}

/-- [1, Eq. 11]: the classes a set of score vectors encodes. -/
def Conform.classesSet (Y : Set (Vec ℝ ny)) : Set (Fin ny) :=
  {i | ∃ y ∈ Y, ∀ j, y j ≤ y i}

/-- [1, Eq. 11]: the classes a score vector encodes. -/
def Conform.classesVec (y : Vec ℝ ny) : Set (Fin ny) :=
  {i | ∀ j, y j ≤ y i}

/-- [1, Eq. 21]: `T = vert(e_cᵀ) - I`, so that `(T z)ᵢ = z_c - zᵢ`. -/
noncomputable def Conform.classMat (c : Fin ny) : Mat ℝ ny ny :=
  Matrix.of fun i j => (if j = c then 1 else 0) - if i = j then 1 else 0

/-- A point's containment constraint at `α`: some `β ∈ C` with `|β| ≤ α`. -/
def Conform.FitsUnder (C : Set (ι → ℝ)) (α : ι → ℝ) : Prop :=
  ∃ β ∈ C, ∀ j, |β j| ≤ α j

/-- [1, Sec. 5.1.1]: reducing some `αⱼ > 0` by any amount loses the point. -/
def Conform.IsBoundaryPoint [DecidableEq ι] (C : Set (ι → ℝ)) (α : ι → ℝ) : Prop :=
  ∃ j, 0 < α j ∧ ∀ ε, 0 < ε → ε ≤ α j → ¬ Conform.FitsUnder C (Function.update α j (α j - ε))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
