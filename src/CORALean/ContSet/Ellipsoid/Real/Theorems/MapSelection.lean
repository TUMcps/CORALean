module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Map

@[expose] public section

/-!
# A map selecting coordinates reads the shape matrix's rows and columns

For `f x = x ∘ σ`, the image `f E` has shape matrix `S Q Sᵀ` with `S` the selection matrix, which is
`Q` at the rows and columns `σ`, CORA's `E.Q(dims, dims)` of `project`, and center `q ∘ σ`.

## Inputs
* `E` – ellipsoid
* `σ` – selected coordinates
* `f` – coordinate selection map

## Hypotheses
* `hf` – `f` reads the coordinates `σ`

## Conclusion
* the image has shape `Q(σ, σ)` and center `q(σ)`
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The image under a coordinate selection: `Q(σ, σ)` and `q(σ)`. -/
theorem Ellipsoid.map_selection (E : Ellipsoid n) (σ : Fin m → Fin n)
    (f : Vec ℝ n →ₗ[ℝ] Vec ℝ m) (hf : ∀ x i, f x i = x (σ i)) : -- --- CONCL ---
    (E.map f).Q = E.Q.submatrix σ σ ∧ (E.map f).q = fun i => E.q (σ i) := by -- --- PROOF ---
  have hS : ∀ i k, LinearMap.toMatrix' f i k = if σ i = k then (1 : ℝ) else 0 := by
    intro i k
    rw [LinearMap.toMatrix'_apply, hf]
    simp [Pi.single_apply]
  constructor
  · ext i j
    show (LinearMap.toMatrix' f * E.Q * (LinearMap.toMatrix' f)ᵀ) i j = _
    simp [Matrix.mul_apply, hS]
  · funext i
    show (LinearMap.toMatrix' f *ᵥ E.q) i = _
    simp [Matrix.mulVec, dotProduct, hS]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
