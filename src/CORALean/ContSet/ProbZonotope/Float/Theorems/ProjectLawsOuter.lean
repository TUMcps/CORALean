module

public import CORALean.ContSet.ProbZonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.ProjectOuter
public import CORALean.ContSet.ProbZonotope.Real.Theorems.MapMultivariateGaussian

@[expose] public section

/-!
# `ProbZonotope.project` projects the laws

Outer: the image of a law of `P` under the coordinate projection is a law of `P.project dims`,
through the selection matrix: `Σ(dims, dims) = S Σ Sᵀ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open MeasureTheory ProbabilityTheory Matrix WithLp FloatOps SoundFloatArithmetic
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.project_laws_outer {m : ℕ} (P : ProbZonotope 𝕋 n) (dims : Fin m → Fin n) :
    (fun μ : Measure (EuclideanSpace ℝ (Fin n)) =>
        μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
          (toLp 2 (fun k => ofLp x (dims k)) : EuclideanSpace ℝ (Fin m)))) '' P.laws
      ⊆ (P.project dims).laws := by -- --- PROOF ---
  rintro _ ⟨_, ⟨a, ha, S, hS, hp, rfl⟩, rfl⟩
  -- the selection matrix picks the coordinates `dims`
  have hv : ∀ x : Vec ℝ n, (Matrix.of fun (i : Fin m) (j : Fin n) =>
      if j = dims i then (1 : ℝ) else 0) *ᵥ x = fun k => x (dims k) := by
    intro x; funext i
    simp [Matrix.mulVec, dotProduct]
  have hC : S.submatrix dims dims = (Matrix.of fun (i : Fin m) (j : Fin n) =>
      if j = dims i then (1 : ℝ) else 0) * S * (Matrix.of fun (i : Fin m) (j : Fin n) =>
      if j = dims i then (1 : ℝ) else 0)ᵀ := by
    ext i j
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  refine ⟨fun k => a (dims k), Zonotope.project_outer P.Z dims ⟨a, ha, rfl⟩, S.submatrix dims dims,
    fun q => hS (dims q.1, dims q.2), ?_, ?_⟩
  · rw [hC]
    simpa [Matrix.mul_assoc] using hp.mul_mul_conjTranspose_same (Matrix.of fun (i : Fin m)
      (j : Fin n) => if j = dims i then (1 : ℝ) else 0)
  · -- the projection is the map of the selection matrix
    have hmap := Real.map_multivariateGaussian (Matrix.of fun (i : Fin m) (j : Fin n) =>
      if j = dims i then (1 : ℝ) else 0) (toLp 2 a) hp
    simp only [hv, hC] at hmap ⊢
    simpa using hmap

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
