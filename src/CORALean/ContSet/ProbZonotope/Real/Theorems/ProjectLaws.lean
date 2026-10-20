module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Basic
public import CORALean.ContSet.ProbZonotope.Real.Theorems.MtimesLaws

@[expose] public section

/-!
# `ProbZonotope.project` maps the laws by the coordinate projection

The images of the laws of `P` under `x ↦ (x (dims k))ₖ` are exactly the laws of `P.project dims`
(the marginals on the selected coordinates, for any `dims`, repeats and reorderings included):
`project` is `mtimes` at the selection matrix, and `Theorems.MtimesLaws` applies. The covariance
must be positive semidefinite.

## Inputs
* `P` – probabilistic zonotope
* `dims` – indices indexed by `Fin m`

## Hypotheses
* `h` – `P.cov` is positive semidefinite

## Conclusion
* `ProbZonotope.project` maps the laws by the coordinate projection
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory Matrix WithLp

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The matrix that picks the coordinates `dims`. -/
def aux_selection (dims : Fin m → Fin n) : Mat ℝ m n :=
  Matrix.of fun i j => if j = dims i then 1 else 0

theorem aux_project_eq_mtimes (P : ProbZonotope n) (dims : Fin m → Fin n) :
    P.project dims = P.mtimes (aux_selection dims) := by -- --- PROOF ---
  have hv : ∀ x : Vec ℝ n, aux_selection dims *ᵥ x = fun k => x (dims k) := by
    intro x; funext i
    simp [aux_selection, Matrix.mulVec, dotProduct]
  have hZ : P.Z.project dims = Zonotope.mtimes (aux_selection dims) P.Z := by
    simp only [Zonotope.project, Zonotope.map, Zonotope.mtimes, hv]
    rfl
  have hC : P.cov.submatrix dims dims = aux_selection dims * P.cov * (aux_selection dims)ᵀ := by
    ext i j
    simp [aux_selection, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [ProbZonotope.project, ProbZonotope.mtimes, hZ, hC]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.project_laws (P : ProbZonotope n) (dims : Fin m → Fin n)
    (h : P.cov.PosSemidef) : -- --- CONCL ---
    (fun μ : Measure (EuclideanSpace ℝ (Fin n)) =>
        μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
          (toLp 2 (fun k => ofLp x (dims k)) : EuclideanSpace ℝ (Fin m)))) '' P.laws
      = (P.project dims).laws := by -- --- PROOF ---
  have hv : ∀ x : EuclideanSpace ℝ (Fin n),
      aux_selection dims *ᵥ ofLp x = fun k => ofLp x (dims k) := by
    intro x; funext i
    simp [aux_selection, Matrix.mulVec, dotProduct]
  rw [aux_project_eq_mtimes]
  simpa only [hv] using ProbZonotope.mtimes_laws (aux_selection dims) P h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
