import CORALean.ContSet.Ellipsoid.Float.Operations.GeneratorError

/-!
# What a rounded generator costs an ellipsoid

The coefficient vector lies in the Euclidean unit ball rather than in a box, and
the box is what the error is charged at: `abs_le_norm₂` puts each `uⱼ` in
`[-1,1]`, and from there `abs_sum_le_radius` applies unchanged, so a rounded
ellipsoid generator costs exactly what a rounded zonotope generator costs.

The tighter answer is Cauchy–Schwarz — a row of the entrywise error reaches only
`‖Δᵢ‖₂` over the ball, not `‖Δᵢ‖₁` — and it is deliberately not taken: it is a
Euclidean norm, which is a square root, and the certificate that answers one for
the support function would have to be supplied here too, by an operation whose
whole job is to be small. Precision paid where the caller cannot see it is worse
than precision lost.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}

theorem Ellipsoid.mem_generatorError {G : Mat 𝕋 n k} {Δ : Mat ℝ n k} {u : Vec ℝ k}
    (hG : ∀ i j, |Δ i j| ≤ toReal (G i j)) (hu : ‖u‖₂ ≤ 1) :
    (fun i => ∑ j, Δ i j * u j) ∈ (Ellipsoid.generatorError G).construct := by
  intro i
  have key := abs_sum_le_radius (fun i j => le_trans (hG i j) (le_abs_self _))
    (fun j => le_trans (abs_le_norm₂ u j) hu) i
  refine ⟨?_, le_of_abs_le key⟩
  show toReal (neg (radius G i)) ≤ ∑ j, Δ i j * u j
  rw [toReal_neg]
  exact neg_le_of_abs_le key

end CORALean.Float
