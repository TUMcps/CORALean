import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparation

/-!
# The input reach set grows with time, once the origin is available

Althoff's Prop. 3.3, argued as the thesis argues it. Split the longer window
into the part before the shorter one and the shorter one itself, which Prop. 3.2
says is realizable; holding the first part at the zero input contributes nothing,
so whatever the shorter window can do the longer one can too.

`0 ∈ U` is exactly what makes the zero input admissible, and it is the whole
content of the hypothesis. This is what identifies the enclosure over a time
interval with the one at its end.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, OuterContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, OuterContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
/-- Holding the input at the origin is admissible when `U` contains it, and
contributes nothing. -/
theorem LinearSys.zero_mem_inputReach (sys : LinearSys 𝕋 n) {U : S n} (τ : ℝ)
    (h0 : (0 : Vec ℝ n) ∈ construct U) : (0 : Vec ℝ n) ∈ sys.inputReach U τ := by
  refine ⟨fun _ => 0, fun _ _ => h0, aestronglyMeasurable_const, ?_⟩
  simp

omit [∀ n, OuterContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
/-- Althoff's Prop. 3.3: with the origin in the input set, a longer window
contributes at least everything a shorter one can. -/
theorem LinearSys.inputReach_mono (sys : LinearSys 𝕋 n) {U : S n} {t r : ℝ}
    (hbdd : Bornology.IsBounded (construct U)) (h0 : (0 : Vec ℝ n) ∈ construct U)
    (ht0 : 0 ≤ t) (htr : t ≤ r) :
    sys.inputReach U t ⊆ sys.inputReach U r := by
  intro y hy
  have hsep := sys.inputReach_separation (a := r - t) (b := t) (by linarith) ht0 hbdd
  rw [show r - t + t = r from by ring] at hsep
  have hmem := hsep (Set.add_mem_add
    (Set.mem_image_of_mem _ (sys.zero_mem_inputReach (r - t) h0)) hy)
  simpa using hmem

end CORALean.Real
