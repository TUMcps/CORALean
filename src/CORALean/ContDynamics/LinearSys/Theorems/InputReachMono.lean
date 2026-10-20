module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparation

@[expose] public section

/-!
# The input reach set grows with time, once the origin is available

[1, Prop. 3.3], argued as it argues it. Split the longer window into the part
before the shorter one and the shorter one itself, which Prop. 3.2 says is
realizable; holding the first part at the zero input contributes nothing, so
whatever the shorter window can do the longer one can too.

`0 ∈ U` is exactly what makes the zero input admissible, and it is the whole
content of the hypothesis. This is what identifies the enclosure over a time
interval with the one at its end.

## Inputs
* `sys` – linear system
* `U` – input set
* `t` – first time
* `r` – second time

## Hypotheses
* `hbdd` – input set bounded
* `h0` – origin in the input set
* `ht0` – first time nonnegative
* `htr` – first time at most the second

## Conclusion
* the input reach grows with time

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Holding the input at the origin is admissible when `U` contains it, and
contributes nothing. -/
theorem LinearSys.aux_zero_mem_inputReach (sys : LinearSys 𝕋 n) {U : S n} (τ : ℝ)
    (h0 : (0 : Vec ℝ n) ∈ construct U) : (0 : Vec ℝ n) ∈ sys.inputReach U τ := by
  refine ⟨fun _ => 0, fun _ _ => h0, aestronglyMeasurable_const, ?_⟩
  simp

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in


-- =======================================  MAIN THEOREM  ======================================= --

/-- Althoff's Prop. 3.3: with the origin in the input set, a longer window
contributes at least everything a shorter one can. -/
theorem LinearSys.inputReach_mono (sys : LinearSys 𝕋 n) {U : S n} {t r : ℝ}
    (hbdd : Bornology.IsBounded (construct U)) (h0 : (0 : Vec ℝ n) ∈ construct U)
    (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- CONCL ---
    sys.inputReach U t ⊆ sys.inputReach U r := by -- --- PROOF ---
  intro y hy
  have hsep := sys.inputReach_separation (a := r - t) (b := t) (by linarith) ht0 hbdd
  rw [show r - t + t = r from by ring] at hsep
  have hmem := hsep (Set.add_mem_add
    (Set.mem_image_of_mem _ (sys.aux_zero_mem_inputReach (r - t) h0)) hy)
  simpa using hmem

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
