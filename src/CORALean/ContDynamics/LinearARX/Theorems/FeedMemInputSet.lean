module

public import CORALean.ContDynamics.LinearARX.Operations.Basic
public import CORALean.ContDynamics.LinearARX.Operations.InputSet

@[expose] public section

/-!
# The input signal stays in the converted input set

Each lag's term is in its own `mtimes`, so the sum is in the `plus` of them; the
fold over the lags is an induction that carries the partial sum.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ExactScalar 𝕋] [∀ n, Plus (S n) (Vec ℝ n)] in
/-- A matrix times a point of `U` is in the `mtimes`. -/
theorem LinearARX.aux_mulVec_mem (M : Mat 𝕋 (p * dy) du) (U : S du) {v : Vec ℝ du}
    (hv : v ∈ construct U) : toRealMat M *ᵥ v ∈ construct (mtimes M U) :=
  mtimes_outer M U (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hv))

omit [ExactScalar 𝕋] in
/-- The fold adds each listed term to a partial sum that is already enclosed. -/
theorem LinearARX.aux_foldl_mem (M : Fin (p + 1) → Mat 𝕋 (p * dy) du) (U : S du)
    (w : Fin (p + 1) → Vec ℝ du) (hw : ∀ j, w j ∈ construct U) : -- --- CONCL ---
    ∀ (l : List (Fin p)) (acc : S (p * dy)) (a : Vec ℝ (p * dy)), a ∈ construct acc →
      a + (l.map fun j => toRealMat (M j.succ) *ᵥ w j.succ).sum ∈
        construct (l.foldl (fun acc j => plus acc (mtimes (M j.succ) U)) acc) := by -- --- PROOF ---
  intro l
  induction l with
  | nil => intro acc a ha; simpa using ha
  | cons j l ih =>
    intro acc a ha
    have h := ih (plus acc (mtimes (M j.succ) U)) (a + toRealMat (M j.succ) *ᵥ w j.succ)
      (plus_outer _ _ (Set.add_mem_add ha
        (LinearARX.aux_mulVec_mem _ U (hw j.succ))))
    simpa [add_assoc] using h


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.feed_mem_inputSet (sys : LinearARX 𝕋 dy du p) (U : S du) {u : ℕ → Vec ℝ du}
    (hu : ∀ k, u k ∈ construct U) (k : ℕ) :
    sys.feed u k ∈ construct (sys.inputSet U) := by
  unfold LinearARX.feed LinearARX.inputSet
  rw [Fin.sum_univ_succ, Fin.sum_univ_def]
  exact LinearARX.aux_foldl_mem sys.inputMat U (fun j => u (k + p - j)) (fun j => hu _)
    (List.finRange p) _ _ (LinearARX.aux_mulVec_mem _ U (hu _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
