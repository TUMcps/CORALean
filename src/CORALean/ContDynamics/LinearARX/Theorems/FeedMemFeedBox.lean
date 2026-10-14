module

public import CORALean.ContDynamics.LinearARX.Operations.FeedBox
public import CORALean.ContDynamics.LinearARX.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The real input feed lies in the float feed box

`feed` of the real values of a float input signal lies in `feedBox`: each lag term is
a matrix times a point, enclosed by `mtimes`, and the fold adds them by `plus`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar Plus Mtimes ContSet CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix times the real value of a point is in the `mtimes` of its point box. -/
theorem LinearARX.aux_mulVec_mem_box (M : Mat 𝕋 (p * dy) du) (v : Vec 𝕋 du) :
    Scalar.toRealMat M *ᵥ Scalar.toRealVec v ∈
      construct (mtimes (S := ℐ𝒱[𝕋]) M (Interval.point v)) :=
  mtimes_outer (S := ℐ𝒱[𝕋]) M _
    (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (Interval.mem_point v)))

/-- The fold adds each listed term to a partial sum that is already enclosed. -/
theorem LinearARX.aux_foldl_mem_box (M : Fin (p + 1) → Mat 𝕋 (p * dy) du)
    (w : Fin (p + 1) → Vec 𝕋 du) :
    ∀ (l : List (Fin p)) (acc : Interval (Vec 𝕋 (p * dy))) (a : Vec ℝ (p * dy)),
      a ∈ construct acc →
      a + (l.map fun j => Scalar.toRealMat (M j.succ) *ᵥ Scalar.toRealVec (w j.succ)).sum ∈
        construct (l.foldl (fun acc j => plus (S := Interval (Vec 𝕋 (p * dy))) acc
          (mtimes (S := ℐ𝒱[𝕋]) (M j.succ) (Interval.point (w j.succ))))
          acc) := by -- --- PROOF ---
  intro l
  induction l with
  | nil => intro acc a ha; simpa using ha
  | cons j l ih =>
    intro acc a ha
    have h := ih _ (a + Scalar.toRealMat (M j.succ) *ᵥ Scalar.toRealVec (w j.succ))
      (plus_outer (S := Interval (Vec 𝕋 (p * dy))) _ _ (Set.add_mem_add ha
        (LinearARX.aux_mulVec_mem_box _ _)))
    simpa [add_assoc] using h


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.feed_mem_feedBox (sys : LinearARX 𝕋 dy du p) (u : ℕ → Vec 𝕋 du) (k : ℕ) :
    sys.feed (fun j => Scalar.toRealVec (u j)) k ∈ construct (sys.feedBox u k) := by
  unfold LinearARX.feed LinearARX.feedBox
  rw [Fin.sum_univ_succ, Fin.sum_univ_def]
  exact LinearARX.aux_foldl_mem_box sys.inputMat (fun j => u (k + p - j)) (List.finRange p) _ _
    (LinearARX.aux_mulVec_mem_box _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
