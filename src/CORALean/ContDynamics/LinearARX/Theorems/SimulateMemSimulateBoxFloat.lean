module

public import CORALean.ContDynamics.LinearARX.Operations.SimulateBoxFloat
public import CORALean.ContDynamics.LinearARX.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContDynamics.LinearARX.Theorems.StackSimulateZero
public import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTStep
public import CORALean.ContDynamics.LinearSysDT.Theorems.MemSimulateBoxIn

@[expose] public section

/-!
# The real ARX run lies in the float boxes

The window `stack` of `simulate` from the real value of a float start window under
the real values of a float input signal lies, at every step, in `simulateBox`
computed in float arithmetic: the float `simulate` row's guarantee (ruling R-SIM).
An enclosure, so the box is outer.

## Inputs
* `sys` – ARX system
* `y₀` – float start window
* `u` – float input signal
* `k` – step

## Hypotheses
* none

## Conclusion
* the real run's window lies in the float box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar ContSet CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Plus Mtimes

/-- A matrix times the real value of a point is in the `mtimes` of its point box. -/
private theorem LinearARX.aux_mulVec_mem_box (M : Mat 𝕋 (p * dy) du) (v : Vec 𝕋 du) :
    Scalar.toRealMat M *ᵥ Scalar.toRealVec v ∈
      construct (mtimes (S := ℐ𝒱[𝕋]) M (Interval.point v)) :=
  mtimes_outer (S := ℐ𝒱[𝕋]) M _
    (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (Interval.mem_point v)))


/-- The fold adds each listed term to a partial sum that is already enclosed. -/
private theorem LinearARX.aux_foldl_mem_box (M : Fin (p + 1) → Mat 𝕋 (p * dy) du)
    (w : Fin (p + 1) → Vec 𝕋 du) : -- --- CONCL ---
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


/-- The real input feed lies in the float feed box. -/
private theorem LinearARX.aux_feed_mem_feedBox (sys : LinearARX 𝕋 dy du p) (u : ℕ → Vec 𝕋 du)
    (k : ℕ) :
    sys.feed (fun j => Scalar.toRealVec (u j)) k ∈ construct (sys.aux_feedBox u k) := by
  unfold LinearARX.feed LinearARX.aux_feedBox
  rw [Fin.sum_univ_succ, Fin.sum_univ_def]
  exact LinearARX.aux_foldl_mem_box sys.inputMat (fun j => u (k + p - j)) (List.finRange p) _ _
    (LinearARX.aux_mulVec_mem_box _ _)

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.simulate_mem_simulateBox (sys : LinearARX 𝕋 dy du p) (y₀ : Vec 𝕋 (p * dy))
    (u : ℕ → Vec 𝕋 du) (k : ℕ) : -- --- CONCL ---
    LinearARX.stack p (sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j)) k ∈
      construct (sys.simulateBox y₀ u k) := by -- --- PROOF ---
  -- the ARX recursion for `k ≥ p` is `simulate`'s definition
  have hrec : ∀ k, p ≤ k →
      sys.simulate (Scalar.toRealVec y₀) (fun j => Scalar.toRealVec (u j)) k
        = ∑ i : Fin p, Scalar.toRealMat (sys.Abar i) *ᵥ
              sys.simulate (Scalar.toRealVec y₀) (fun j => Scalar.toRealVec (u j)) (k - (i + 1))
          + ∑ j : Fin (p + 1), Scalar.toRealMat (sys.Bbar j) *ᵥ Scalar.toRealVec (u (k - j)) :=
    fun k hk => by rw [LinearARX.simulate, dif_neg (not_lt.mpr hk)]
  -- the first window is the start window
  have h0 : LinearARX.stack p
      (sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j)) 0 ∈
        construct (Interval.point y₀) := by
    rw [LinearARX.stack_simulate_zero]
    exact Interval.mem_point y₀
  -- so the stacked windows take the converted system's step
  have hstep : ∀ k, LinearARX.stack p
        (sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j)) (k + 1)
      = Scalar.toRealMat sys.toLinearSysDT.A *ᵥ LinearARX.stack p
          (sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j)) k
        + sys.feed (fun j => Scalar.toRealVec (u j)) k :=
    fun k => sys.toLinearSysDT_step
      (y := sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j))
      (u := fun j => Scalar.toRealVec (u j)) hrec k
  -- the feed lies in the feed box; then the generic box induction
  have hu := fun k => sys.aux_feed_mem_feedBox u k
  exact sys.toLinearSysDT.mem_simulateBoxIn (Interval.point y₀) (sys.aux_feedBox u) h0 hu hstep k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
