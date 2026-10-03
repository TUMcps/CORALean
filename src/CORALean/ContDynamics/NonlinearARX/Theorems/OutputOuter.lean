import CORALean.ContDynamics.NonlinearARX.Theorems.ReachOuter

/-!
# The ARX output lies in the output set of the converted reach

`y(k)` is block `0` of the window at step `k`, which `outputSel` selects, so the
`mtimes` of `outputSel` with the converted reach encloses it. `0 < p`: at `p = 0`
the window is empty and says nothing about `y`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The selection matrix reads `y(k)` off the window. -/
theorem NonlinearARX.aux_outputSel_mulVec (sys : NonlinearARX dy du p) (hp : 0 < p)
    (y : ℕ → Vec ℝ dy) (k : ℕ) :
    toRealMat (sys.outputSel (𝕋 := 𝕋)) *ᵥ NonlinearARX.stack p y k = y k := by -- --- PROOF ---
  -- the selection matrix reads as the real 0/1 selection
  have hsel : toRealMat (sys.outputSel (𝕋 := 𝕋)) =
      Matrix.of fun (r : Fin dy) (c : Fin (p * dy)) =>
        if (finProdFinEquiv.symm c).1.val = 0 ∧ (finProdFinEquiv.symm c).2 = r then (1 : ℝ)
        else 0 := by
    funext r c
    rw [Scalar.toRealMat_apply]
    simp only [NonlinearARX.outputSel, Matrix.of_apply]
    split_ifs
    · exact CORALean.Float.SoundFloatArithmetic.toReal_one
    · exact CORALean.Float.SoundFloatArithmetic.toReal_zero
  rw [hsel]
  -- one row: only the entry `(0, r)` of the window survives the sum
  funext r
  simp only [Matrix.mulVec, dotProduct]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single (⟨0, hp⟩ : Fin p)]
  · rw [Finset.sum_eq_single r]
    · simp only [Matrix.of_apply, Equiv.symm_apply_apply, and_self,
        if_true, one_mul, NonlinearARX.stack, Nat.add_zero]
    · intro b _ hb
      simp only [Matrix.of_apply, Equiv.symm_apply_apply, true_and,
        if_neg hb, zero_mul]
    · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    have : ¬ a.val = 0 := fun h => ha (Fin.ext h)
    simp only [Matrix.of_apply, Equiv.symm_apply_apply, this,
      false_and, if_false, zero_mul]
  · simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.output_outer (sys : NonlinearARX dy du p) (hp : 0 < p) {o : ℕ}
    (ho : 0 < o) {Y₀ : S (p * dy)} {U : S du} {V : S ((p + 1) * du)}
    (hV : ∀ v : Vec ℝ ((p + 1) * du),
      (∀ a : Fin (p + 1), (fun b => v (finProdFinEquiv (a, b))) ∈ construct U) →
        v ∈ construct V)
    (steps : ℕ → sys.toNonlinearSysDT.LinStep 𝕋 V)
    {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du} (traj : sys.Trajectory Y₀ U y u)
    (hR : ∀ k, NonlinearARX.stack p y k ∈ (steps k).R) (k : ℕ) :
    y k ∈ construct (mtimes (𝕄 := Mat 𝕋) (sys.outputSel (𝕋 := 𝕋))
      (sys.toNonlinearSysDT.reach ⟨Y₀, V, 0, k⟩ ⟨o, ho⟩ steps)) := by
  rw [← sys.aux_outputSel_mulVec (𝕋 := 𝕋) hp y k]
  exact Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (sys.outputSel (𝕋 := 𝕋)) _
    (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (sys.reach_outer ho hV steps traj hR k)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
