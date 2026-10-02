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
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The selection matrix reads `y(k)` off the window. -/
theorem NonlinearARX.aux_outputSel_mulVec (sys : NonlinearARX dy du p) (hp : 0 < p)
    (y : ℕ → Vec ℝ dy) (k : ℕ) :
    sys.outputSel *ᵥ NonlinearARX.stack p y k = y k := by -- --- PROOF ---
  funext r
  simp only [Matrix.mulVec, dotProduct]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single (⟨0, hp⟩ : Fin p)]
  · rw [Finset.sum_eq_single r]
    · simp only [NonlinearARX.outputSel, Matrix.of_apply, Equiv.symm_apply_apply, and_self,
        if_true, one_mul, NonlinearARX.stack, Nat.add_zero]
    · intro b _ hb
      simp only [NonlinearARX.outputSel, Matrix.of_apply, Equiv.symm_apply_apply, true_and,
        if_neg hb, zero_mul]
    · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    have : ¬ a.val = 0 := fun h => ha (Fin.ext h)
    simp only [NonlinearARX.outputSel, Matrix.of_apply, Equiv.symm_apply_apply, this,
      false_and, if_false, zero_mul]
  · simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.output_outer (sys : NonlinearARX dy du p) (hp : 0 < p) {o : ℕ}
    (ho : 0 < o) {Y₀ : S (p * dy)} {U : S du} {V : S ((p + 1) * du)}
    (hV : ∀ v : Vec ℝ ((p + 1) * du),
      (∀ a : Fin (p + 1), (fun b => v (finProdFinEquiv (a, b))) ∈ construct U) →
        v ∈ construct V)
    (steps : ℕ → sys.toNonlinearSysDT.LinStep V)
    {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du} (traj : sys.Trajectory Y₀ U y u)
    (hR : ∀ k, NonlinearARX.stack p y k ∈ (steps k).R) (k : ℕ) :
    y k ∈ construct (mtimes (𝕄 := Mat ℝ) sys.outputSel
      (sys.toNonlinearSysDT.reach ⟨Y₀, V, 0, k⟩ ⟨o, ho⟩ steps)) := by
  rw [← sys.aux_outputSel_mulVec hp y k]
  exact Mtimes.mtimes_outer (𝕄 := Mat ℝ) sys.outputSel _
    (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (sys.reach_outer ho hV steps traj hR k)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
