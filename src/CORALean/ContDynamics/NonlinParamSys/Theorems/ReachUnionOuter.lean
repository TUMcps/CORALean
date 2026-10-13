import CORALean.ContDynamics.NonlinParamSys.Definitions.ReachUnionExact
import CORALean.ContDynamics.NonlinParamSys.Operations.ReachUnion
import CORALean.ContDynamics.NonlinParamSys.Theorems.ConstTrajectoryToAugment
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachUnionOuter

/-!
# A union `reachUnion` returns contains every constant-parameter state reached

The reduction, spent in three steps. A constant-parameter run from `X₀` read
with its parameter appended is a run of `augment` from `X₀ × P`,
`ConstTrajectory.toAugment`, once `plus_outer` and `mtimes_outer` put every
pair `(x₀, p)` into the product computed; `aug_sys` makes that a run of the
bundled augmented system, whose union encloses it at every time of the horizon,
`NonlinearSys.WithSteps.reachUnion_outer`, with no confinement assumed; the
selection matrix, through `mtimes_outer`, carries the member holding the pair
to the one holding its first half, which is the state.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m q n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.WithSteps.reachUnion_outer (sys : NonlinParamSys.WithSteps S Rg m q n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachOptions ℝ) :
    match sys.reachUnion params options with
    | some R => sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
        ⊆ construct R
    | none => True := by -- --- PROOF ---
  cases hR : sys.reachUnion params options with
  | none => trivial
  | some R =>
    intro y hy
    simp only [NonlinParamSys.WithSteps.reachUnion, Option.map_eq_some_iff] at hR
    obtain ⟨Ra, hRa, rfl⟩ := hR
    set Z₀ : S (n + q) :=
      Mtimes.mtimes (𝕄 := Mat ℝ) (LinearMap.toMatrix' (blockPadLeft n q)) params.X₀ ⊞
      Mtimes.mtimes (𝕄 := Mat ℝ) (LinearMap.toMatrix' (blockPadRight n q)) sys.P
    -- every pair `(x₀, p)` lies in the product computed, `(x₀, 0) + (0, p)`
    have hZ : ∀ v ∈ construct params.X₀, ∀ w ∈ construct sys.P, Fin.append v w ∈ construct Z₀ := by
      intro v hv w hw
      have hE := Mtimes.mtimes_outer (𝕄 := Mat ℝ) (LinearMap.toMatrix' (blockPadLeft n q)) params.X₀
        (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hv))
      have hF := Mtimes.mtimes_outer (𝕄 := Mat ℝ) (LinearMap.toMatrix' (blockPadRight n q)) sys.P
        (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hw))
      refine Plus.plus_outer _ _ ⟨_, hE, _, hF, ?_⟩
      simp only [Scalar.toRealMat_real, LinearMap.toMatrix'_mulVec]
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [blockPadLeft, blockPadRight]
    -- the run, its parameter appended, is one of the augmented system from `Z₀`
    simp only [NonlinParamSys.WithSteps.reachUnionExact, Set.mem_iUnion, Set.mem_setOf_eq] at hy
    obtain ⟨t, ht, x, u, c, traj, rfl⟩ := hy
    have hz : Fin.append (x t) c ∈ construct Ra := by
      have haug := sys.aug.reachUnion_outer ⟨Z₀, params.tStart, params.tFinal⟩ options
      rw [hRa] at haug
      refine haug ?_
      simp only [NonlinearSys.WithSteps.reachUnionExact, Set.mem_iUnion]
      refine ⟨t, ht, fun s => Fin.append (x s) c, u, ?_, rfl⟩
      rw [sys.aug_sys]
      exact traj.toAugment (Z₀ := construct Z₀) fun v hv w hw => hZ v hv w hw
    -- the member holding `(x t, c)` maps to the projected one holding `x t`
    obtain ⟨s, hs, hzs⟩ := SetUnion.mem_construct.mp hz
    refine SetUnion.mem_construct.mpr ⟨_, List.mem_map_of_mem hs, ?_⟩
    have hPr := Mtimes.mtimes_outer (𝕄 := Mat ℝ) (LinearMap.toMatrix' (blockLeft n q)) s
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hzs))
    rwa [Scalar.toRealMat_real, LinearMap.toMatrix'_mulVec, blockLeft_append] at hPr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
