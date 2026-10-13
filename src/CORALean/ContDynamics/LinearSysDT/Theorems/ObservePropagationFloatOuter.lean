import CORALean.ContDynamics.LinearSysDT.Operations.ObservePropagationFloat
import CORALean.ContDynamics.LinearSysDT.Theorems.ErrMatFloatMem
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter

/-!
# The float propagation observer holds the true state

[1, Eq. 6] over time: every run `x_{k+1} = A x_k + u_k + ω_k` from `x_0 ∈ R₀`, with `ω_k ∈ W` and
measurements `y_k = C x_k + v_k`, `v_k ∈ V`, is in the observer's set at every step, whatever the
gain and the order. All quantities are the real values of stored floats; an outer statement.

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observePropagationFloat_outer (sys : LinearSysDT 𝕋 n) (C : Mat 𝕋 p n)
    (gain : Zonotope (Vec 𝕋 n) → Mat 𝕋 n p) (order : ℕ) (W R₀ : Zonotope (Vec 𝕋 n))
    (V : Zonotope (Vec 𝕋 p)) (u : ℕ → Vec 𝕋 n) (y : ℕ → Vec 𝕋 p) (x w : ℕ → Vec ℝ n)
    (v : ℕ → Vec ℝ p) (h0 : x 0 ∈ R₀.construct) (hw : ∀ k, w k ∈ W.construct)
    (hv : ∀ k, v k ∈ V.construct)
    (hstep : ∀ k, x (k + 1) = toRealMat sys.A *ᵥ x k + toRealVec (u k) + w k)
    (hy : ∀ k, toRealVec (y k) = toRealMat C *ᵥ x k + v k) (k : ℕ) :
    x k ∈ (sys.observePropagationFloat C gain order W R₀ V u y k).construct := by -- --- PROOF ---
  induction k with
  | zero => exact h0
  | succ k ih =>
    set S := sys.observePropagationFloat C gain order W R₀ V u y k
    set L := gain S
    -- the true state, one point of each summand of (6)
    have heq : x (k + 1) = (toRealMat sys.A - toRealMat L * toRealMat C) *ᵥ x k +
        toRealVec (u k) + toRealMat L *ᵥ toRealVec (y k) + toRealMat (fun i j => neg (L i j)) *ᵥ v k
        + w k := by
      have hneg : toRealMat (fun i j => neg (L i j)) = -toRealMat L := by
        funext i j
        simp [toRealMat, toReal_neg]
      rw [hstep, hy k, hneg, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
        Matrix.neg_mulVec]
      abel
    -- (A - L C) x_k is in the first summand, the matrix being in the interval matrix
    have h1 : (toRealMat sys.A - toRealMat L * toRealMat C) *ᵥ x k ∈
        (Zonotope.mtimesIntervalMat (LinearSysDT.errMatFloat sys.A L C) S).construct :=
      Zonotope.mtimesIntervalMat_outer _ S
        (Set.mem_iUnion₂.mpr ⟨_, LinearSysDT.errMatFloat_mem sys.A L C, ⟨x k, ih, rfl⟩⟩)
    -- the input is a point
    have h2 : toRealVec (u k) ∈ (Zonotope.point (u k)).construct := by
      rw [Zonotope.construct_point]
      exact rfl
    -- `L y_k` is the gain applied to the point `y_k`
    have h3 : toRealMat L *ᵥ toRealVec (y k) ∈
        (Zonotope.mtimes L (Zonotope.point (y k))).construct := by
      refine Zonotope.mtimes_outer L _ ⟨toRealVec (y k), ?_, rfl⟩
      rw [Zonotope.construct_point]
      exact rfl
    -- `(-L) v_k` is in the product of `-L` with `V`
    have h4 : toRealMat (fun i j => neg (L i j)) *ᵥ v k ∈
        (Zonotope.mtimes (fun i j => neg (L i j)) V).construct :=
      Zonotope.mtimes_outer _ V ⟨v k, hv k, rfl⟩
    -- the sum of the five points is in the sum of the five sets, then reduced
    show x (k + 1) ∈ (Zonotope.reduce (((((Zonotope.mtimesIntervalMat
      (LinearSysDT.errMatFloat sys.A L C) S).plus (Zonotope.point (u k))).plus
      (Zonotope.mtimes L (Zonotope.point (y k)))).plus
      (Zonotope.mtimes (fun i j => neg (L i j)) V)).plus W) order).construct
    refine Zonotope.reduce_outer _ _ ?_
    rw [heq]
    exact Zonotope.plus_outer _ _ ⟨_, Zonotope.plus_outer _ _ ⟨_, Zonotope.plus_outer _ _
      ⟨_, Zonotope.plus_outer _ _ ⟨_, h1, _, h2, rfl⟩, _, h3, rfl⟩, _, h4, rfl⟩, _, hw k, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
