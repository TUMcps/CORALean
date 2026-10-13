import CORALean.ContDynamics.LinearSysDT.Operations.BackReachExists
import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetExists

/-!
# `backReachExists` encloses the backward reachable set

The ordinary outer direction, propagated along a run, and what it buys is the
contrapositive: a state *outside* the computed set is one no admissible input
signal drives into the target. Only `plus_outer` and `mtimes_outer` are used, so
this holds at every representation with `Plus` and `Mtimes` — no exactness, and
no inner half of anything.

`hA` is a *left* inverse, `Ainv A = 1`, where `backReachForall_inner` asks for a
right one: it is what turns the preimage under `A` into an image under `Ainv`
the outer way, since a state the step keeps is recovered from where it lands.
At a square matrix each inverse is the other, so a caller supplies the same
thing; the proofs do not.

`hneg` is the input set negated, an enclosure like every other hypothesis here.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar Plus Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.backReachExists_outer (sys : LinearSysDT 𝕋 n) {Ainv : Mat 𝕋 n n}
    (hA : toRealMat Ainv * toRealMat sys.A = 1) (T U negU : S n)
    (hneg : -construct U ⊆ construct negU) (k : ℕ) :
    sys.backReachSetExists T U k ⊆
      construct (sys.backReachExists ⟨T, negU, 0, k⟩ ⟨Ainv⟩) := by -- --- PROOF ---
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    rintro x ⟨u, hu, hx⟩
    -- the step's own state, with the chosen input paid back out of `negU`
    have hstep : toRealMat sys.A *ᵥ x ∈
        construct (plus (sys.backReachExists ⟨T, negU, 0, k⟩ ⟨Ainv⟩) negU) := by
      have hsplit : toRealMat sys.A *ᵥ x = (toRealMat sys.A *ᵥ x + u) + -u := by abel
      rw [hsplit]
      exact plus_outer _ _ (Set.add_mem_add (ih hx) (hneg (Set.neg_mem_neg.mpr hu)))
    -- the left inverse recovers `x` from it, so the preimage is inside the image
    have hback : toRealMat Ainv *ᵥ (toRealMat sys.A *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
    exact mtimes_outer Ainv _ (Set.mem_biUnion rfl ⟨_, hstep, hback⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
