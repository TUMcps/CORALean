module

public import CORALean.ContDynamics.LinearSysDT.Operations.BackReachForall
public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetForallExact

@[expose] public section

/-!
# `backReachForall` is an inner approximation of the backward reachable set

The direction `MinkDiff` runs, propagated along a run: a backward reachable set
is a guarantee about every state in it, so an implementation may only ever
return a subset of it, and both hypotheses about the operations run inner too.
`hdiff` is `MinkDiff`'s own obligation at a partial difference, and `hinv` is
the half of an exact `mtimes` that `mtimes_outer` does not give — an enclosure
of the image would put states outside the preimage into the result, which is
exactly the unsound direction here.

`hA` is a *right* inverse, `A Ainv = 1`, which is all a step uses: what `Ainv`
maps into is carried back onto itself by `A`, and nothing asks what `Ainv` does
anywhere else. `Zonotope` supplies `hinv` and `hdiff` both — see
`BackReachForallInnerZonotope`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.backReachForall_inner (sys : LinearSysDT 𝕋 n) {Ainv : Mat 𝕋 n n}
    (hA : toRealMat sys.A * toRealMat Ainv = 1) {diff : S n → S n → Option (S n)}
    (hdiff : ∀ B V D, diff B V = some D →
      construct D ⊆ minkowskiDiff (construct B) (construct V))
    (hinv : ∀ s : S n, construct (mtimes Ainv s) ⊆ (toRealMat Ainv *ᵥ ·) '' construct s)
    (T U : S n) : -- --- CONCL ---
    ∀ (k : ℕ) (R : S n), sys.backReachForall ⟨T, U, 0, k⟩ ⟨Ainv, diff⟩ = some R →
      construct R ⊆ sys.backReachSetForallExact T U k := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro R hR; rw [← Option.some.inj hR]; exact subset_rfl
  | succ k ih =>
    intro R hR
    -- the step, taken apart: the set the run held, and the difference at it
    have hR' : (sys.backReachForall ⟨T, U, 0, k⟩ ⟨Ainv, diff⟩).bind
        (fun P => (diff P U).map (mtimes Ainv)) = some R := hR
    rw [Option.bind_eq_some_iff] at hR'
    obtain ⟨B, hB, hR'⟩ := hR'
    rw [Option.map_eq_some_iff] at hR'
    obtain ⟨D, hD, rfl⟩ := hR'
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hinv D hz
    show ∀ w ∈ construct U,
      toRealMat sys.A *ᵥ (toRealMat Ainv *ᵥ y) + w ∈ sys.backReachSetForallExact T U k
    -- one step forward undoes `Ainv`, and the difference pays for the input
    intro w hw
    have hAy : toRealMat sys.A *ᵥ (toRealMat Ainv *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
    rw [hAy]
    exact ih B hB (hdiff B U D hD hy w hw)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
