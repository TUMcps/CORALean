import CORALean.ContDynamics.LinearSys.Theorems.ReachSetEq
import CORALean.Global.LinProg.Composition

/-!
# A lower bound on the reachable set — the dual of the upper one

[1, Alg. 1 (lower bounds)]'s line 15, over `reachSet`: `ρ(R₀, ℓᵀe^{tA}) + ρ(P, ℓ)` again,
now with a point in each set attaining at least it, assembled by
`SupportWitness.image` and `.add` and carried across `reachSet_eq`. The
first lower bound in the tree on a continuous-time reachable set: every
enclosure elsewhere runs `⊆`, which only a witness — a point genuinely in the
set — can turn into a lower bound, and only the equality supplies one.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A witness for `R₀` and for `sys.inputReach U t`, in every direction, give a
witness for the time-point reachable set at `t` — no set built, and
`reachSet` named only in the conclusion. -/
noncomputable def LinearSys.timePointWitness (sys : LinearSys 𝕋 n) (R₀ U : S n)
    {t : ℝ} (ht : 0 ≤ t) (hU : Bornology.IsBounded (construct U))
    (w₀ : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportWitness (construct R₀) d)
    (wP : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportWitness (sys.inputReach U t) d)
    (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportWitness (sys.reachSet (Set.Icc 0 t) R₀ U t) c :=
  sys.reachSet_eq R₀ U ht hU ▸
    (SupportWitness.image (mulVecLin (exp (t • toRealMat sys.A)))
      (w₀ (c.comp (mulVecLin (exp (t • toRealMat sys.A)))))).add (wP c)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
