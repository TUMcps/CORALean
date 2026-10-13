import CORALean.ContDynamics.NonlinDASys.Operations.JointReachSet
import CORALean.ContDynamics.NonlinDASys.Theorems.AlgDeviationEq
import Mathlib.Algebra.BigOperators.Fin

/-!
# The joint reachable set holds every consistent state

[1, Prop. 2]: `R(τₖ)` encloses the differential and algebraic variables together. Every
`x ∈ Rᵈ(τₖ)`, `u ∈ U` and `ℓᵃ ∈ L̄ᵃ` with `0 = g(z*) + D Δx + E Δu + F Δy + ℓᵃ` — the
linearized constraint, `ℓᵃ` its error — gives `(x, y) ∈ R(τₖ)`, at the factors of `x`, `u`
and `ℓᵃ` side by side. By the printed proof: [1, Eq. 12] solves for `Δy`, and the zonotope
rules of [1, Eq. 5] do the rest. The second component is [1, Eq. 19]'s `Rᵃ(τₖ)`, so `y` lies
in that too. Only `F⁻¹ F = I` is used.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: `x ∈ Rᵈ(τₖ)`, `u ∈ U`, `ℓᵃ ∈ L̄ᵃ` and the linearized constraint give
`(x, y) ∈ R(τₖ)`. -/
theorem NonlinDASys.jointReachSet_outer {xs : Vec ℝ n} {ys : Vec ℝ p} {us : Vec ℝ m}
    {g₀ : Vec ℝ p} {D : Mat ℝ p n} {E : Mat ℝ p m} {F F_inv : Mat ℝ p p} (hF : F_inv * F = 1)
    {R_d : Zonotope (Vec ℝ n)} {U : Zonotope (Vec ℝ m)} {L_a : Zonotope (Vec ℝ p)}
    {x : Vec ℝ n} {y : Vec ℝ p} {u : Vec ℝ m} {ℓa : Vec ℝ p} (hx : x ∈ R_d.construct)
    (hu : u ∈ U.construct) (hl : ℓa ∈ L_a.construct)
    (hg : g₀ + D *ᵥ (x - xs) + E *ᵥ (u - us) + F *ᵥ (y - ys) + ℓa = 0) :
    (x, y) ∈
      (NonlinDASys.jointReachSet xs ys us g₀ D E F_inv R_d U L_a).construct := by -- --- PROOF ---
  obtain ⟨βd, hβd, rfl⟩ := hx
  obtain ⟨βu, hβu, rfl⟩ := hu
  obtain ⟨βl, hβl, rfl⟩ := hl
  -- [1, Eq. 12]: the algebraic deviation
  have hΔy := NonlinDASys.alg_deviation_eq hF hg
  refine ⟨Fin.append (Fin.append βd βu) βl, Fin.addCases (Fin.addCases
      (fun j => by simpa using hβd j) (fun j => by simpa using hβu j))
    (fun j => by simpa using hβl j), ?_⟩
  change _ = _ + ∑ j : Fin (R_d.h + U.h + L_a.h), _
  simp only [NonlinDASys.jointReachSet, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  refine Prod.ext ?_ ?_
  -- the differential part: only the `G_d` block reaches it
  · simp [Prod.fst_sum]
  -- the algebraic part: `y = y* + Δy`, each factor carried through `-F⁻¹`
  · rw [show y = ys + (y - ys) by abel, hΔy]
    simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, Matrix.mulVec_add, Matrix.mulVec_sum,
      Matrix.mulVec_smul, Matrix.mulVec_sub, smul_neg,
      Finset.sum_neg_distrib, ← Matrix.mulVec_mulVec]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
