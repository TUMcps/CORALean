module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.PRadiusPredictStripsLe
public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.QuadFormLeOfLmiChain

@[expose] public section

/-!
# The P-radius gains of `Alg. 2`

[1, Alg. 2], step `j`: the strips of outputs `0, …, j - 1` are met one after another at the gains
`λₛ`, the first `j - 1` of them from the earlier steps and the last the one being designed. If
the matrix inequality of step `j` holds at every vertex of `[A]`, the estimate satisfies
`L_k ≤ β L_{k-1} + ψ + φ₀² + … + φ_{j-1}²` at every `A` in their hull: the quadratic form of
`quadForm_le_of_lmi_chain` spent in `Zonotope.pRadius_predict_strips_le`. At `j = 1` it is
[1, Eq. 9] with [1, Eq. 4]. The program's objective, `max τ`, picks among the gains the
inequality admits and is not a claim; any feasible gain is sound.

## Inputs
* `G` – vertex matrices
* `F` – disturbance matrix
* `C` – output matrix
* `φ` – strip widths
* `y` – measurements
* `Λ` – gain columns
* `κ` – strip update matrices
* `u` – gain direction vectors
* `φ'` – strip widths per step
* `β` – contraction factor
* `P` – radius matrix
* `A` – state matrix member
* `L` – bound on the previous radius
* `ψ` – bound on the disturbance term
* `X` – previous zonotope

## Hypotheses
* `hκ` – update matrices built from the gains
* `hu` – direction vectors built from gains and widths
* `hφ` – widths per step copy the strip widths
* `hP` – radius matrix positive definite
* `hβ` – contraction factor nonnegative
* `hLMI` – matrix inequality holds at every vertex
* `hA` – `A` lies in the hull of the vertices
* `hL` – previous radius bounded by `L`
* `hψ` – disturbance term bounded by `ψ`

## Conclusion
* the P-radius after the strips is at most the stated bound

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix
open scoped CORALean.Real

variable {n m p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: a feasible step `p` bounds the P-radius after `p` strips. -/
theorem LinearSysDT.pRadius_le_of_lmi_chain (G : Fin q → Mat ℝ n n) (F : Mat ℝ n m)
    (C : Mat ℝ p n) (φ y : Vec ℝ p) (Λ : Mat ℝ n p) (κ : ℕ → Mat ℝ n n) (u : ℕ → Vec ℝ n)
    (φ' : ℕ → ℝ) (hκ : ∀ s : Fin p, κ s = 1 - vecMulVec (fun r => Λ r s) (C s))
    (hu : ∀ s : Fin p, u s = φ s • fun r => Λ r s) (hφ : ∀ s : Fin p, φ' s = φ s)
    (β : ℝ) (P : Mat ℝ n n) (hP : P.PosDef) (hβ : 0 ≤ β)
    (hLMI : ∀ i,
      let Ξ : Matrix (Fin n ⊕ (Fin m ⊕ Fin p)) (Fin n) ℝ :=
        fromRows ((Conform.prodJac κ p p * G i)ᵀ * P)
          (fromRows ((Conform.prodJac κ p p * F)ᵀ * P)
            (Matrix.of fun s c => (Conform.prodJac κ p (p - s - 1) *ᵥ u s) ⬝ᵥ fun r => P r c))
      (fromBlocks (fromBlocks (β • P) 0 0
        (fromBlocks (Fᵀ * F) 0 0 (diagonal fun s : Fin p => φ' s ^ 2))) Ξ Ξᵀ P).PosSemidef)
    (A : Mat ℝ n n) (hA : A ∈ convexHull ℝ (Set.range G)) (L ψ : ℝ)
    (X : Real.Zonotope (Vec ℝ n))
    (hL : ∀ z ∈ X.construct, (z - X.c) ⬝ᵥ (P *ᵥ (z - X.c)) ≤ L)
    (hψ : ∀ γ : Vec ℝ m, (∀ j, |γ j| ≤ 1) → (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) ≤ ψ) : -- --- CONCL ---
    Real.Zonotope.pRadius P
        (ContSet.intersectStripSeq (S := 𝒵) C φ y (fun _ => Λ)
          ((X.mtimes A).plus (⟨m, 0, fun j i => F i j⟩ : Real.Zonotope (Vec ℝ n))))
      ≤ β * L + ψ + ∑ s : Fin p, φ s ^ 2 := by -- --- PROOF ---
  refine Real.Zonotope.pRadius_predict_strips_le A P F C φ y Λ κ u hκ hu β L ψ X ?_ hβ hL hψ
  intro θ γ η
  -- the quadratic form of the matrix inequality, with `φ'` read off as `φ`
  have h := LinearSysDT.quadForm_le_of_lmi_chain p G F κ u φ' β P hP hLMI A hA θ γ η
  simpa only [hφ] using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
