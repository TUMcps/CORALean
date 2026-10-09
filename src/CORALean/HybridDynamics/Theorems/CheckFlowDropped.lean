import CORALean.HybridDynamics.Definitions.CheckFlow

/-!
# A reach set `Location.checkFlow` drops has no outward flow on its projection

If `R` is dropped, the supremum `flowUp` of the flow component along the outward normal `c` is
not positive. Every state `x` of `R`, projected onto the hyperplane, and every input `u` of the
location then have `c·(A (x - (c·x - d) c) + u) ≤ 0`: the flow nowhere points out of the
invariant through the projection. This is a statement about the projection, not about `R`
itself, and it says nothing about states that left the invariant by another face.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, ContSet (G n) (Vec ℝ n)] in
/-- A dropped set carries the flow nowhere outward on its projection. -/
theorem Location.checkFlow_dropped (ℓ : Location (fun n => Real.Zonotope (Vec ℝ n)) G L ℝ n)
    (c : Vec ℝ n) (d : ℝ) (Rs : List (Real.Zonotope (Vec ℝ n)))
    {R : Real.Zonotope (Vec ℝ n)} (hR : R ∈ Rs) (hdrop : R ∉ ℓ.checkFlow c d Rs)
    {x u : Vec ℝ n} (hx : x ∈ R.construct) (hu : u ∈ ContSet.construct ℓ.U) :
    c ⬝ᵥ (toRealMat ℓ.dynamics.A *ᵥ (x - (c ⬝ᵥ x - d) • c) + u) ≤ 0 := by -- --- PROOF ---
  -- dropped means the supremum is not positive
  have hle : ℓ.flowUp c d R ≤ 0 := by
    by_contra hpos
    exact hdrop (by
      unfold Location.checkFlow
      rw [List.mem_filter]
      exact ⟨hR, by simpa using not_le.mp hpos⟩)
  -- the two support bounds
  have h1 := (R.supportBound (Real.HPolytope.rowLin
    (fun _ : Fin 1 => (1 - vecMulVec c c)ᵀ *ᵥ ((toRealMat ℓ.dynamics.A)ᵀ *ᵥ c)) 0)).le x hx
  have h2 := ((ℓ.U).supportBound (Real.HPolytope.rowLin (fun _ : Fin 1 => c) 0)).le u hu
  unfold Location.flowUp at hle
  -- the projected state is `P x + d c`, and the flow component splits over it
  have hproj : x - (c ⬝ᵥ x - d) • c = (1 - vecMulVec c c) *ᵥ x + d • c := by
    funext i
    simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, vecMulVec, Finset.mul_sum, sub_smul,
      mul_comm, mul_left_comm]
    ring
  have hsplit : c ⬝ᵥ (toRealMat ℓ.dynamics.A *ᵥ (x - (c ⬝ᵥ x - d) • c) + u) =
      ((1 - vecMulVec c c)ᵀ *ᵥ ((toRealMat ℓ.dynamics.A)ᵀ *ᵥ c)) ⬝ᵥ x
        + c ⬝ᵥ (toRealMat ℓ.dynamics.A *ᵥ (d • c)) + c ⬝ᵥ u := by
    rw [hproj, Matrix.mulVec_add, dotProduct_add, dotProduct_add, Matrix.mulVec_transpose,
      Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec]
  rw [hsplit]
  have h1' : ((1 - vecMulVec c c)ᵀ *ᵥ ((toRealMat ℓ.dynamics.A)ᵀ *ᵥ c)) ⬝ᵥ x ≤ _ := h1
  have h2' : c ⬝ᵥ u ≤ _ := h2
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
