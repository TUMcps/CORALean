module

public import CORALean.ContSet.Ellipsoid.Real.Operations.CartProdVec
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqOfFactor
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MulGMulTranspose

@[expose] public section

/-!
# `Ellipsoid.cartProdVec` is the product with a point, exactly

`blkdiag(Q, 0) = P Q Pᵀ` is factored by `P G`, `P = [I; 0]` the embedding
(`construct_eq_of_factor`), and `E.q + E.G u` with the point appended is the padded center plus
`P G u`, as the padding rows of `P` are zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.cartProdVec_exact (E : Ellipsoid n) (v : Vec ℝ m) :
    (E.cartProdVec v).construct =
      (fun x : Vec ℝ n => (Fin.append x v : Vec ℝ (n + m))) '' E.construct := by -- --- PROOF ---
  set P : Mat ℝ (n + m) n := Matrix.of fun i j => Fin.addCases (fun i => if i = j then 1 else 0)
    (fun _ => 0) i with hP
  have hQ : (E.cartProdVec v).Q = P * E.Q * Pᵀ := rfl
  rw [(E.cartProdVec v).construct_eq_of_factor (P * E.G)
    (by rw [hQ]; exact E.mul_G_mul_transpose P)]
  -- `P` pads with zeros
  have hPw : ∀ w : Vec ℝ n, P *ᵥ w = Fin.append w 0 := fun w => by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp [hP, Matrix.mulVec, dotProduct]
  have hq : (E.cartProdVec v).q = Fin.append E.q v := rfl
  have hval : ∀ u : Vec ℝ n, Fin.append E.q v + (P * E.G) *ᵥ u = Fin.append (E.q + E.G *ᵥ u) v :=
    fun u => by
      rw [← Matrix.mulVec_mulVec, hPw]
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨E.q + E.G *ᵥ u, ⟨u, hu, rfl⟩, by rw [hq, hval]⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [hq, hval]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
