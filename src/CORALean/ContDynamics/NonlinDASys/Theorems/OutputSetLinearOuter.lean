import CORALean.ContDynamics.NonlinDASys.Operations.OutputSetLinear
import CORALean.Global.JacobianMatAffine

/-!
# The linear output set holds the output of every state, algebraic variable and input

For an affine output `h(x, y, u) = c + M_x x + M_y y + M_u u`, the output of every `x ∈ R`,
`y ∈ R_y` and `u ∈ U` lies in `NonlinDASys.outputSetLinear`: the first-order expansion is exact,
and the term in `y`, absent from CORA's (`outputSetLinearCora_counterexample`), is what covers
the algebraic variables. An outer statement over the product `R × R_y × U`: the algebraic
variable is determined by `x` and `u`, so the true output set can be smaller.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n p m r : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinDASys.outputSetLinear_outer (h : Vec ℝ n → Vec ℝ p → Vec ℝ m → Vec ℝ r)
    (c : Vec ℝ r) (M_x : Mat ℝ r n) (M_y : Mat ℝ r p) (M_u : Mat ℝ r m)
    (hh : ∀ x y u, h x y u = c + M_x *ᵥ x + M_y *ᵥ y + M_u *ᵥ u)
    (p_x : Vec ℝ n) (p_y : Vec ℝ p) (p_u : Vec ℝ m) (R : S n) (R_y : S p) (U : S m)
    {x : Vec ℝ n} {y : Vec ℝ p} {u : Vec ℝ m} (hx : x ∈ construct R) (hy : y ∈ construct R_y)
    (hu : u ∈ construct U) :
    h x y u ∈ NonlinDASys.outputSetLinear h p_x p_y p_u R R_y U := by -- --- PROOF ---
  -- each partial map is affine, so its Jacobian is the matrix
  have hJx : jacobianMat (fun x => h x p_y p_u) p_x = M_x := by
    have := jacobianMat_affine (c + M_y *ᵥ p_y + M_u *ᵥ p_u) M_x p_x
    simpa [hh, add_assoc, add_comm, add_left_comm] using this
  have hJy : jacobianMat (fun y => h p_x y p_u) p_y = M_y := by
    have := jacobianMat_affine (c + M_x *ᵥ p_x + M_u *ᵥ p_u) M_y p_y
    simpa [hh, add_assoc, add_comm, add_left_comm] using this
  have hJu : jacobianMat (fun u => h p_x p_y u) p_u = M_u := by
    have := jacobianMat_affine (c + M_x *ᵥ p_x + M_y *ᵥ p_y) M_u p_u
    simpa [hh, add_assoc, add_comm, add_left_comm] using this
  refine ⟨x, hx, y, hy, u, hu, ?_⟩
  rw [hJx, hJy, hJu]
  simp only [hh, Matrix.mulVec_sub]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
