module

public import CORALean.ContSet.Ellipsoid.Real.Operations.CartProdVec

@[expose] public section

/-!
# `Ellipsoid.cartProdVec` is the product with a point, exactly

`E.c + E.G u` with the point appended is the padded center plus the padded generators at `u`, as
the padding rows are zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.cartProdVec_exact (E : Ellipsoid n) (v : Vec ℝ m) :
    (E.cartProdVec v).construct =
      (fun x : Vec ℝ n => (Fin.append x v : Vec ℝ (n + m))) '' E.construct := by -- --- PROOF ---
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨E.c + E.G.mulVec u, ⟨u, hu, rfl⟩, ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp [Ellipsoid.cartProdVec, Matrix.mulVec, dotProduct]
    rfl
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u, hu, ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp [Ellipsoid.cartProdVec, Matrix.mulVec, dotProduct]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
