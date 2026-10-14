module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Augment
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Extended

@[expose] public section

/-!
# At a linear plant, the extended system is the augmented linear one

CORA's `aux_augmentLinear`, checked: `extended`'s field `(A x + B u + c, 0)` at `z = [x; u]` is
`[A B; 0 0] z + [c; 0]`, `augment`'s. This is what lets `LinearSys`'s own reachability reach a
control period of the closed loop.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.extended_f_eq_augment (sys : NeurNetContrSys (LinearSys 𝕋 n) S n)
    (z : Vec ℝ (n + sys.plant.m)) (w : Vec ℝ 0) :
    sys.extended.f z w = sys.augment.A *ᵥ z + sys.augment.c := by -- --- PROOF ---
  -- the plant's field, written out at the linear plant
  show Fin.append (toRealMat sys.plant.A *ᵥ (fun k => z (Fin.castAdd sys.plant.m k)) +
      (toRealMat sys.plant.B *ᵥ (fun k => z (Fin.natAdd n k)) + toRealVec sys.plant.c))
      (0 : Vec ℝ sys.plant.m) = _
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp [NeurNetContrSys.augment, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
