module

public import CORALean.NN.Operations.SmoothNetworkOutputFn

@[expose] public section

/-!
# `f(x, 0)` is the network's evaluation

CORA's own comment on `nonlinearSysDT`: `func(x,0)` is equal to `evaluate(net, x)`. With the
input at zero every bias is untouched. True of CORA's code only if the scale of an elementwise
affine layer is kept, which its conversion drops; see
`SmoothNetwork.elementwiseAffine_cora_counterexample`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SmoothNetwork.outputFn_zero : -- --- STMT ---
    ∀ {n k : ℕ} (N : SmoothNetwork n k) (x : Vec ℝ n),
    N.outputFn x 0 = N.eval x
  | _, _, .output, _ => rfl
  | _, _, .linear (m := m) W b rest, x => by
      have h : (fun i : Fin m => (0 : Vec ℝ (m + rest.nu)) (Fin.castAdd rest.nu i)) = 0 := rfl
      have h' : (fun j : Fin rest.nu => (0 : Vec ℝ (m + rest.nu)) (Fin.natAdd m j)) = 0 := rfl
      show rest.outputFn
        (W *ᵥ x + b + fun i : Fin m => (0 : Vec ℝ (m + rest.nu)) (Fin.castAdd rest.nu i))
        (fun j : Fin rest.nu => (0 : Vec ℝ (m + rest.nu)) (Fin.natAdd m j)) = rest.eval (W *ᵥ x + b)
      rw [h, h', add_zero]
      exact SmoothNetwork.outputFn_zero rest _
  | _, _, .elementwiseAffine _ _ rest, x => SmoothNetwork.outputFn_zero rest _
  | _, _, .tanh rest, x => SmoothNetwork.outputFn_zero rest _
  | _, _, .relu rest, x => SmoothNetwork.outputFn_zero rest _
  | _, _, .sigmoid rest, x => SmoothNetwork.outputFn_zero rest _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
