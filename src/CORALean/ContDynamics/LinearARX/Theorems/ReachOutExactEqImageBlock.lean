module

public import CORALean.ContDynamics.LinearARX.Definitions.ReachOutExact
public import CORALean.ContDynamics.LinearARX.Definitions.ReachWindowExact

@[expose] public section

/-!
# Each block of the window set is a reachable output set

`Y(k+a)` is the projection of the joint window set at `k` onto block `a`, exactly: the
reading under which [1, Eq. 12] and Alg. 1–2 return the reachable sets, one per block,
and the one CORA's `reach` takes (`project` per block). The windows themselves are not
the product of these projections; see `reachWindowExact_ne_prod`.

## Inputs
* `sys` – ARX system
* `y₀` – measured first output window
* `U` – input sets per step
* `k` – step
* `a` – block index

## Hypotheses
* none

## Conclusion
* the reachable outputs are the block projection of the window set

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.reachOutExact_eq_image_block (sys : LinearARX 𝕋 dy du p) (y₀ : Vec ℝ (p * dy))
    (U : ℕ → Set (Vec ℝ du)) (k : ℕ) (a : Fin p) : -- --- CONCL ---
    sys.reachOutExact y₀ U (k + a)
      = (fun w b => w (finProdFinEquiv (a, b))) ''
        sys.reachWindowExact y₀ U k := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨y, u, h₀, hu, hy, rfl⟩
    refine ⟨LinearARX.stack p y k, ⟨y, u, h₀, hu, hy, rfl⟩, ?_⟩
    funext b
    show y (k + (finProdFinEquiv.symm (finProdFinEquiv (a, b))).1)
      (finProdFinEquiv.symm (finProdFinEquiv (a, b))).2 = y (k + a) b
    rw [Equiv.symm_apply_apply]
  · rintro ⟨w, ⟨y, u, h₀, hu, hy, rfl⟩, rfl⟩
    refine ⟨y, u, h₀, hu, hy, ?_⟩
    funext b
    show y (k + (finProdFinEquiv.symm (finProdFinEquiv (a, b))).1)
      (finProdFinEquiv.symm (finProdFinEquiv (a, b))).2 = y (k + a) b
    rw [Equiv.symm_apply_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
