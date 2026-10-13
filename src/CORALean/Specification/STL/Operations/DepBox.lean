module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Diagonal

@[expose] public section

/-!
# `interval(Z)` as a zonotope

[1, Alg. 1] encloses `C_i` and `D_i` by intervals "to reduce the number of generators": the
interval hull of a zonotope `⟨c, G⟩_Z`, `[c - r, c + r]` with `r_i = Σ_l |G_{i,l}|`, which is
the zonotope with the centre `c` and the `n` generators `r_i e_i`.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `interval(Z)` of [1, Alg. 1], as a zonotope with `n` axis-aligned generators. -/
noncomputable def STL.depBox (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) where
  h := n
  c := Z.c
  G := Matrix.diagonal fun i => ∑ l, |Z.G l i|

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
