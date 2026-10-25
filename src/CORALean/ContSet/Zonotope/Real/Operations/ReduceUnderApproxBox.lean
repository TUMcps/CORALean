module

public import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit
public import CORALean.ContSet.Zonotope.Real.Operations.SplitKept
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `Zonotope.reduceUnderApproxBox`

The box method of [1, Sec. IV-B]: split `Z = Z_a ⊕ Z_b` by the metric (5), which is Girard's
(`girardSplit`, `Z_a` the `ν̂ - n = (ô - 1) n` generators ranking first), underapproximate the
rotation of `Z_b` by a box `B = ⟨0, diag(γ)⟩`, and rotate it back: `Ẑ = Z_a ⊕ U B`. The rotation `U`
(Step 2, the left singular vectors of `[G_b -G_b][G_b -G_b]ᵀ`) and the box `γ` (Step 3, a
second-order cone program) are arguments; `o = ô`.

## Inputs
* `Z` – zonotope
* `o` – target order
* `U` – basis matrix
* `γ` – box radii

## Hypotheses
* `hlt` – reduction needed

## Output
* under-approximating zonotope with an added box

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the Order Reduction
      of Zonotopes". IEEE Control Systems Letters, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real
open scoped CORALean
variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. IV-B], Steps 1), 3) and 4): `Ẑ = Z_a ⊕ U B`, with `B = ⟨0, diag(γ)⟩`. -/
noncomputable def Zonotope.reduceUnderApproxBox (Z : Zonotope (Vec ℝ n)) (o : ℕ)
    (hlt : o * n < Z.h) (U : Mat ℝ n n) (γ : Vec ℝ n) : Zonotope (Vec ℝ n) :=
  let part := Z.girardSplit o hlt                       -- 1) Z = Z_a ⊕ Z_b by (5)
  let Za := Z.splitKept part                            --    Z_a = ⟨c, G_a⟩
  let B : Zonotope (Vec ℝ n) := ⟨n, 0, Matrix.diagonal γ⟩  -- 3) B = ⟨0, diag(γ)⟩
  Za.plus (Zonotope.mtimes U B)                         -- 4) Ẑ = Z_a ⊕ U B

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
