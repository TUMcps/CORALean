module

public import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
public import CORALean.Global.Block

@[expose] public section

/-!
# `ConZonotope.lift`

[1, Prop. 3]'s lifted zonotope `Z⁺ = {[G; A₁], [c; −b₁], A₂, b₂}` in `ℝ^{n+m₁}`. The partition
`[A b] = [A₁ b₁; A₂ b₂]` is the first `m₁` rows and the last `m₂`; any other partition is
this one after permuting the rows, which does not change the set. At `m₂ = 0` the constraint is
empty and `Z⁺` is a zonotope.

## Inputs
* `n` – dimension
* `m₁` – constraints moved into coordinates
* `m₂` – constraints kept
* `h` – number of generators
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset

## Output
* the lifted constrained zonotope

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 3]: the first `m₁` constraint rows move into the generators and the center. -/
noncomputable def ConZonotope.lift {n m₁ m₂ h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n)
    (A : Mat ℝ (m₁ + m₂) h) (b : Vec ℝ (m₁ + m₂)) : ConZonotope (Vec ℝ (n + m₁)) :=
  let A₁ : Mat ℝ m₁ h := fun i => A (Fin.castAdd m₂ i)           -- first m₁ rows of A
  let A₂ : Mat ℝ m₂ h := fun i => A (Fin.natAdd m₁ i)            -- last m₂ rows of A
  let b₁ : Vec ℝ m₁ := fun i => b (Fin.castAdd m₂ i)
  let b₂ : Vec ℝ m₂ := fun i => b (Fin.natAdd m₁ i)
  ConZonotope.ofMat (Fin.append c (-b₁)) (fun j => Fin.append (G j) fun i => A₁ i j) A₂ b₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
