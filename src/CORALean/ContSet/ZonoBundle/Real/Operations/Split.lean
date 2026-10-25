module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Parallelotope
public import CORALean.ContSet.ZonoBundle.Real.Operations.Intersection
public import CORALean.ContSet.Zonotope.Real.Operations.Split

@[expose] public section

/-!
# `ZonoBundle.split`: splitting a bundle along a column of `Λ`

[1, Eq. 2]: the bundle is enclosed by the parallelotope `Ψ = Λ box(Λ⁻¹ Z_∩)`, `Ψ` is split along its
`j`-th generator `w⁽ʲ⁾ = γ λⱼ` into `Ψ₁` and `Ψ₂`, and the halves are the bundle with `Ψ₁`,
respectively `Ψ₂`, appended: `Z_∩¹ = Z_∩ ∩ Ψ₁`, `Z_∩² = Z_∩ ∩ Ψ₂`. One zonotope more than the bundle
had.
The box `B` is an argument; `Zonotope.split` is the halving of one generator.

## Inputs
* `Λ` – edge directions
* `B` – box in the transformed coordinates
* `j` – dimension to cut along
* `zB` – zonotope bundle

## Output
* the two halves of the bundle

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves `Z_∩¹`, `Z_∩²` of [1, Eq. 2], split along the `j`-th column of `Λ`. -/
noncomputable def ZonoBundle.split (Λ : Mat ℝ n n) (B : Interval (Vec ℝ n)) (j : Fin n)
    (zB : ZonoBundle (Vec ℝ n)) : ZonoBundle (Vec ℝ n) × ZonoBundle (Vec ℝ n) :=
  let Ψ := ZonoBundle.parallelotope Λ B                  -- Ψ = Λ box(Λ⁻¹ Z_∩)
  let Ψ₁ := (Ψ.split j).fst                                -- first half, center moved by -w⁽ʲ⁾/2
  let Ψ₂ := (Ψ.split j).snd                                -- second half, center moved by +w⁽ʲ⁾/2
  (zB.intersection ⟨1, fun _ => Ψ₁⟩, zB.intersection ⟨1, fun _ => Ψ₂⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
