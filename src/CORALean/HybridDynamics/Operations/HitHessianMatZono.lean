import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation

/-!
# The matrix zonotope enclosing the numerators of `y_h`'s second derivatives

[1, Prop. 3]: for `R(0) = ⟨c_x, g_x^(1), …, g_x^(p)⟩` and an enclosure `ψ_c ⊕ [-1, 1]ψ_g` of
`Θ(x₀)/Λ(x₀)` over `R(0)` (the proof's (19)), the matrix zonotope
`(C̃⁽ⁱ⁾, G̃^(i,1), …, G̃^(i,1+2p))` of the proof's (18) and the proposition, one `let` per printed
formula. Its factors are `κ`, the one of `[-1, 1]ψ_g`, then `β_α` and `κβ_α`.

Real layer only: a specification of the matrix zonotope [1] computes, at `ℝ`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 3]: `(C̃⁽ⁱ⁾, G̃^(i,1), …, G̃^(i,1+2p))` from `R(0)`, `ψ_c` and `ψ_g`. -/
def GuardMap.hitHessianMatZono (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ)
    (R₀ : Real.Zonotope (Vec ℝ n)) (ψc ψg : Vec ℝ n) (i : Fin n) :
    Real.Zonotope (Mat ℝ n n) :=
  let cx := R₀.c                                             -- `c_x`
  let gx := R₀.G                                             -- `g_x^(α)`
  let Υ : Vec ℝ n := nv ᵥ* A                                 -- `Υ = nᵀA`
  let Ω : Mat ℝ n n := -vecMulVec nv Υ + vecMulVec Υ nv      -- `Ω = -nΥ + Υᵀnᵀ`
  let Θc : Vec ℝ n :=                                        -- `Θ_c`, (18)
    -((nv ⬝ᵥ (A *ᵥ cx + b)) • nv) - (d - nv ⬝ᵥ cx) • Υ
  let Θg : Fin R₀.h → Vec ℝ n := fun α =>                    -- `Θ_g^(α)`, (18)
    -((nv ⬝ᵥ (A *ᵥ gx α)) • nv) + (nv ⬝ᵥ gx α) • Υ
  let C : Mat ℝ n n := Matrix.of fun l m =>                  -- `C̃⁽ⁱ⁾`
    A i l * Θc m + A i m * Θc l + (Ω l m - ψc l * 2 * Υ m) * ((A *ᵥ cx) i + b i)
  let G₁ : Mat ℝ n n := Matrix.of fun l m =>                 -- `G̃^(i,1)`
    -(ψg l * 2 * Υ m) * ((A *ᵥ cx) i + b i)
  let Gβ : Fin R₀.h → Mat ℝ n n := fun α => Matrix.of fun l m =>   -- `G̃^(i,1+α)`
    A i l * Θg α m + A i m * Θg α l + (Ω l m - ψc l * 2 * Υ m) * (A *ᵥ gx α) i
  let Gκβ : Fin R₀.h → Mat ℝ n n := fun α => Matrix.of fun l m =>  -- `G̃^(i,1+p+α)`
    -(ψg l * 2 * Υ m) * (A *ᵥ gx α) i
  ⟨1 + R₀.h + R₀.h, C, Fin.append (Fin.append ![G₁] Gβ) Gκβ⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
