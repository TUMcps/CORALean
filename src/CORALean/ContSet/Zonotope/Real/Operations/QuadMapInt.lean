module

public import CORALean.ContSet.Zonotope.Real.Operations.QuadMap

@[expose] public section

/-!
# `Zonotope.quadMapInt`

[1, Prop. 3]'s `quadint(H, Z)`: the quadratic map of a zonotope at interval matrices
`H⁽ⁱ⁾ = Hc⁽ⁱ⁾ ⊕ [-HΔ⁽ⁱ⁾, HΔ⁽ⁱ⁾]`. The center and generators of `Zonotope.quadMap` ([1, Lemma 1])
are evaluated in interval arithmetic; the result keeps the midpoints as center and generators and
puts the radii into the axis generators `l⁽ᵏ⁾`, `l⁽ᵏ⁾ₖ = d_Δ,ₖ + Σᵢ h_Δ,ₖ⁽ⁱ⁾`. Every entry of
`quadMap` is a sum of terms `λ⁽ⁱ⁾ᵀH⁽ʲ⁾λ⁽ᵏ⁾` holding the interval matrix once, which interval
arithmetic evaluates exactly ([1, Lemma 2]): midpoint `λ⁽ⁱ⁾ᵀHc⁽ʲ⁾λ⁽ᵏ⁾`, radius
`|λ⁽ⁱ⁾|ᵀHΔ⁽ʲ⁾|λ⁽ᵏ⁾|`. So the midpoints are `quadMap` at `Hc` and the radii `quadMap` at `HΔ` of
the zonotope of absolute values; no interval type is involved. `HΔ` is meant nonnegative.

## Inputs
* `Hc` – center quadratic matrices
* `HΔ` – radius quadratic matrices
* `Z` – zonotope

## Output
* zonotope enclosing the interval quadratic images

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 3]: `quadint(H, Z) = (d_c, h_c⁽¹⁾, …, h_c⁽σ⁾, l⁽¹⁾, …, l⁽ᵐ⁾)`. -/
noncomputable def Zonotope.quadMapInt (Hc HΔ : Fin m → Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ m) :=
  let Z_abs : Zonotope (Vec ℝ n) := ⟨Z.h, fun i => |Z.c i|, fun j i => |Z.G j i|⟩  -- |λ⁽ⁱ⁾|
  let d_c : Vec ℝ m := (Z.quadMap Hc).c                       -- midpoint of the center
  let h_c : Fin (Z.quadMap Hc).h → Vec ℝ m := (Z.quadMap Hc).G  -- midpoints of the generators
  let d_Δ : Vec ℝ m := (Z_abs.quadMap HΔ).c                   -- radius of the center
  let h_Δ : Fin (Z.quadMap Hc).h → Vec ℝ m := (Z_abs.quadMap HΔ).G  -- radii of the generators
  let y : Vec ℝ m := d_Δ + ∑ i, h_Δ i                         -- y = d_Δ + Σᵢ h_Δ⁽ⁱ⁾
  let l : Fin m → Vec ℝ m := fun k => Pi.single k (y k)       -- l⁽ᵏ⁾ⱼ = yₖ at j = k, else 0
  ⟨(Z.quadMap Hc).h + m, d_c, Fin.append h_c l⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
