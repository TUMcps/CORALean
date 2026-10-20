module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Operations.CubIdx
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.cubMapMixed`

The mixed form of CORA's `@zonotope/cubMap` (`aux_cubMapMixed`): an enclosure of
`{ z = (x₁ᵀ T x₂) * x₃ | x₁ ∈ Z₁, x₂ ∈ Z₂, x₃ ∈ Z₃ }`, `zᵢ = Σₖ (x₃)ₖ · (x₁ᵀ T{i,k} x₂)`. The
three arguments range independently, so every product `β₃ⱼ β₂ᵦ β₁ₐ` of extended factors gets
its own generator `Σₖ ([c₁,G₁]ᵀ T{i,k} [c₂,G₂])(a, b) · [c₃,G₃](k, j)`, the one at `((0, 0), 0)`
being the center (`Zcub(i, 1)`, the first column of `zonotope(Zcub)`).

## Inputs
* `T` – cubic tensor
* `Z₁` – first zonotope
* `Z₂` – second zonotope
* `Z₃` – third zonotope

## Output
* zonotope enclosing the mixed cubic image
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

/-- `aux_cubMapMixed`: the zonotope enclosing `{ (x₁ᵀ T x₂) * x₃ | xᵢ ∈ Zᵢ }`; generator
`((j, b), a)` is `Σₖ (x₁ᵀ T{i,k} x₂)(a, b) · [c₃,G₃](k, j)`. -/
noncomputable def Zonotope.cubMapMixed (T : Fin m → Fin n → Mat ℝ n n)
    (Z₁ Z₂ Z₃ : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ m) :=
  -- `[c,G]` of each set
  let Zext₁ : Fin (Z₁.h + 1) → Vec ℝ n := Fin.cons Z₁.c Z₁.G
  let Zext₂ : Fin (Z₂.h + 1) → Vec ℝ n := Fin.cons Z₂.c Z₂.G
  let Zext₃ : Fin (Z₃.h + 1) → Vec ℝ n := Fin.cons Z₃.c Z₃.G
  -- `Zcub(i, (j-1)*Nq + (b-1)*N1 + a)`
  let Zcub : Fin m → Fin (Z₃.h + 1) → Fin (Z₂.h + 1) → Fin (Z₁.h + 1) → ℝ :=
    fun i j b a => ∑ k, (Zext₁ a ⬝ᵥ (T i k *ᵥ Zext₂ b)) * Zext₃ j k
  { h := (Z₃.h + 1) * (Z₂.h + 1) * (Z₁.h + 1)
    c := fun i => Zcub i 0 0 0
    G := fun l i =>
      let t := Zonotope.cubIdx (Z₃.h + 1) (Z₂.h + 1) (Z₁.h + 1) l
      if t.1.1 = 0 ∧ t.1.2 = 0 ∧ t.2 = 0 then 0 else Zcub i t.1.1 t.1.2 t.2 }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
