module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.SpectraShadow.Float.Operations.CenterResidual

@[expose] public section

/-!
# `SpectraShadow.plus`

Generators and matrices concatenate exactly, the inequality's blocks along a
diagonal with `zero` between them, so only the centre rounds and its `residual`
goes into the box, leaving the sizes at `k₁ + k₂` and `m₁ + m₂` as over ℝ. Paying
into new generators instead is not an option here: a generator of a shadow
multiplies a variable nothing bounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.plus (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) where
  k := S₁.k + S₂.k
  m := S₁.m + S₂.m
  A₀ := blockDiag zero S₁.A₀ S₂.A₀
  A := Fin.append (fun i => blockDiag zero (S₁.A i) (fun _ _ => zero))
    (fun i => blockDiag zero (fun _ _ => zero) (S₂.A i))
  c := fun i => addDown (S₁.c i) (S₂.c i)
  G := Fin.append S₁.G S₂.G
  E := (S₁.E.plus S₂.E).plus (SpectraShadow.centerResidual S₁.c S₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
