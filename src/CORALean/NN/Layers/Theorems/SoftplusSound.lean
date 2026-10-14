module

public import CORALean.NN.Layers.Operations.Softplus
public import CORALean.NN.Layers.Theorems.ActivationOuterWhere
public import CORALean.NN.Layers.Theorems.SoftplusRelaxationSound
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# What the softplus layer encloses

`Real.softplus` at the stored sharpness, coordinatewise, for every point of a set whose box
satisfies `SoftplusBox` at each coordinate: the sharpness positive and the arguments of `expUp`
and `logDown` in the ranges those enclosures cover.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.softplus_outer (β : 𝕋) (k nl kl : ℕ) (s : S n) (x : Vec ℝ n) (hx : x ∈ construct s)
    (hs : ∀ i, SoftplusBox β k nl ((Float.IntervalOuter.interval s).inf i)
      ((Float.IntervalOuter.interval s).sup i)) :
    (fun i => Real.softplus (toReal β) (x i)) ∈
      construct ((Layer.softplus (S := S) (n := n) β k nl kl).enclose s) :=
  Layer.activation_outer_where (softplusRelaxation_sound β k nl kl) s x hx hs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
