module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Capsule.mtimes`

The exact layer's map: center and generator multiplied by `M`, the radius by the Frobenius norm
of `M`, an upper bound of its operator norm (not CORA's `max(eig(M Mᵀ))`, which is the square of
it, `Capsule.mtimes_cora_counterexample`). In floats the center and the generator are each a
rounded-down `mulVecDown`, and the distance of each from the exact product (from the gap between
`dotUp` and `dotDown`, per entry) is added to the radius as a length, with the scaled radius:
`r' = r σ + ‖M c - c̃‖₂ + ‖M g - g̃‖₂`. `σ` is `sqrtUp` of the sum of the squared entries, rounded
up. `k` is the number of Newton steps of the roots (`Global/Float/Sqrt`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.mtimes (k : ℕ) (M : Mat 𝕋 m n) (C : Capsule 𝕋 n) : Capsule 𝕋 m :=
  let c := mulVecDown M C.c
  let g := mulVecDown M C.g
  let cGap := fun i => subUp (dotUp (M i) C.c) (c i)
  let gGap := fun i => subUp (dotUp (M i) C.g) (g i)
  let σ := sqrtUp k (sumUp fun i => sqSumUp fun j => absolute (M i j))
  let r := addUp (addUp (mulUp C.r σ) (normUp k cGap)) (normUp k gGap)
  ⟨c, g, r⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
