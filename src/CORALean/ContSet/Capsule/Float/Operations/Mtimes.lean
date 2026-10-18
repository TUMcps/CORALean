module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Capsule.mtimes`

The exact layer's map: center and generator multiplied by `M`, the radius by the Frobenius norm
of `M`, an upper bound of its operator norm (not CORA's `max(eig(M Mᵀ))`, which is the square of
it, `Capsule.mtimes_cora_counterexample`). In floats the center and the generator are each a
rounded-down `mulVecDown`, and what each misses of the exact product (between `0` and the gap to
`dotUp`, per entry) goes into the error box: the center's as it is, the generator's at every
segment parameter `t ∈ [-1, 1]`, so as the symmetric box of the gap. The operand's box is mapped
by `Interval.mtimes`. The radius is `r σ` rounded up, `σ` the `sqrtUp` of the sum of the squared
entries, rounded up. `k` is the number of Newton steps of the roots (`Global/Float/Sqrt`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.mtimes (k : ℕ) (M : Mat 𝕋 m n) (C : Capsule 𝕋 n) : Capsule 𝕋 m :=
  let c := mulVecDown M C.c
  let g := mulVecDown M C.g
  -- what the stored center and generator miss of the exact products
  let cRes := Interval.residual c (fun i => dotUp (M i) C.c) c
  let gGap := fun i => subUp (dotUp (M i) C.g) (g i)
  let σ := sqrtUp k (sumUp fun i => sqSumUp fun j => absolute (M i j))
  ⟨c, g, mulUp C.r σ, ((Interval.mtimes M C.I_error).plus cRes).plus (Interval.symmetric gGap)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
