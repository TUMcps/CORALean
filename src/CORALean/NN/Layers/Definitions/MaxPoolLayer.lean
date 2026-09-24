import CORALean.ContSet.Interval.Float.Interval

/-!
# The weights of a max pooling layer

CORA's `nnMaxPool2DLayer` as an `Enclose` kind: the stencil `tap`, windows of `k + 1`, and
`pivot`, which entry of each window the layer follows given the box of its input. Any pivot
is sound; a good one is only tighter.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure MaxPoolLayer (𝕋 : Type) (n m : ℕ) where
  k : ℕ
  tap : Fin m → Fin (k + 1) → Fin n
  pivot : Float.Interval (Vec 𝕋 n) → Fin m → Fin (k + 1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
