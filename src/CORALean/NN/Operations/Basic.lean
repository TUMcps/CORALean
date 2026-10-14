module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps
public import CORALean.NN.Definitions.Schedule
public import CORALean.NN.Definitions.WeightAcc
public import CORALean.NN.Definitions.WeightNetwork
public import CORALean.NN.Operations.WeightLayerEval
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `NN/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- ==================================  `identityDerEnclosure`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The identity's derivative is `1` everywhere, so the enclosure is the point `[1, 1]`. -/
def identityDerEnclosure (_ : Interval 𝕋) : Interval 𝕋 := ⟨one, one⟩


-- ====================================  `reluDerEnclosure`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's derivative of ReLU is `1` for `x > 0` and `0` otherwise. On a box it is `1` only when the
lower bound is certified positive, `0` only when the upper bound is certified nonpositive, and
`[0, 1]` across the kink. -/
def reluDerEnclosure (I : Interval 𝕋) : Interval 𝕋 :=
  ⟨if ltStrict zero I.inf then one else zero, if le I.sup zero then zero else one⟩


-- =====================================  `reluEnclosure`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `[max 0 l, max 0 u]` of the box `[l, u]`: the activation `max 0` is monotone. -/
def reluEnclosure (I : Interval 𝕋) : Interval 𝕋 := ⟨maximum zero I.inf, maximum zero I.sup⟩

end CORALean.Float


namespace CORALean

open Matrix

variable {α : Type} [Semiring α] {n m k d : ℕ}


-- =====================================  `Schedule.head`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The head layer's own pattern, cut to the width that layer has.

The head layer's own pattern, cut to the width that layer has: a layer reads its width here. -/
def Schedule.head (sch : Schedule) (n : ℕ) : OrderPattern n := fun i => sch 0 i.val


-- =====================================  `Schedule.tail`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- What the rest of a network reads, the head layer's pattern dropped. -/
def Schedule.tail (sch : Schedule) : Schedule := fun l => sch (l + 1)


-- =====================================  `WeightAcc.eval`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `x ↦ x` for nothing fused, `x ↦ W x + b` otherwise. -/
def WeightAcc.eval : ∀ {n d : ℕ}, WeightAcc α n d → (Fin n → α) → (Fin d → α)
  | _, _, .id, x => x
  | _, _, .aff W b, x => W *ᵥ x + b


-- ==================================  `WeightAcc.pushAffine`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Follow the accumulated map by `x ↦ scale ⊙ x + offset`.

CORA's `W = diag(scale) * W; b = scale .* b + offset`. -/
def WeightAcc.pushAffine : WeightAcc α n d → (Fin d → α) → (Fin d → α) → WeightAcc α n d
  | .id, s, o => .aff (Matrix.diagonal s) o
  | .aff W b, s, o => .aff (Matrix.diagonal s * W) (fun i => s i * b i + o i)


-- ==================================  `WeightAcc.pushLinear`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Follow the accumulated map by `x ↦ W₂ x + b₂`.

CORA's `W = layer.W * W; b = layer.W * b + layer.b`. -/
def WeightAcc.pushLinear : WeightAcc α n d → Mat α m d → (Fin m → α) → WeightAcc α n m
  | .id, W₂, b₂ => .aff W₂ b₂
  | .aff W b, W₂, b₂ => .aff (W₂ * W) (W₂ *ᵥ b + b₂)


-- ===================================  `WeightNetwork.eval`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The composite of the layers' maps, first layer first. -/
def WeightNetwork.eval : ∀ {n m : ℕ}, WeightNetwork α n m → (Fin n → α) → (Fin m → α)
  | _, _, .nil, x => x
  | _, _, .cons L rest, x => rest.eval (L.eval x)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
