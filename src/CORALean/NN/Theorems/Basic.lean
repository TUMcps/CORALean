module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Definitions.Basic
public import CORALean.NN.Layers.Instances
public import CORALean.NN.Operations.Basic
public import CORALean.NN.Operations.ChainEval
public import CORALean.NN.Operations.RefinableLayerAtPattern
public import CORALean.NN.Operations.ScheduleCons
public import CORALean.NN.Operations.WeightAccLayer
public import CORALean.NN.Operations.WeightLayerEval
public import CORALean.NN.Theorems.ImageSubset
public import CORALean.NN.Theorems.SoundEval

@[expose] public section

/-!
# `NN/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ====================================  `Chain.eval_cons`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

variable {n m : ℕ}

/-- The head map first, then the rest's composite, by definition; stated so that a rewrite can name
it. -/
theorem Chain.eval_cons {k : ℕ} (f : Vec ℝ n → Vec ℝ m) (rest : Chain m k) (x : Vec ℝ n) :
    (Chain.cons f rest).eval x = rest.eval (f x) := rfl

end CORALean


-- =====================================  `Chain.eval_nil`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

variable {n m : ℕ}

/-- By definition; stated so that a rewrite can name it. -/
theorem Chain.eval_nil (x : Vec ℝ n) : (Chain.nil : Chain n n).eval x = x := rfl

end CORALean


-- =============================  `identityDerEnclosure_encloses`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The derivative is the constant `1`, and `1` reads as `1`. -/
theorem identityDerEnclosure_encloses :
    ScalarEncloses (identityDerEnclosure (𝕋 := 𝕋)) (fun _ => 1) :=
  fun _ _ _ _ => by simp [identityDerEnclosure, toReal_one]

end CORALean.Float


-- ===============================  `identityEnclosure_encloses`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `id` is its own enclosure: a point of the box is a point of the box. -/
theorem identityEnclosure_encloses : ScalarEncloses (id : Interval 𝕋 → Interval 𝕋) id :=
  fun _ _ hl hu => ⟨hl, hu⟩

end CORALean.Float


-- ==============================  `NeuralNetwork.enclose_outer`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

/-- Its own function, on every input set, with no hypothesis: `sound_eval` read through
`Sound.image_subset`. This is the guarantee a network gives as an `Enclose` kind. -/
theorem NeuralNetwork.enclose_outer (nn : NeuralNetwork S n m) (X : S n) :
    nn.eval.out '' construct X ⊆ construct (nn.enclose X) :=
  (NeuralNetwork.sound_eval nn).image_subset X

end CORALean


-- =============================  `RefinableLayer.atPattern_sound`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

/-- At the refinable layer's own `eval`, whatever the pattern: the obligation is stored once and
asked at each. -/
theorem RefinableLayer.atPattern_sound (L : RefinableLayer S n m) (t : OrderPattern n) :
    (Enclose.toLayer (S := S) (L.atPattern t)).Sound L.eval :=
  ⟨L.enclose_outer t⟩

end CORALean


-- =================================  `reluEnclosure_encloses`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- Monotonicity of `max 0`, and `maximum` reads as `max`. -/
theorem reluEnclosure_encloses : ScalarEncloses (reluEnclosure (𝕋 := 𝕋)) (fun x => max 0 x) :=
  fun _ _ hl hu => by
    simp only [reluEnclosure, toReal_maximum, toReal_zero]
    exact ⟨max_le_max le_rfl hl, max_le_max le_rfl hu⟩

end CORALean.Float


-- ===================================  `Schedule.head_cons`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- Every index of the pattern is under the layer's width, so `cons`'s padding is never read. -/
theorem Schedule.head_cons (t : OrderPattern n) (sch : Schedule) :
    Schedule.head (Schedule.cons t sch) n = t := by
  funext i
  -- every index of the pattern is under the width, so the padding is not reached
  exact dif_pos i.isLt

end CORALean


-- =================================  `toRealMat_map_absolute`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `absolute` is exact, so reading `W.map absolute` as reals is the entrywise absolute value of the
real reading of `W`. -/
theorem toRealMat_map_absolute {m n : ℕ} (W : Mat 𝕋 m n) :
    (toRealMat W).map abs = toRealMat (W.map absolute) :=
  funext fun _ => funext fun _ => (toReal_absolute _).symm

end CORALean.Float


-- ==================================  `WeightAcc.layer_eval`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open Matrix

variable {α : Type} [Semiring α] {n m k d : ℕ}

/-- `acc.layer` and `acc` have the same map. -/
theorem WeightAcc.layer_eval (acc : WeightAcc α n d) (x : Fin n → α) :
    acc.layer.eval x = acc.eval x := by
  cases acc <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
