module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Definitions.Basic
public import CORALean.NN.Definitions.Sound
public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.NN.Layers.Instances
public import CORALean.NN.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemLinearIff
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


namespace CORALean

open Matrix

variable {α : Type} [Semiring α] {n m k d : ℕ}


-- ===================================  `CatCond.mem_ge_iff`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The guard `CatCond.ge i j` holds at `x` exactly when `xᵢ ≥ xⱼ`. -/
theorem CatCond.mem_ge_iff (i j : Fin n) (x : Vec ℝ n) :
    x ∈ (CatCond.ge i j).construct ↔ x j ≤ x i := (Real.PolyLevelSet.mem_linear_iff _ _ _ x).trans
  (by simp [Real.CompOp.holds, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib,
    Pi.single_apply])


-- ==================================  `CatCond.mem_neg_iff`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The guard `CatCond.neg i` holds at `x` exactly when `xᵢ < 0`. -/
theorem CatCond.mem_neg_iff (i : Fin n) (x : Vec ℝ n) :
    x ∈ (CatCond.neg i).construct ↔ x i < 0 :=
  (Real.PolyLevelSet.mem_linear_iff _ _ _ x).trans (by simp [Real.CompOp.holds, mulVec])


-- =================================  `CatCond.mem_nonneg_iff`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The guard `CatCond.nonneg i` holds at `x` exactly when `xᵢ ≥ 0`. -/
theorem CatCond.mem_nonneg_iff (i : Fin n) (x : Vec ℝ n) :
    x ∈ (CatCond.nonneg i).construct ↔ 0 ≤ x i := (Real.PolyLevelSet.mem_linear_iff _ _ _ x).trans
  (by simp [Real.CompOp.holds, mulVec, dotProduct, Pi.single_apply])


-- ====================================  `Chain.eval_cons`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The head map first, then the rest's composite, by definition; stated so that a rewrite can name
it. -/
theorem Chain.eval_cons {k : ℕ} (f : Vec ℝ n → Vec ℝ m) (rest : Chain m k) (x : Vec ℝ n) :
    (Chain.cons f rest).eval x = rest.eval (f x) := rfl


-- =====================================  `Chain.eval_nil`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- By definition; stated so that a rewrite can name it. -/
theorem Chain.eval_nil (x : Vec ℝ n) : (Chain.nil : Chain n n).eval x = x := rfl


-- ===================================  `Schedule.head_cons`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- Every index of the pattern is under the layer's width, so `cons`'s padding is never read. -/
theorem Schedule.head_cons (t : OrderPattern n) (sch : Schedule) :
    Schedule.head (Schedule.cons t sch) n = t := by
  funext i
  -- every index of the pattern is under the width, so the padding is not reached
  exact dif_pos i.isLt


-- ==================================  `WeightAcc.layer_eval`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `acc.layer` and `acc` have the same map. -/
theorem WeightAcc.layer_eval (acc : WeightAcc α n d) (x : Fin n → α) :
    acc.layer.eval x = acc.eval x := by
  cases acc <;> rfl

end CORALean


namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =============================  `identityDerEnclosure_encloses`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)

/-- The derivative is the constant `1`, and `1` reads as `1`. -/
theorem identityDerEnclosure_encloses :
    ScalarEncloses (identityDerEnclosure (𝕋 := 𝕋)) (fun _ => 1) :=
  fun _ _ _ _ => by simp [identityDerEnclosure, toReal_one]


-- ===============================  `identityEnclosure_encloses`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `id` is its own enclosure: a point of the box is a point of the box. -/
theorem identityEnclosure_encloses : ScalarEncloses (id : Interval 𝕋 → Interval 𝕋) id :=
  fun _ _ hl hu => ⟨hl, hu⟩


-- =================================  `reluEnclosure_encloses`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotonicity of `relu`, and `maximum` reads as `max`. -/
theorem reluEnclosure_encloses : ScalarEncloses (reluEnclosure (𝕋 := 𝕋)) Real.relu :=
  fun _ _ hl hu => by
    simp only [reluEnclosure, toReal_maximum, toReal_zero, Real.relu, max_comm _ (0 : ℝ)]
    exact ⟨max_le_max le_rfl hl, max_le_max le_rfl hu⟩


-- =================================  `toRealMat_map_absolute`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `absolute` is exact, so reading `W.map absolute` as reals is the entrywise absolute value of the
real reading of `W`. -/
theorem toRealMat_map_absolute {m n : ℕ} (W : Mat 𝕋 m n) :
    (toRealMat W).map abs = toRealMat (W.map absolute) :=
  funext fun _ => funext fun _ => (toReal_absolute _).symm

end CORALean.Float


namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- ==============================  `NeuralNetwork.enclose_outer`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Its own function, on every input set, with no hypothesis: `sound_eval` read through
`Sound.image_subset`. This is the guarantee a network gives as an `Enclose` kind. -/
theorem NeuralNetwork.enclose_outer (nn : NeuralNetwork S n m) (X : S n) :
    nn.eval.out '' construct X ⊆ construct (nn.enclose X) :=
  (NeuralNetwork.sound_eval nn).image_subset X


-- ==============================  `NeuralNetwork.ofLayer_sound`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- A single layer, sound at the function it is sound at. -/
theorem NeuralNetwork.ofLayer_sound {L : ℕ → ℕ → Type} [Enclose L S] {curr : L n m}
    {f : Vec ℝ n → Vec ℝ m} (h : (Enclose.toLayer (S := S) curr).Sound f) :
    (NeuralNetwork.ofLayer (S := S) curr).Sound f :=
  .layer h (.output fun _ => rfl) fun _ => rfl


-- ===============================  `NeuralNetwork.sound_output`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- The identity at `output`, which is the constructor read at `f = id`. -/
theorem NeuralNetwork.sound_output : (NeuralNetwork.output : NeuralNetwork S n n).Sound id :=
  .output fun _ => rfl


-- =============================  `RefinableLayer.atPattern_sound`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- At the refinable layer's own `eval`, whatever the pattern: the obligation is stored once and
asked at each. -/
theorem RefinableLayer.atPattern_sound (L : RefinableLayer S n m) (t : OrderPattern n) :
    (Enclose.toLayer (S := S) (L.atPattern t)).Sound L.eval :=
  ⟨L.enclose_outer t⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
