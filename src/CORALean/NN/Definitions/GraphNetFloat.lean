module

public import CORALean.NN.Definitions.GraphNet
public import CORALean.NN.Layers.Definitions.Relaxation

@[expose] public section

/-!
# Graph networks in floats

`Real.GraphNet` with float weights, each activation given by what CORA.cpp's `ZonoNet::forward`
computes for it: a `Relaxation`, or `productLine`'s parameters for the product of the halves (`p`
Newton steps, the least scale `τ`, the margins `w₁ q` at `q` generators and `w₂`). `slots` puts
the layer's errors into generators (CORA.cpp's slot count at every neuron) or the error box (at
none). `Images` ties a float network to the exact one with its weights read as reals, each
relaxation enclosing its function and the product's parameters as `productLine_encloses` asks.

-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic


-- ========================================  MAIN TYPE  ========================================= --

/-- A residual of a layer with `m` outputs: the earlier output `src` through the map `R`. -/
structure GraphResidual (𝕋 : Type) (Γ : List ℕ) (m : ℕ) where
  src : Fin Γ.length
  R : Mat 𝕋 m (Γ.get src)

/-- The activation of a layer: the identity, a relaxation at every neuron, or the product of the
halves; `slots` puts the errors into generators. -/
inductive GraphAct (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] : ℕ → Type where
  | identity {m : ℕ} : GraphAct 𝕋 m
  | elementwise {m : ℕ} (R : Relaxation 𝕋) (slots : Bool) : GraphAct 𝕋 m
  | product (n p : ℕ) (τ w₂ : 𝕋) (w₁ : ℕ → 𝕋) (slots : Bool) : GraphAct 𝕋 (n + n)

/-- A layer with `m` outputs after the outputs `Γ`: the source `src` through `W`, the bias `b`,
the residuals, and the activation. -/
structure GraphLayer (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (Γ : List ℕ) (m : ℕ) where
  src : Fin Γ.length
  W : Mat 𝕋 m (Γ.get src)
  b : Vec 𝕋 m
  residuals : List (GraphResidual 𝕋 Γ m)
  act : GraphAct 𝕋 m

/-- The layers after the outputs `Γ`, the last output of dimension `k`. -/
inductive GraphNet (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] : List ℕ → ℕ → Type where
  | done {k : ℕ} {Γ : List ℕ} : GraphNet 𝕋 (k :: Γ) k
  | layer {Γ : List ℕ} {m k : ℕ} (L : GraphLayer 𝕋 Γ m) (rest : GraphNet 𝕋 (m :: Γ) k) :
      GraphNet 𝕋 Γ k

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The exact activation `a` is what the float one encloses. -/
inductive GraphAct.Images : {m : ℕ} → GraphAct 𝕋 m → Real.GraphAct m → Prop where
  | identity {m : ℕ} : GraphAct.Images (GraphAct.identity (m := m)) Real.GraphAct.identity
  | elementwise {m : ℕ} {R : Relaxation 𝕋} {σ : ℝ → ℝ} (slots : Bool) (h : R.Encloses σ) :
      GraphAct.Images (GraphAct.elementwise (m := m) R slots) (Real.GraphAct.elementwise σ)
  | product {n p : ℕ} {τ w₂ : 𝕋} {w₁ : ℕ → 𝕋} (slots : Bool) (hτ : 0 < toReal τ)
      (hw₁ : ∀ q, 0 ≤ toReal (w₁ q)) (hw₂ : 0 ≤ toReal w₂) :
      GraphAct.Images (GraphAct.product n p τ w₂ w₁ slots) (Real.GraphAct.product n)

/-- The layer read as reals, with the exact activation `a`. -/
noncomputable def GraphLayer.toReal {Γ : List ℕ} {m : ℕ} (L : GraphLayer 𝕋 Γ m)
    (a : Real.GraphAct m) : Real.GraphLayer Γ m where
  src := L.src
  W := toRealMat L.W
  b := toRealVec L.b
  residuals := L.residuals.map fun r => ⟨r.src, toRealMat r.R⟩
  act := a

/-- The exact network `R` has `F`'s weights read as reals and activations that `F`'s enclose. -/
inductive GraphNet.Images : {Γ : List ℕ} → {k : ℕ} → GraphNet 𝕋 Γ k → Real.GraphNet Γ k → Prop
  where
  | done {k : ℕ} {Γ : List ℕ} : GraphNet.Images (GraphNet.done (k := k) (Γ := Γ)) Real.GraphNet.done
  | layer {Γ : List ℕ} {m k : ℕ} {L : GraphLayer 𝕋 Γ m} {rest : GraphNet 𝕋 (m :: Γ) k}
      {a : Real.GraphAct m} {R : Real.GraphNet (m :: Γ) k} (ha : L.act.Images a)
      (h : GraphNet.Images rest R) : GraphNet.Images (.layer L rest) (.layer (L.toReal a) R)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
