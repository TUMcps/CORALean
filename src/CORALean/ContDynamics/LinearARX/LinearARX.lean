module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Linear ARX models: the representation

CORA's `linearARX` [1], `y(k) = ∑_{i=1}^p Ā_i y(k-i) + ∑_{i=1}^{p+1} B̄_i u(k-i+1)`, in the
outputs and not in a state: the ARMAX model of [2, Def. 5]. `Abar i` is `Ā_{i+1}` and `Bbar j`
is `B̄_{j+1}`, so `Bbar 0` is the feedthrough. CORA's sampling time `dt` is stored, as in
`LinearSysDT`, and runs are indexed by the step; CORA's `tvp` parametrization is computed from
this one (`Aext`, `Btilde`). `stack y k` is the window `(y(k), …, y(k+p-1))`, the state the
conversion to `LinearSysDT` carries. `IsTrajectory` is the ARX recursion for every `k ≥ p`, the
first window in `Y₀`, as CORA's `y0`, every input in `U`.

## References

* [1] `contDynamics/@linearARX/linearARX.m`
* [2] [L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.](../../../../references/2023/luetzow-cdc-armax.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A linear ARX model: the output at step `k` is a combination of the last `p` outputs through
`Abar` and of the current and last `p` inputs through `Bbar`; `dt` is the sampling time. -/
structure LinearARX (𝕋 : Type) (dy du p : ℕ) where
  Abar : Fin p → Mat 𝕋 dy dy
  Bbar : Fin (p + 1) → Mat 𝕋 dy du
  dt : 𝕋

/-- The window of `p` outputs starting at `k`, block `a` holding `y(k+a)`. -/
def LinearARX.stack (p : ℕ) (y : ℕ → Vec ℝ dy) (k : ℕ) : Vec ℝ (p * dy) :=
  fun r => y (k + (finProdFinEquiv.symm r).1) (finProdFinEquiv.symm r).2

/-- A run of the model: the initial output window lies in `Y₀`, every input lies in `U`, and from
step `p` on each output follows the ARX equation. -/
structure LinearARX.IsTrajectory (sys : LinearARX 𝕋 dy du p) (Y₀ : S (p * dy)) (U : S du)
    (y : ℕ → Vec ℝ dy) (u : ℕ → Vec ℝ du) : Prop where
  init : LinearARX.stack p y 0 ∈ construct Y₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) (hk : p ≤ k) :
    y k = ∑ i : Fin p, toRealMat (sys.Abar i) *ᵥ y (k - (i + 1))
      + ∑ j : Fin (p + 1), toRealMat (sys.Bbar j) *ᵥ u (k - j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
