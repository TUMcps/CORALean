module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Linear ARX models: the representation

CORA's `linearARX` [1], `y(k) = ∑_{i=1}^p Ā_i y(k-i) + ∑_{i=1}^{p+1} B̄_i u(k-i+1)`, in the
outputs and not in a state: the ARMAX model of [2, Def. 5], its input the combined `ũ`.
`Abar i` is `Ā_{i+1}` and `Bbar j` is `B̄_{j+1}`, so lag `j` of the input, `u(k-j)`, is
`Bbar j`, and `Bbar 0` is the feedthrough.

Time is counted in sampling periods, as in `LinearSysDT`, which is why no `dt` is
stored. CORA's `tvp` parametrization (`A_tilde`, `B_tilde`) is not stored: it is
computed from this one (`Aext`, `Btilde`). No `B`-versus-`c` choice: a constant
offset folds into the input set, as it does for every system here.

`stack y k` is the window `(y(k), …, y(k+p-1))`, block `a` holding `y(k+a)`, the
state the conversion to `LinearSysDT` carries. `Trajectory` is the ARX recursion
for every `k ≥ p`, the first window `stack y 0` in `Y₀`, as CORA's `y0`, and every
input in `U`; the conversion is not used to state it.

## References

* [1] `contDynamics/@linearARX/linearARX.m`
* [2] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure LinearARX (𝕋 : Type) (dy du p : ℕ) where
  Abar : Fin p → Mat 𝕋 dy dy
  Bbar : Fin (p + 1) → Mat 𝕋 dy du

/-- The window of `p` outputs starting at `k`, block `a` holding `y(k+a)`. -/
def LinearARX.stack (p : ℕ) (y : ℕ → Vec ℝ dy) (k : ℕ) : Vec ℝ (p * dy) :=
  fun r => y (k + (finProdFinEquiv.symm r).1) (finProdFinEquiv.symm r).2

structure LinearARX.Trajectory (sys : LinearARX 𝕋 dy du p) (Y₀ : S (p * dy)) (U : S du)
    (y : ℕ → Vec ℝ dy) (u : ℕ → Vec ℝ du) : Prop where
  init : LinearARX.stack p y 0 ∈ construct Y₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) (hk : p ≤ k) :
    y k = ∑ i : Fin p, toRealMat (sys.Abar i) *ᵥ y (k - (i + 1))
      + ∑ j : Fin (p + 1), toRealMat (sys.Bbar j) *ᵥ u (k - j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
