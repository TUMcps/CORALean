import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# `SetBasedNet`

The feed-forward network of [1, Def. 1] as set-based training propagates it: a chain of
layers, each linear, `W h + b`, or an elementwise activation given by what its image enclosure
needs per dimension, the slope `m(i)` and the approximation errors `e(i)`, `ē(i)` as functions
of that dimension's row of the input set (`Zonotope.imageEnclosure`). Indexed by the input and
output widths, `n₀` and `n_κ`.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

inductive SetBasedNet : ℕ → ℕ → Type
  | output {n : ℕ} : SetBasedNet n n
  | linear {n m k : ℕ} (W : Mat ℝ m n) (b : Vec ℝ m) (tail : SetBasedNet m k) : SetBasedNet n k
  | nonlinear {n k : ℕ} (m eLo eUp : Zonotope (Vec ℝ 1) → ℝ) (tail : SetBasedNet n k) :
      SetBasedNet n k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
