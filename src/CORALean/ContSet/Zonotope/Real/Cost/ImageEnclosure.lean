import CORALean.ContSet.Zonotope.Real.Cost.Mtimes
import CORALean.ContSet.Zonotope.Real.Cost.Plus
import CORALean.ContSet.Zonotope.Real.Operations.ImageEnclosure

/-!
# `Zonotope.imageEnclosureCost`

Asserted, not proved, as [1, Prop. 15]'s proof counts [1, Alg. 1]: the bounds `c ∓ |G| 1` of the
input (line 2, Prop. 2) at `2n(q + 1)`; per neuron the slope and the approximation errors
(lines 3-5, Def. 7 and Prop. 10) at a constant `cNeuron`; `Diag(m) H` (line 6) as Prop. 4's
matrix product, `Zonotope.mtimesCost n n q`, and the `n` additions of the offset; and the sum
with the interval (line 7, Prop. 3), `Zonotope.plusCost n`. `Operations/ImageEnclosure.lean`
reads the same per-row quantities. The proved part is the bound [1, Prop. 15] states,
`O(n² q)` in `n` and `q`: at most `(cNeuron + 10) n² q` once `n, q ≥ 1`.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What [1, Alg. 1] costs at `n` dimensions, `q` generators and `cNeuron` per neuron. -/
def Zonotope.imageEnclosureCost (n q : ℕ) (cNeuron : Cost) : Cost :=
  ⟨2 * (n * (q + 1))⟩ + n • cNeuron + Zonotope.mtimesCost n n q + ⟨n⟩ + Zonotope.plusCost n

/-- [1, Prop. 15]: `O(n² q)`, at most `(cNeuron + 10) n² q` for `n, q ≥ 1`. -/
theorem Zonotope.imageEnclosureCost_le (n q : ℕ) (cNeuron : Cost) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    (Zonotope.imageEnclosureCost n q cNeuron).ops ≤
      (cNeuron.ops + 10) * (n * n * q) := by -- --- PROOF ---
  simp only [Zonotope.imageEnclosureCost, Zonotope.mtimesCost, Zonotope.plusCost, Cost.matVec,
    Cost.ops_add, Cost.ops_smul]
  have h1 : n ≤ n * n * q := by nlinarith
  have h2 : n * q ≤ n * n * q := by nlinarith
  have h3 : n * cNeuron.ops ≤ cNeuron.ops * (n * n * q) := by nlinarith
  nlinarith

/-- Monotone in the generator count. -/
theorem Zonotope.imageEnclosureCost_mono {q q' : ℕ} (n : ℕ) (cNeuron : Cost) (hq : q ≤ q') :
    Zonotope.imageEnclosureCost n q cNeuron ≤
      Zonotope.imageEnclosureCost n q' cNeuron := by -- --- PROOF ---
  simp only [Cost.le_iff, Zonotope.imageEnclosureCost, Zonotope.mtimesCost, Cost.ops_add,
    Cost.ops_smul]
  have : 2 * (n * (q + 1)) ≤ 2 * (n * (q' + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have : (q + 1) * (Cost.matVec n n).ops ≤ (q' + 1) * (Cost.matVec n n).ops :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
