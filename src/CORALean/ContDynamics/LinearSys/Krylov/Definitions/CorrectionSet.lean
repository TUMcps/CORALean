module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff

@[expose] public section

/-!
# The correction interval matrix in the Krylov subspace

[1, Lemma III.3]'s `F = ⊕_{i=2}^η [(i^{-i/(i-1)} - i^{-1/(i-1)})δⁱ, 0] Hⁱ/i! ⊕ E(δ)`, with
`E(δ) = [-W(δ), W(δ)]` and `W(δ) = e^{|H|δ} - Σ_{i≤η} (δ|H|)ⁱ/i!` (15), as the set of matrices it
contains: one coefficient per order, in its interval, plus a matrix within `W(δ)` entrywise.
The interval's lower end is `corrCoeff i · δⁱ`, `corrCoeff i = i^{-i/(i-1)} - i^{-1/(i-1)}`.

## Inputs
* `H` – Hessenberg matrix
* `δ` – step length
* `η` – Taylor order

## Output
* set of correction matrices in the Krylov subspace

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Krylov.correctionSet (H : Mat ℝ m m) (δ : ℝ) (η : ℕ) : Set (Mat ℝ m m) :=
  {F | ∃ (lam : ℕ → ℝ) (E : Mat ℝ m m),
    (∀ i ∈ Finset.Icc 2 η, lam i ∈ Set.Icc (MatExp.corrCoeff i * δ ^ i) 0) ∧
    E ∈ MatExp.expRemainderInterval H δ η ∧
    F = ∑ i ∈ Finset.Icc 2 η, lam i • (((Nat.factorial i : ℝ))⁻¹ • H ^ i) + E}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
