module

public import CORALean.Global.CrossProduct

@[expose] public section

/-!
# Zonotopes stretched from a template

`⟨c, G diag(α)⟩`: a fixed template `G` whose generators are stretched by `α` — the
uncertainty sets [1, Eq. 5], [2, Eq. 9] and [3, Eq. 3] identify, `c` and `α` the
unknowns. Generators are a family over any finite index, so that a sum of such sets
is one over the sum of the indices, without renumbering into a `Fin`.

`HasNormals G N` says the rows of `N` carry both signs of every cross product of
`n` generators of `G`, up to a positive factor: the directions [2, Thm. 1] and
[3, Lemma 3] take from the template's halfspace representation.

## Inputs
* `m` – dimension
* `ι` – generator index type
* `c` – center
* `G` – template generators
* `α` – stretch factors

## Output
* the zonotope with the generators stretched by `α`

## References

* [1] [S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems: Unifying Formal
      Controller Synthesis and Reachset-Conformant Identification". IEEE Transactions on Robotics,
      2023.](../../../../../references/2023/liu-tro-guarantees-real-robotic.md)
* [2] [M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". Proceedings of
      10th International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH23),
      2023.](../../../../../references/2023/althoff-arch-reachset-conformance.md)
* [3] [L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE Transactions on
      Automatic Control,
      2026.](../../../../../references/2026/luetzow-tac-reachset-conformant-identification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⟨c, G diag(α)⟩`. -/
def Conform.templateZono {m : ℕ} {ι : Type} [Fintype ι] (c : Vec ℝ m) (G : ι → Vec ℝ m)
    (α : ι → ℝ) : Set (Vec ℝ m) :=
  {y | ∃ β : ι → ℝ, (∀ j, |β j| ≤ 1) ∧ y = c + ∑ j, β j • α j • G j}

/-- The rows of `N` carry both signs of every cross product of `m` generators. -/
def Conform.HasNormals {m : ℕ} {ι κ : Type} (G : ι → Vec ℝ (m + 1))
    (N : κ → Vec ℝ (m + 1)) : Prop :=
  ∀ S : Fin m → ι, ∃ (i₁ i₂ : κ) (lam : ℝ), 0 < lam ∧
    N i₁ = lam • nCross (Matrix.of fun a b => G (S b) a) ∧
    N i₂ = -(lam • nCross (Matrix.of fun a b => G (S b) a))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
