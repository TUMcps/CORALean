module

public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Zonotope.Real.Operations.Recenter
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Sort

@[expose] public section

/-!
# `Alg. 1`: which generators of the minuend have to enclose the subtrahend

[1, Alg. 1] picks `Z_{m,encl} ⊇ Z_s` out of the minuend's own generators, so that [1, Prop. 4] can
take the difference against the enclosing part alone and add the remainder back afterwards.
Longest generators first, greedily, while the interval hulls' worst coordinate ratio is still above
`µ̄`; then one at a time until the subtrahend actually fits. `sort` ranks by the squared length;
`enclGenSel_subset` proves what holds whatever the caller's `encloses` answers.

## Inputs
* `le` – decidable non-strict comparison
* `lt` – decidable strict comparison
* `encloses` – enclosure test
* `Zm` – zonotope to select from
* `Zs` – zonotope to enclose
* `μbar` – ratio threshold

## Output
* zonotope with the kept generators

## References

* [1] [M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794,
      2015.](../../../../../../references/2015/althoff-arxiv-minkowski-difference.md)
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}
variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The first `ξ` generators of `Z` under `σ`, at the center `c`. -/
def Zonotope.aux_genSelection (Z : Zonotope α) (σ : Equiv.Perm (Fin Z.h)) (c : α)
    (ξ : ℕ) : Zonotope α where
  h := min ξ Z.h
  c := c
  G := fun i => Z.G (σ (Fin.castLE (min_le_right ξ Z.h) i))

/-- Lines 6 and 9 together: `maxᵢ r_{s,i}/r_{sel,i} > µ̄`, cross-multiplied so
that `r_sel = 0` reads as line 4's `µ ← inf` rather than dividing by zero. -/
def Zonotope.aux_ratioExceeds (lt : ℝ → ℝ → Bool) (rs rsel : Vec ℝ n) (μbar : ℝ) : Bool :=
  (List.finRange n).any fun j => lt (μbar * rsel j) (rs j)

/-- Lines 6-10: one more generator while the ratio is still over `µ̄`, carrying
line 2's `r_sel` grown by line 8. The fuel is line 6's own bound `ξ < n_m`. -/
def Zonotope.aux_enclRatioLoop (lt : ℝ → ℝ → Bool) (Z : Zonotope (Vec ℝ n))
    (σ : Equiv.Perm (Fin Z.h)) (rs : Vec ℝ n) (μbar : ℝ) : ℕ → ℕ → Vec ℝ n → ℕ
  | 0, ξ, _ => ξ
  | k + 1, ξ, rsel =>
    if h : ξ < Z.h ∧ Zonotope.aux_ratioExceeds lt rs rsel μbar then
      Z.aux_enclRatioLoop lt σ rs μbar k (ξ + 1)
        (fun j => rsel j + |Z.G (σ ⟨ξ, h.1⟩) j|)
    else ξ

/-- Lines 11-13: one more generator while the selection, read at the
subtrahend's center, still does not enclose it. -/
def Zonotope.aux_enclCoverLoop (encloses : Zonotope (Vec ℝ n) → Bool) (Z : Zonotope (Vec ℝ n))
    (σ : Equiv.Perm (Fin Z.h)) (cs : Vec ℝ n) : ℕ → ℕ → ℕ
  | 0, ξ => ξ
  | k + 1, ξ =>
    if ξ < Z.h ∧ encloses (Z.aux_genSelection σ cs ξ) = false then
      Z.aux_enclCoverLoop encloses σ cs k (ξ + 1)
    else ξ


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the generators of `Zm` that are kept to enclose `Zs`. -/
noncomputable def Zonotope.enclGenSel (le lt : ℝ → ℝ → Bool)
    (encloses : Zonotope (Vec ℝ n) → Bool) (Zm Zs : Zonotope (Vec ℝ n)) (μbar : ℝ) :
    Zonotope (Vec ℝ n) :=
  -- 1. `G_sort ← sort(G_m)`, longest first
  let Gsort := sortPerm fun i j => le (∑ k, Zm.G j k ^ 2) (∑ k, Zm.G i k ^ 2)
  -- 2. `r_sel ← 0`
  let rsel : Vec ℝ n := 0
  -- 3. `r_s ← rad(box(Z_s))`
  let rs := Zs.recenter.absBound
  -- 4. lines 4-10: `µ ← inf`, `ξ ← 0`; while `µ > µ̄` and `ξ < n_m`, grow `ξ` by the ratio
  let ξratio := Zm.aux_enclRatioLoop lt Gsort rs μbar Zm.h 0 rsel
  -- 11. lines 11-13: while `Z_s ⊄ (c_s, g_sort^(1), …, g_sort^(ξ))`, `ξ ← ξ + 1`
  let ξ := Zm.aux_enclCoverLoop encloses Gsort Zs.c Zm.h ξratio
  -- 14. `Z_{m,encl} ← (c_m, g_sort^(1), …, g_sort^(ξ))`
  Zm.aux_genSelection Gsort Zm.c ξ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
