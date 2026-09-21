import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
import CORALean.ContSet.Zonotope.Real.Operations.GenSelection
import CORALean.ContSet.Zonotope.Real.Operations.Recentre
import CORALean.Global.Sort

/-!
# `Alg. 1`: which generators of the minuend have to enclose the subtrahend

[1, Alg. 1] picks `Z_{m,encl} ⊇ Z_s` out of the minuend's own generators, so
that [1, Prop. 4] can take the difference against the enclosing part alone and
add the remainder back afterwards. Longest generators first, greedily, while
the interval hulls' worst coordinate ratio is still above `µ̄`; then one at a
time until the subtrahend actually fits.

Three departures, all recorded on the paper's page. Lines 6 and 9 are one
cross-multiplied test, `µ̄ · r_{sel,i} < r_{s,i}`, line 4's `µ ← inf` being
exactly `r_sel = 0` and no real number. `sort` ranks by the squared length,
which orders generators as `‖·‖₂` does without a square root. And line 11's
containment test is the caller's `encloses` — zonotope-in-zonotope containment
has no decision procedure here — so the enclosure it reports is the caller's
claim; `enclGenSel_subset` proves what holds whatever it answers.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- Lines 6 and 9 together: `maxᵢ r_{s,i}/r_{sel,i} > µ̄`, cross-multiplied so
that `r_sel = 0` reads as line 4's `µ ← inf` rather than dividing by zero. -/
def Zonotope.ratioExceeds (lt : ℝ → ℝ → Bool) (rs rsel : Vec ℝ n) (μbar : ℝ) : Bool :=
  (List.finRange n).any fun j => lt (μbar * rsel j) (rs j)

/-- Lines 6-10: one more generator while the ratio is still over `µ̄`, carrying
line 2's `r_sel` grown by line 8. The fuel is line 6's own bound `ξ < n_m`. -/
def Zonotope.enclRatioLoop (lt : ℝ → ℝ → Bool) (Z : Zonotope (Vec ℝ n))
    (σ : Equiv.Perm (Fin Z.h)) (rs : Vec ℝ n) (μbar : ℝ) : ℕ → ℕ → Vec ℝ n → ℕ
  | 0, ξ, _ => ξ
  | k + 1, ξ, rsel =>
    if h : ξ < Z.h ∧ Zonotope.ratioExceeds lt rs rsel μbar then
      Z.enclRatioLoop lt σ rs μbar k (ξ + 1)
        (fun j => rsel j + |Z.G (σ ⟨ξ, h.1⟩) j|)
    else ξ

/-- Lines 11-13: one more generator while the selection, read at the
subtrahend's centre, still does not enclose it. -/
def Zonotope.enclCoverLoop (encloses : Zonotope (Vec ℝ n) → Bool) (Z : Zonotope (Vec ℝ n))
    (σ : Equiv.Perm (Fin Z.h)) (cs : Vec ℝ n) : ℕ → ℕ → ℕ
  | 0, ξ => ξ
  | k + 1, ξ =>
    if ξ < Z.h ∧ encloses (Z.genSelection σ cs ξ) = false then
      Z.enclCoverLoop encloses σ cs k (ξ + 1)
    else ξ


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the generators of `Zm` that are kept to enclose `Zs`. -/
noncomputable def Zonotope.enclGenSel (le lt : ℝ → ℝ → Bool)
    (encloses : Zonotope (Vec ℝ n) → Bool) (Zm Zs : Zonotope (Vec ℝ n)) (μbar : ℝ) :
    Zonotope (Vec ℝ n) :=
  let Gsort := sortPerm fun i j => le (∑ k, Zm.G j k ^ 2) (∑ k, Zm.G i k ^ 2)  -- 1. sort(Gm)
  let rsel : Vec ℝ n := 0                                       -- 2. r_sel ← 0
  let rs := Zs.recentre.absBound                                -- 3. r_s ← rad(box(Zs))
  let ξratio := Zm.enclRatioLoop lt Gsort rs μbar Zm.h 0 rsel   -- 4.-10. grow by the ratio
  let ξ := Zm.enclCoverLoop encloses Gsort Zs.c Zm.h ξratio     -- 11.-13. grow until Zs fits
  Zm.genSelection Gsort Zm.c ξ                                  -- 14. Z_{m,encl}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
