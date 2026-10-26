module

public import CORALean.ContSet.Interval.Real.Operations.PolyBoxRevise
public import CORALean.ContSet.Interval.Real.Theorems.PolyBoxReviseLeftLe
public import CORALean.ContSet.Interval.Real.Theorems.PolyBoxReviseRightGe
public import CORALean.ContSet.Interval.Real.Theorems.ZeroMemExtremal
public import CORALean.ContSet.LevelSet.Real.Definitions.Contractor
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.Monoid

@[expose] public section

/-!
# `polyBoxRevise` is a contractor

[1, Sec. 3 (PolyBoxRevise)] for a polynomial constraint `f(z) = Σᵢ fᵢ(z) z_kⁱ = 0`: the box it
returns lies in the box it was given and keeps every solution — the contractor property of
`IsContractor`, so contraction removes no solution. It needs the interval extension to enclose
every coefficient on the box, `[fᵢ]_N([Y]) ∋ fᵢ(z)` (conservative, [1, Def. 1]), and the two
searches to meet `IsLeftRootBound`/`IsRightRootBound`. A solution makes `Σᵢ fᵢ(z) z_kⁱ`
vanish, so it passes the extremal test, and the extremal functions are continuous, each term
being `min(c̲ᵢ xⁱ, c̅ᵢ xⁱ)`; the bound steps then keep it.

## Inputs
* `d` – polynomial degree
* `c` – constraint function
* `F` – coefficient functions
* `coeff` – coefficient enclosure of a box
* `k` – contracted coordinate
* `rootL` – left root search
* `rootR` – right root search

## Hypotheses
* `hc` – `c` is the polynomial in coordinate `k`
* `hF` – coefficient enclosure holds on every box
* `hL` – `rootL` is a left root bound
* `hR` – `rootR` is a right root bound

## Conclusion
* the revised box map is a contractor of `c`

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor Based
      on Extremal Functions". Principles and Practice of Constraint Programming – CP 2010, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- With `C` nonempty, `x ↦ g̲(x)` at `hᵢ = xⁱ` is a sum of minima, hence continuous. -/
private theorem aux_extremalLo_continuous {d : ℕ} {C : Interval (Vec ℝ (d + 1))}
    (hC : C.IsNonempty) : -- --- CONCL ---
    Continuous fun x : ℝ => C.extremalLo (fun i => x ^ (i : ℕ)) := by -- --- PROOF ---
  have heq : (fun x : ℝ => C.extremalLo (fun i => x ^ (i : ℕ))) =
      fun x => ∑ i, min (C.inf i * x ^ (i : ℕ)) (C.sup i * x ^ (i : ℕ)) := by
    funext x
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : C.inf i ≤ C.sup i := hC i
    split_ifs with hh
    · exact (min_eq_left (mul_le_mul_of_nonneg_right hi hh)).symm
    · exact (min_eq_right (mul_le_mul_of_nonpos_right hi (not_le.mp hh).le)).symm
  rw [heq]
  exact continuous_finsetSum _ fun i _ =>
    (continuous_const.mul (continuous_pow _)).min (continuous_const.mul (continuous_pow _))

/-- The mirror image: `g̅` is a sum of maxima. -/
private theorem aux_extremalHi_continuous {d : ℕ} {C : Interval (Vec ℝ (d + 1))}
    (hC : C.IsNonempty) : -- --- CONCL ---
    Continuous fun x : ℝ => C.extremalHi (fun i => x ^ (i : ℕ)) := by -- --- PROOF ---
  have heq : (fun x : ℝ => C.extremalHi (fun i => x ^ (i : ℕ))) =
      fun x => ∑ i, max (C.inf i * x ^ (i : ℕ)) (C.sup i * x ^ (i : ℕ)) := by
    funext x
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : C.inf i ≤ C.sup i := hC i
    split_ifs with hh
    · exact (max_eq_right (mul_le_mul_of_nonneg_right hi hh)).symm
    · exact (max_eq_left (mul_le_mul_of_nonpos_right hi (not_le.mp hh).le)).symm
  rw [heq]
  exact continuous_finsetSum _ fun i _ =>
    (continuous_const.mul (continuous_pow _)).max (continuous_const.mul (continuous_pow _))


/-- Membership in `B` with coordinate `k` replaced by `[a, b]`. -/
private theorem aux_mem_update_iff {B : Interval (Vec ℝ n)} {k : Fin n} {a b : ℝ}
    {z : Vec ℝ n} : -- --- CONCL ---
    z ∈ (⟨Function.update B.inf k a, Function.update B.sup k b⟩ : Interval (Vec ℝ n)).construct ↔
      (a ≤ z k ∧ z k ≤ b) ∧ ∀ i, i ≠ k → B.inf i ≤ z i ∧ z i ≤ B.sup i := by -- --- PROOF ---
  constructor
  · intro h
    refine ⟨?_, fun i hik => ?_⟩
    · have hk : Function.update B.inf k a k ≤ z k ∧ z k ≤ Function.update B.sup k b k := h k
      rwa [Function.update_self, Function.update_self] at hk
    · have hi : Function.update B.inf k a i ≤ z i ∧ z i ≤ Function.update B.sup k b i := h i
      rwa [Function.update_of_ne hik, Function.update_of_ne hik] at hi
  · rintro ⟨hk, hrest⟩ i
    change Function.update B.inf k a i ≤ z i ∧ z i ≤ Function.update B.sup k b i
    by_cases hik : i = k
    · subst hik
      rwa [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hik, Function.update_of_ne hik]
      exact hrest i hik


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.polyBoxRevise_isContractor {d : ℕ} {c : Vec ℝ n → ℝ}
    {F : Fin (d + 1) → Vec ℝ n → ℝ} {coeff : Interval (Vec ℝ n) → Interval (Vec ℝ (d + 1))}
    {k : Fin n} {rootL rootR : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (hc : ∀ z, c z = ∑ i, F i z * z k ^ (i : ℕ))
    (hF : ∀ B : Interval (Vec ℝ n), ∀ z ∈ B.construct, (fun i => F i z) ∈ (coeff B).construct)
    (hL : Interval.IsLeftRootBound rootL) (hR : Interval.IsRightRootBound rootR) : -- --- CONCL ---
    IsContractor c (Interval.polyBoxRevise coeff k rootL rootR) := by -- --- PROOF ---
  intro B
  have hB : ∀ z ∈ B.construct, ∀ i, B.inf i ≤ z i ∧ z i ≤ B.sup i := fun z hz i => hz i
  refine ⟨fun z hz => ?_, fun z hz hcz => ?_⟩
  · -- the result lies in `B`: coordinate `k` is cut to `[x̲, x̅]`, the rest unchanged
    dsimp only [Interval.polyBoxRevise] at hz
    obtain ⟨⟨hl, hu⟩, hrest⟩ := aux_mem_update_iff.mp hz
    intro i
    change B.inf i ≤ z i ∧ z i ≤ B.sup i
    by_cases hik : i = k
    · subst hik
      exact ⟨le_trans (le_max_left _ _) hl, le_trans hu (min_le_left _ _)⟩
    · exact hrest i hik
  · -- a solution passes the extremal test at `z_k`, so both bound steps keep it
    have hzk : z k ∈ Set.Icc (B.inf k) (B.sup k) := hB z hz k
    have hmem := hF B z hz
    have hC : (coeff B).IsNonempty := fun j => le_trans (hmem j).1 (hmem j).2
    have htest := Interval.zero_mem_extremal (h := fun i => z k ^ (i : ℕ)) hmem
      (by rw [← hc z, hcz])
    have hLo := (aux_extremalLo_continuous hC).continuousOn (s := Set.Icc (B.inf k) (B.sup k))
    have hHi := (aux_extremalHi_continuous hC).continuousOn (s := Set.Icc (B.inf k) (B.sup k))
    have hl := Interval.polyBoxReviseLeft_le hL hLo hHi hzk htest.1 htest.2
    have hr := Interval.le_polyBoxReviseRight hR hLo hHi hzk htest.1 htest.2
    dsimp only [Interval.polyBoxRevise]
    exact aux_mem_update_iff.mpr ⟨⟨max_le hzk.1 hl, le_min hzk.2 hr⟩, fun i _ => hB z hz i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
