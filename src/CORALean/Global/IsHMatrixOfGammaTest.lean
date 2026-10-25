module

public import CORALean.Global.PassesGammaTest
public import CORALean.Global.HMatrix

@[expose] public section

/-!
# The inclusion (2) makes the interval Jacobian an H-matrix

[1, Cor. 3.1], "furthermore": if `x₀ + Γ(J, x - x₀, y - f(x₀)) ⊆ int x` with `f(x₀) ∈ y`, then
`J` is an H-matrix. The proof is the paper's, made explicit: the vector `u = wid x` is the
scaling. For row `i`, take the real row of `J` with the smallest magnitude on the diagonal and
the largest off it, and the two corners of `x` that push `Σ_{j≠i} Jᵢⱼ (vⱼ - x₀ⱼ)` to its
extremes; both images lie in the open interval `(xloᵢ, xhiᵢ)`, whose width they exceed unless
`Σ_{j≠i} |Jᵢⱼ| widⱼ < |Jᵢᵢ| widᵢ`. The interval matrix `J` enters only through its mignitudes
(`min |Jlo|, |Jhi|`) and magnitudes (`max`), and needs `0 ∉ Jᵢᵢ`.

## Inputs
* `f` – map
* `x₀` – expansion point
* `xlo` – lower end of the domain box
* `xhi` – upper end of the domain box
* `ylo` – lower end of the target box
* `yhi` – upper end of the target box
* `Jlo` – lower end of the Jacobian enclosure
* `Jhi` – upper end of the Jacobian enclosure

## Hypotheses
* `hJ` – the enclosure's ends are ordered
* `hdiag` – no diagonal enclosure contains zero
* `hx₀` – the expansion point lies in the domain box
* `hy` – the map's value at the expansion point lies in the target box
* `h` – the inclusion test holds

## Conclusion
* the Jacobian enclosure is an H-matrix

## References

* [1] A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued functions".
      Reliable Computing, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Finset

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 3.1]: (2) makes `J` an H-matrix, with the scaling `u = wid x`. -/
theorem isHMatrix_of_gammaTest {f : (Fin n → ℝ) → (Fin n → ℝ)} {x₀ xlo xhi ylo yhi : Fin n → ℝ}
    {Jlo Jhi : Matrix (Fin n) (Fin n) ℝ} (hJ : ∀ i j, Jlo i j ≤ Jhi i j)
    (hdiag : ∀ i, (0 : ℝ) ∉ Icc (Jlo i i) (Jhi i i)) (hx₀ : x₀ ∈ Icc xlo xhi)
    (hy : f x₀ ∈ Icc ylo yhi) (h : PassesGammaTest f x₀ xlo xhi Jlo Jhi ylo yhi) : -- --- CONCL ---
    IsHMatrix (fun i j => min |Jlo i j| |Jhi i j|)
      (fun i j => max |Jlo i j| |Jhi i j|) := by -- --- PROOF ---
  -- the box has positive width: the open interval it must contain is nonempty
  have hw : ∀ i, xlo i < xhi i := fun i => by
    have := h (f x₀) hy Jlo (fun i j => ⟨le_rfl, hJ i j⟩) x₀ hx₀ i
    exact this.1.trans this.2
  refine ⟨fun j => xhi j - xlo j, fun j => sub_pos.2 (hw j), fun i => ?_⟩
  rw [compMat_mulVec_apply (fun i j => min |Jlo i j| |Jhi i j|)
    (fun i j => max |Jlo i j| |Jhi i j|)]
  -- the row of `J` with the smallest diagonal and the largest off-diagonal magnitudes
  let r : Fin n → ℝ := fun b => if b = i then (if |Jlo i i| ≤ |Jhi i i| then Jlo i i else Jhi i i)
    else (if |Jhi i b| ≤ |Jlo i b| then Jlo i b else Jhi i b)
  have hr : ∀ b, r b ∈ Icc (Jlo i b) (Jhi i b) := fun b => by
    by_cases hb : b = i
    · subst hb
      simp only [r, if_pos rfl]
      split_ifs
      exacts [⟨le_rfl, hJ _ _⟩, ⟨hJ _ _, le_rfl⟩]
    · simp only [r, if_neg hb]
      split_ifs
      exacts [⟨le_rfl, hJ _ _⟩, ⟨hJ _ _, le_rfl⟩]
  -- its diagonal entry has the mignitude, the others the magnitudes
  have hrd : |r i| = min |Jlo i i| |Jhi i i| := by
    simp only [r, if_pos rfl]
    split_ifs with hc
    · exact (min_eq_left hc).symm
    · exact (min_eq_right (le_of_not_ge hc)).symm
  have hro : ∀ b, b ≠ i → |r b| = max |Jlo i b| |Jhi i b| := fun b hb => by
    simp only [r, if_neg hb]
    split_ifs with hc
    · exact (max_eq_left hc).symm
    · exact (max_eq_right (le_of_not_ge hc)).symm
  -- and the diagonal entry is nonzero, as `0 ∉ Jᵢᵢ`
  have hr0 : r i ≠ 0 := fun h0 => hdiag i (h0 ▸ hr i)
  -- the two corners of `x` extremising `Σ r_j (v_j - x₀_j)`
  let vp : Fin n → ℝ := fun b => if 0 ≤ r b then xhi b else xlo b
  let vm : Fin n → ℝ := fun b => if 0 ≤ r b then xlo b else xhi b
  have hvp : vp ∈ Icc xlo xhi := ⟨fun b => by
      simp only [vp]; split_ifs
      exacts [(hw b).le, le_rfl], fun b => by
      simp only [vp]; split_ifs
      exacts [le_rfl, (hw b).le]⟩
  have hvm : vm ∈ Icc xlo xhi := ⟨fun b => by
      simp only [vm]; split_ifs
      exacts [le_rfl, (hw b).le], fun b => by
      simp only [vm]; split_ifs
      exacts [(hw b).le, le_rfl]⟩
  -- the real matrix: row `i` is `r`
  let J : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => if a = i then r b else Jlo a b
  have hJmem : ∀ a b, J a b ∈ Icc (Jlo a b) (Jhi a b) := fun a b => by
    simp only [J, Matrix.of_apply]
    split_ifs with ha
    · subst ha; exact hr b
    · exact ⟨le_rfl, hJ a b⟩
  have hJi : ∀ b, J i b = r b := fun b => by simp [J]
  have hp := h (f x₀) hy J hJmem vp hvp i
  have hq := h (f x₀) hy J hJmem vm hvm i
  simp only [sub_self, zero_sub, hJi] at hp hq
  -- the difference of the two sums is `Σ |r_j| wid_j`
  have hdiff : ∑ j ∈ univ.erase i, r j * (vp j - x₀ j) - ∑ j ∈ univ.erase i, r j * (vm j - x₀ j)
      = ∑ j ∈ univ.erase i, max |Jlo i j| |Jhi i j| * (xhi j - xlo j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← hro j (Finset.ne_of_mem_erase hj)]
    simp only [vp, vm]
    split_ifs with hc
    · rw [abs_of_nonneg hc]; ring
    · rw [abs_of_neg (not_le.mp hc)]; ring
  -- both points lie in `(xlo_i, xhi_i)`, so they differ by less than its width
  have hlt : |(∑ j ∈ univ.erase i, r j * (vp j - x₀ j) - ∑ j ∈ univ.erase i, r j * (vm j - x₀ j))
      / r i| < xhi i - xlo i := by
    have : x₀ i + (-(∑ j ∈ univ.erase i, r j * (vm j - x₀ j))) / r i
        - (x₀ i + (-(∑ j ∈ univ.erase i, r j * (vp j - x₀ j))) / r i)
        = (∑ j ∈ univ.erase i, r j * (vp j - x₀ j) - ∑ j ∈ univ.erase i, r j * (vm j - x₀ j))
          / r i := by field_simp; ring
    rw [← this, abs_lt]
    constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
  rw [hdiff, abs_div, abs_of_nonneg (Finset.sum_nonneg fun j _ =>
    mul_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) (sub_nonneg.2 (hw j).le)),
    div_lt_iff₀ (abs_pos.2 hr0), hrd] at hlt
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
