import CORALean.ContSet.ConZonotope.Real.Operations.Eliminate
import CORALean.ContSet.ConZonotope.Real.Operations.MemOfMatIff
import CORALean.ContSet.ConZonotope.Real.Theorems.TightenOuterSafe
import CORALean.ContSet.Interval.Real.Theorems.DivBetweenEndpoints
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenEndpoints
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# `ConZonotope.eliminate`, exactly — under the closure [1, Thm. 2]'s own proof uses

`Thm. 2` states an identity, `Zc = Zr`, from `a_{r,j} ≠ 0` and `R_{r,j} ⊆ [-1,1]` (eq. 12,
at `E_k` from a full run of Algorithm 1 on `Zc`) alone. Its `⊇` direction is exactly those
facts run through the substitution algebra — `aux_eliminate_subset` below. Its `⊆`
direction solves row `r` for `ξ_j` from the *other* coordinates and bounds that solution by
`[-1,1]` only if those other coordinates are already known inside their own `E_k`, not
merely `[-1,1]`; the paper never says why they are, and its procedural remark — full-pivoted
Gauss-Jordan before Algorithm 1 — is never connected back to the proof (see the page's
`## Findings` for the counterexample showing the bound is false without some such
condition).

`hclosed`/`hjS`/`hrS` name that condition directly, in `tighten_outer_safe`'s own
`S`-closure shape: the coordinates row `r` reads besides `j` sit in `S`, `j` itself
excluded, closed under what every row reads from `S`. Given that, `tighten_outer_safe`
bounds every coordinate of `S` inside `tighten A b`, and row `r`'s own sandwich
(`aux_rowBound_dep`) bounds `ξ_j` between `rowBound`'s endpoints from those — landing it
inside `[-1,1]` exactly where `R_{r,j} ⊆ [-1,1]` says.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Tobias Ladner
-- Written:       21-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Row `r`'s equation, solved for coefficient `j` from the running box at every other
coordinate it reads, sandwiches `β j` between `rowBound`'s two endpoints — `tightenCoeff`'s
own tightening step, run once directly. -/
theorem ConZonotope.aux_rowBound_dep {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (S : Set (Fin ng)) (r : Fin nc) (j : Fin ng)
    (hSread : ∀ l, l ≠ j → A r l ≠ 0 → l ∈ S) {E : Interval (Vec ℝ ng)}
    {β : Vec ℝ ng} (hβS : ∀ k ∈ S, E.inf k ≤ β k ∧ β k ≤ E.sup k)
    (hAj : A r j ≠ 0) (hrow : (A *ᵥ β) r = b r) :
    min (ConZonotope.rowBound A b r j E).1 (ConZonotope.rowBound A b r j E).2 ≤ β j ∧
      β j ≤ max (ConZonotope.rowBound A b r j E).1
        (ConZonotope.rowBound A b r j E).2 := by -- --- PROOF ---
  have hR1 : (ConZonotope.rowBound A b r j E).1
      = (b r - ∑ l ∈ Finset.univ.erase j, max (A r l * E.inf l) (A r l * E.sup l))
        / A r j := rfl
  have hR2 : (ConZonotope.rowBound A b r j E).2
      = (b r - ∑ l ∈ Finset.univ.erase j, min (A r l * E.inf l) (A r l * E.sup l))
        / A r j := rfl
  -- outside `S` a term only enters with a zero coefficient: `hSread` catches the rest
  have hS1 : (∑ l ∈ Finset.univ.erase j, min (A r l * E.inf l) (A r l * E.sup l))
      ≤ ∑ l ∈ Finset.univ.erase j, A r l * β l := by
    apply Finset.sum_le_sum
    intro l hl
    rcases eq_or_ne (A r l) 0 with h1 | h1
    · simp [h1]
    · exact (Interval.mul_between_endpoints
        (hβS l (hSread l (Finset.ne_of_mem_erase hl) h1)).1
        (hβS l (hSread l (Finset.ne_of_mem_erase hl) h1)).2).1
  have hS2 : (∑ l ∈ Finset.univ.erase j, A r l * β l)
      ≤ ∑ l ∈ Finset.univ.erase j, max (A r l * E.inf l) (A r l * E.sup l) := by
    apply Finset.sum_le_sum
    intro l hl
    rcases eq_or_ne (A r l) 0 with h1 | h1
    · simp [h1]
    · exact (Interval.mul_between_endpoints
        (hβS l (hSread l (Finset.ne_of_mem_erase hl) h1)).1
        (hβS l (hSread l (Finset.ne_of_mem_erase hl) h1)).2).2
  -- row `r` of `Aβ = b`, split at coordinate `j`
  have hrow' : A r j * β j + ∑ l ∈ Finset.univ.erase j, A r l * β l = b r := by
    rw [Finset.add_sum_erase Finset.univ (fun l => A r l * β l) (Finset.mem_univ j),
      ← hrow, Matrix.mulVec_apply_eq_sum]
  have h1 : b r - (∑ l ∈ Finset.univ.erase j, max (A r l * E.inf l) (A r l * E.sup l))
      ≤ A r j * β j := by linarith
  have h2 : A r j * β j
      ≤ b r - (∑ l ∈ Finset.univ.erase j, min (A r l * E.inf l) (A r l * E.sup l)) := by
    linarith
  rw [hR1, hR2]
  exact Interval.div_between_endpoints hAj h1 h2

/-- The value identity behind `eliminate`: the centre and generator `j`'s term, read
either from the original system (`t = β j`) or from any `t` solving row `r` the same
way — both directions below read this once each way. -/
theorem ConZonotope.aux_eliminate_value {ng nc : ℕ} (c : α) (G : Fin ng → α)
    (A : Mat ℝ nc ng) (b : Vec ℝ nc) (r : Fin nc) (j : Fin ng) (hAj : A r j ≠ 0)
    (β' : Fin (ng - 1) → ℝ) (t : ℝ)
    (ht : A r j * t = b r - ∑ i, A r (dropIdx j i) * β' i) :
    c + t • G j + ∑ i, β' i • G (dropIdx j i)
      = (c + b r • ((A r j)⁻¹ • G j))
        + ∑ i, β' i •
            (G (dropIdx j i) - A r (dropIdx j i) • ((A r j)⁻¹ • G j)) := by -- --- PROOF ---
  set ΛG : α := (A r j)⁻¹ • G j with hΛGdef
  have hGj : A r j • ΛG = G j := by rw [hΛGdef, smul_smul, mul_inv_cancel₀ hAj, one_smul]
  have hval : (A r j * t) • ΛG = t • G j := by rw [mul_comm, ← smul_smul, hGj]
  have hcomb2 : b r • ΛG - (∑ i, A r (dropIdx j i) * β' i) • ΛG = t • G j := by
    rw [← sub_smul, ← ht]; exact hval
  have hdistrib : ∑ i, β' i • (G (dropIdx j i) - A r (dropIdx j i) • ΛG)
      = (∑ i, β' i • G (dropIdx j i)) - (∑ i, A r (dropIdx j i) * β' i) • ΛG := by
    have hterm : ∀ i, β' i • (G (dropIdx j i) - A r (dropIdx j i) • ΛG)
        = β' i • G (dropIdx j i) - (A r (dropIdx j i) * β' i) • ΛG := fun i => by
      rw [smul_sub, smul_smul, mul_comm]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [hdistrib, ← hcomb2]
  abel

/-- The row identity behind `eliminate`: row `i` with coefficient `j` read off as `t`
equals the reduced system's corrected row at `i`, plus what `Λ_A`'s row gives back —
unconditional, given only how `t` solves row `r`. -/
theorem ConZonotope.aux_eliminate_row {ng nc : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (r : Fin nc) (j : Fin ng) (hAj : A r j ≠ 0) (i : Fin nc) (β' : Fin (ng - 1) → ℝ)
    (t : ℝ) (ht : A r j * t = b r - ∑ l, A r (dropIdx j l) * β' l) :
    A i j * t + ∑ l, A i (dropIdx j l) * β' l
      = (∑ l, (A i (dropIdx j l) - A i j * (A r j)⁻¹ * A r (dropIdx j l)) * β' l)
        + A i j * (A r j)⁻¹ * b r := by -- --- PROOF ---
  have hsum : ∑ l, (A i (dropIdx j l) - A i j * (A r j)⁻¹ * A r (dropIdx j l)) * β' l
      = ∑ l, A i (dropIdx j l) * β' l
        - A i j * (A r j)⁻¹ * ∑ l, A r (dropIdx j l) * β' l := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hAr : ∑ l, A r (dropIdx j l) * β' l = b r - A r j * t := by linarith [ht]
  rw [hsum, hAr]
  field_simp
  ring

/-- `Zc ⊆ Zr`: every feasible `β` of the original system restricts, at every column but
`j`, to a feasible point of the eliminated one — routine algebra, needing only
`a_{r,j} ≠ 0`. -/
theorem ConZonotope.aux_eliminate_subset {ng nc : ℕ} (c : α) (G : Fin ng → α)
    (A : Mat ℝ nc ng) (b : Vec ℝ nc) (r : Fin nc) (j : Fin ng) (hAj : A r j ≠ 0) :
    (ConZonotope.ofMat c G A b).construct
      ⊆ (ConZonotope.eliminate c G A b r j).construct := by -- --- PROOF ---
  intro x hx
  rw [ConZonotope.mem_ofMat_iff] at hx
  obtain ⟨β, hβbox, hβeq, hx⟩ := hx
  have hsplitA : ∀ i : Fin nc,
      (A *ᵥ β) i
        = A i j * β j + ∑ l : Fin (ng - 1), A i (dropIdx j l) * β (dropIdx j l) := by
    intro i
    rw [Matrix.mulVec_apply_eq_sum]
    exact sum_dropIdx j (fun l => A i l * β l)
  have ht : A r j * β j = b r - ∑ l : Fin (ng - 1), A r (dropIdx j l) * β (dropIdx j l) := by
    have := hsplitA r; rw [hβeq r] at this; linarith
  -- `β` restricted off column `j` is the reduced system's witness
  simp only [ConZonotope.eliminate, ConZonotope.mem_ofMat_iff]
  refine ⟨β ∘ dropIdx j, fun i => hβbox (dropIdx j i), ?_, ?_⟩
  · -- every surviving row, read off `aux_eliminate_row` at `t = β j`
    show ∀ i : Fin (nc - 1), ∑ l : Fin (ng - 1),
        (A (dropIdx r i) (dropIdx j l) - A (dropIdx r i) j * (A r j)⁻¹ * A r (dropIdx j l))
          * β (dropIdx j l)
        = b (dropIdx r i) - A (dropIdx r i) j * (A r j)⁻¹ * b r
    intro i
    have hrow :=
      ConZonotope.aux_eliminate_row A b r j hAj (dropIdx r i) (β ∘ dropIdx j) (β j) ht
    simp only [Function.comp_apply] at hrow
    have hi := hsplitA (dropIdx r i)
    rw [hβeq (dropIdx r i)] at hi
    linarith [hrow, hi]
  · -- the value: `aux_eliminate_value` at `t = β j`, then `x` split the same way
    show x = (c + b r • ((A r j)⁻¹ • G j))
        + ∑ i : Fin (ng - 1), (β ∘ dropIdx j) i
            • (G (dropIdx j i) - A r (dropIdx j i) • ((A r j)⁻¹ • G j))
    rw [← ConZonotope.aux_eliminate_value c G A b r j hAj (β ∘ dropIdx j) (β j) ht]
    show x = c + β j • G j + ∑ i : Fin (ng - 1), β (dropIdx j i) • G (dropIdx j i)
    rw [hx, sum_dropIdx j (fun l => β l • G l)]
    abel

/-- `Zr ⊆ Zc`: given the dependency-closed `S` `Thm. 2`'s own proof needs, a feasible
point of the eliminated system extends back to a feasible point of the original one —
row `r`'s solved-for coefficient lands in `[-1,1]` via `aux_rowBound_dep` and `hR`. -/
theorem ConZonotope.aux_eliminate_superset {ng nc : ℕ} (c : α) (G : Fin ng → α)
    (A : Mat ℝ nc ng) (b : Vec ℝ nc) (r : Fin nc) (j : Fin ng) (hAj : A r j ≠ 0)
    (S : Set (Fin ng)) (hjS : j ∉ S) (hrS : ∀ l, l ≠ j → A r l ≠ 0 → l ∈ S)
    (hclosed : ∀ k ∈ S, ∀ i : Fin nc, A i k ≠ 0 →
      ∀ l : Fin ng, l ≠ k → A i l ≠ 0 → l ∈ S)
    (hR : -1 ≤ min (ConZonotope.rowBound A b r j (ConZonotope.tighten A b)).1
              (ConZonotope.rowBound A b r j (ConZonotope.tighten A b)).2 ∧
          max (ConZonotope.rowBound A b r j (ConZonotope.tighten A b)).1
              (ConZonotope.rowBound A b r j (ConZonotope.tighten A b)).2 ≤ 1) :
    (ConZonotope.eliminate c G A b r j).construct
      ⊆ (ConZonotope.ofMat c G A b).construct := by -- --- PROOF ---
  intro x hx
  -- read `hx`'s witness `β'` back in the clean, zeta-reduced sum form
  simp only [ConZonotope.eliminate, ConZonotope.mem_ofMat_iff] at hx
  obtain ⟨β', hβ'box, hβ'eq, hx⟩ := hx
  replace hβ'eq : ∀ k : Fin (nc - 1), ∑ l : Fin (ng - 1),
      (A (dropIdx r k) (dropIdx j l) - A (dropIdx r k) j * (A r j)⁻¹ * A r (dropIdx j l)) * β' l
      = b (dropIdx r k) - A (dropIdx r k) j * (A r j)⁻¹ * b r := hβ'eq
  replace hx : x = (c + b r • ((A r j)⁻¹ • G j))
      + ∑ i : Fin (ng - 1),
          β' i • (G (dropIdx j i) - A r (dropIdx j i) • ((A r j)⁻¹ • G j)) := hx
  -- `ξ_j`: row `r` of `Aβ = b`, solved for `j` from `β'` alone
  set ξc : ℝ := (b r - ∑ i : Fin (ng - 1), A r (dropIdx j i) * β' i) / A r j with hξcdef
  have ht : A r j * ξc = b r - ∑ i : Fin (ng - 1), A r (dropIdx j i) * β' i := by
    rw [hξcdef]; field_simp
  -- `β`: `β'` extended by `ξ_j` at `j` — `dropIdx`'s converse
  set β : Fin ng → ℝ := insertIdx j ξc β' with hβdef
  have hβj : β j = ξc := insertIdx_self j ξc β'
  have hβdrop : ∀ i, β (dropIdx j i) = β' i := insertIdx_dropIdx j ξc β'
  have hcase : ∀ l : Fin ng, l = j ∨ ∃ i, l = dropIdx j i :=
    (forall_dropIdx_iff j).mpr ⟨Or.inl rfl, fun i => Or.inr ⟨i, rfl⟩⟩
  -- `β` satisfies every row of `Aβ = b`: row `r` by construction, others via `aux_eliminate_row`
  have heqAll : ∀ i : Fin nc, (A *ᵥ β) i = b i := by
    rw [forall_dropIdx_iff r]
    refine ⟨?_, ?_⟩
    · show (A *ᵥ β) r = b r
      rw [Matrix.mulVec_apply_eq_sum, sum_dropIdx j (fun l => A r l * β l), hβj]
      have heach : ∀ l : Fin (ng - 1), A r (dropIdx j l) * β (dropIdx j l)
          = A r (dropIdx j l) * β' l := fun l => by rw [hβdrop]
      rw [Finset.sum_congr rfl (fun l _ => heach l)]
      linarith [ht]
    · intro k
      show (A *ᵥ β) (dropIdx r k) = b (dropIdx r k)
      have hrow := ConZonotope.aux_eliminate_row A b r j hAj (dropIdx r k) β' ξc ht
      rw [hβ'eq k] at hrow
      rw [Matrix.mulVec_apply_eq_sum, sum_dropIdx j (fun l => A (dropIdx r k) l * β l), hβj]
      have heach : ∀ l : Fin (ng - 1), A (dropIdx r k) (dropIdx j l) * β (dropIdx j l)
          = A (dropIdx r k) (dropIdx j l) * β' l := fun l => by rw [hβdrop]
      rw [Finset.sum_congr rfl (fun l _ => heach l)]
      linarith [hrow]
  rw [ConZonotope.mem_ofMat_iff]
  refine ⟨β, ?_, heqAll, ?_⟩
  · -- box: every coordinate but `j` from `β'`, `j` itself from `rowBound`'s sandwich
    rw [forall_dropIdx_iff j]
    refine ⟨?_, fun i => hβdrop i ▸ hβ'box i⟩
    have hβS : ∀ k ∈ S,
        (ConZonotope.tighten A b).inf k ≤ β k ∧ β k ≤ (ConZonotope.tighten A b).sup k := by
      have hbox : ∀ k ∈ S, |β k| ≤ 1 := by
        intro k hk
        rcases hcase k with rfl | ⟨i, rfl⟩
        · exact absurd hk hjS
        · rw [hβdrop]; exact hβ'box i
      exact ConZonotope.tighten_outer_safe A b S hclosed hbox heqAll
    have hsand := ConZonotope.aux_rowBound_dep A b S r j hrS hβS hAj (heqAll r)
    rw [abs_le]
    exact ⟨le_trans hR.1 hsand.1, le_trans hsand.2 hR.2⟩
  · -- the value: `aux_eliminate_value` at `t = ξc`, then `x` matches `β`'s own split
    rw [hx, ← ConZonotope.aux_eliminate_value c G A b r j hAj β' ξc ht, ← hβj]
    have heq2 : ∑ i : Fin (ng - 1), β' i • G (dropIdx j i)
        = ∑ i : Fin (ng - 1), β (dropIdx j i) • G (dropIdx j i) :=
      Finset.sum_congr rfl fun i _ => by rw [hβdrop]
    rw [heq2, sum_dropIdx j (fun l => β l • G l)]
    abel


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: `Zc = Zr`, under the dependency-closed hypothesis the paper's own
proof needs to cross the `⊆` direction and never states — the columns row `r` reads
besides `j` sit in a set `S`, `j` excluded, closed under what every row reads from `S`. -/
theorem ConZonotope.eliminate_exact_of_dependClosed {ng nc : ℕ} (c : α) (G : Fin ng → α)
    (A : Mat ℝ nc ng) (b : Vec ℝ nc) (r : Fin nc) (j : Fin ng) (hAj : A r j ≠ 0)
    (S : Set (Fin ng)) (hjS : j ∉ S) (hrS : ∀ l, l ≠ j → A r l ≠ 0 → l ∈ S)
    (hclosed : ∀ k ∈ S, ∀ i : Fin nc, A i k ≠ 0 →
      ∀ l : Fin ng, l ≠ k → A i l ≠ 0 → l ∈ S)
    (hR : -1 ≤ min (ConZonotope.rowBound A b r j (ConZonotope.tighten A b)).1
              (ConZonotope.rowBound A b r j (ConZonotope.tighten A b)).2 ∧
          max (ConZonotope.rowBound A b r j (ConZonotope.tighten A b)).1
              (ConZonotope.rowBound A b r j (ConZonotope.tighten A b)).2 ≤ 1) :
    (ConZonotope.ofMat c G A b).construct = (ConZonotope.eliminate c G A b r j).construct := by
  exact Set.Subset.antisymm (ConZonotope.aux_eliminate_subset c G A b r j hAj)
    (ConZonotope.aux_eliminate_superset c G A b r j hAj S hjS hrS hclosed hR)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
