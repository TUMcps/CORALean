import CORALean.ContSet.ConZonotope.Real.Theorems.TightenOuter

/-!
# `ConZonotope.tighten` is sound at a dependency-closed set of coordinates

`tighten_outer` needs the *whole* box `∀ j, |β j| ≤ 1`: Algorithm 1's Gauss-Seidel
pass lets a row's bound on one coefficient read every other, so a coordinate left
out of the box hypothesis can corrupt the bound derived for any coordinate whose
row happens to read it — and from there, transitively, any coordinate reading
*that* one. `[1, Thm. 2]`'s own `⊆` direction needs the opposite: soundness at
every coordinate but the one being eliminated, with no hypothesis on that one at
all, which the corruption above makes false in general (see the page's
`## Findings` for a matrix witnessing it).

What survives is soundness restricted to a set `S` closed under "what a row reads
when it touches a coordinate in `S`": for every `j ∈ S` and row `i` with
`a_{i,j} ≠ 0`, every other column `l` that row reads (`a_{i,l} ≠ 0`) is also in
`S`. `aux_tightenCoeff_outer_safe` and `aux_tightenRow_outer_safe` are
`aux_tightenCoeff_outer`/`aux_tightenRow_outer` restricted to `S` this way;
`tighten_outer_safe` carries it across every row, exactly as `tighten_outer` does.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Row `i`'s bound on a coordinate `j ∈ S` is sound, given the running box only at
coordinates in `S` and `S` closed under what row `i` (or any earlier row) reads
from a coordinate of `S`. -/
theorem ConZonotope.aux_tightenCoeff_outer_safe {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (S : Set (Fin ng))
    (hclosed : ∀ j ∈ S, ∀ i : Fin nc, A i j ≠ 0 → ∀ l : Fin ng, l ≠ j → A i l ≠ 0 → l ∈ S)
    (i : Fin nc) (j : Fin ng) {E : Interval (Vec ℝ ng)} {β : Vec ℝ ng}
    (hβS : ∀ k ∈ S, E.inf k ≤ β k ∧ β k ≤ E.sup k) (hrow : (A *ᵥ β) i = b i) :
    ∀ k ∈ S, (ConZonotope.tightenCoeff A b i j E).inf k ≤ β k ∧
        β k ≤ (ConZonotope.tightenCoeff A b i j E).sup k := by -- --- PROOF ---
  intro k hkS
  unfold ConZonotope.tightenCoeff
  split_ifs with h0
  · exact hβS k hkS
  · rcases eq_or_ne k j with rfl | hne
    · -- the tightened coordinate: `k ∈ S`, so `hclosed` reaches every coordinate row `i` reads
      show Function.update E.inf k (max (E.inf k)
            (min (ConZonotope.rowBound A b i k E).1 (ConZonotope.rowBound A b i k E).2)) k
            ≤ β k
          ∧ β k ≤ Function.update E.sup k (min (E.sup k)
            (max (ConZonotope.rowBound A b i k E).1 (ConZonotope.rowBound A b i k E).2)) k
      rw [Function.update_self, Function.update_self]
      obtain ⟨hbin, hbsup⟩ := hβS k hkS
      have hR1 : (ConZonotope.rowBound A b i k E).1
          = (b i - ∑ l ∈ Finset.univ.erase k, max (A i l * E.inf l) (A i l * E.sup l)) / A i k :=
        rfl
      have hR2 : (ConZonotope.rowBound A b i k E).2
          = (b i - ∑ l ∈ Finset.univ.erase k, min (A i l * E.inf l) (A i l * E.sup l)) / A i k :=
        rfl
      -- outside `S` a term only enters with a zero coefficient: `hclosed` catches the rest
      have hS1 : (∑ l ∈ Finset.univ.erase k, min (A i l * E.inf l) (A i l * E.sup l))
          ≤ ∑ l ∈ Finset.univ.erase k, A i l * β l := by
        apply Finset.sum_le_sum
        intro l hl
        rcases eq_or_ne (A i l) 0 with h1 | h1
        · simp [h1]
        · have hlS := hclosed k hkS i h0 l (Finset.ne_of_mem_erase hl) h1
          exact (Interval.mul_between_endpoints (hβS l hlS).1 (hβS l hlS).2).1
      have hS2 : (∑ l ∈ Finset.univ.erase k, A i l * β l)
          ≤ ∑ l ∈ Finset.univ.erase k, max (A i l * E.inf l) (A i l * E.sup l) := by
        apply Finset.sum_le_sum
        intro l hl
        rcases eq_or_ne (A i l) 0 with h1 | h1
        · simp [h1]
        · have hlS := hclosed k hkS i h0 l (Finset.ne_of_mem_erase hl) h1
          exact (Interval.mul_between_endpoints (hβS l hlS).1 (hβS l hlS).2).2
      -- row `i` of `Aβ = b`, split at coordinate `k`
      have hrow' : A i k * β k + ∑ l ∈ Finset.univ.erase k, A i l * β l = b i := by
        rw [Finset.add_sum_erase Finset.univ (fun l => A i l * β l) (Finset.mem_univ k),
          ← hrow, Matrix.mulVec_apply_eq_sum]
      have h1 : b i - (∑ l ∈ Finset.univ.erase k, max (A i l * E.inf l) (A i l * E.sup l))
          ≤ A i k * β k := by linarith
      have h2 : A i k * β k
          ≤ b i - (∑ l ∈ Finset.univ.erase k, min (A i l * E.inf l) (A i l * E.sup l)) := by
        linarith
      -- solve back for `βk` itself, then meet the box already known around it
      rw [hR1, hR2]
      obtain ⟨hlo, hhi⟩ := Interval.div_between_endpoints h0 h1 h2
      exact ⟨max_le hbin hlo, le_min hbsup hhi⟩
    · show Function.update E.inf j (max (E.inf j)
              (min (ConZonotope.rowBound A b i j E).1 (ConZonotope.rowBound A b i j E).2)) k
            ≤ β k
          ∧ β k ≤ Function.update E.sup j (min (E.sup j)
              (max (ConZonotope.rowBound A b i j E).1 (ConZonotope.rowBound A b i j E).2)) k
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact hβS k hkS

/-- Every row of `Aξ = b`, applied in turn, still leaves a feasible coefficient
inside the running box at every coordinate of `S`. -/
theorem ConZonotope.aux_tightenRow_outer_safe {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (S : Set (Fin ng))
    (hclosed : ∀ j ∈ S, ∀ i : Fin nc, A i j ≠ 0 → ∀ l : Fin ng, l ≠ j → A i l ≠ 0 → l ∈ S)
    (i : Fin nc) {E : Interval (Vec ℝ ng)} {β : Vec ℝ ng}
    (hβS : ∀ k ∈ S, E.inf k ≤ β k ∧ β k ≤ E.sup k) (hrow : (A *ᵥ β) i = b i) :
    ∀ k ∈ S, (ConZonotope.tightenRow A b i E).inf k ≤ β k ∧
        β k ≤ (ConZonotope.tightenRow A b i E).sup k := by
  unfold ConZonotope.tightenRow
  exact Fin.foldl_induction (P := fun y => ∀ k ∈ S, y.inf k ≤ β k ∧ β k ≤ y.sup k) ng
    (fun E j => ConZonotope.tightenCoeff A b i j E) E hβS
    fun _ j hy => ConZonotope.aux_tightenCoeff_outer_safe A b S hclosed i j hy hrow


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]'s soundness, restricted to a dependency-closed set of coordinates
`S`: given only `|β j| ≤ 1` for `j ∈ S` (nothing assumed at any coordinate outside
`S`) and `Aβ = b`, every `k ∈ S` lands in `tighten`'s bound at `k`. -/
theorem ConZonotope.tighten_outer_safe {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (S : Set (Fin ng))
    (hclosed : ∀ j ∈ S, ∀ i : Fin nc, A i j ≠ 0 → ∀ l : Fin ng, l ≠ j → A i l ≠ 0 → l ∈ S)
    {β : Vec ℝ ng} (hbox : ∀ j ∈ S, |β j| ≤ 1) (heq : ∀ i, (A *ᵥ β) i = b i) :
    ∀ k ∈ S, (ConZonotope.tighten A b).inf k ≤ β k ∧
        β k ≤ (ConZonotope.tighten A b).sup k := by -- --- PROOF ---
  unfold ConZonotope.tighten
  have hE₀ : ∀ k ∈ S, (⟨fun _ => -1, fun _ => 1⟩ : Interval (Vec ℝ ng)).inf k ≤ β k ∧
      β k ≤ (⟨fun _ => -1, fun _ => 1⟩ : Interval (Vec ℝ ng)).sup k :=
    fun k hk => abs_le.mp (hbox k hk)
  exact Fin.foldl_induction (P := fun y => ∀ k ∈ S, y.inf k ≤ β k ∧ β k ≤ y.sup k) nc
    (fun E i => ConZonotope.tightenRow A b i E) _ hE₀
    fun _ i hE => ConZonotope.aux_tightenRow_outer_safe A b S hclosed i hE (heq i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
