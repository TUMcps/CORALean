module

public import CORALean.ContSet.Zonotope.Real.Operations.BisectLowPrinted
public import CORALean.ContSet.Zonotope.Real.Theorems.CrossPosOfArgLt
public import CORALean.ContSet.Zonotope.Real.Theorems.CrossNonnegOfArgLe

@[expose] public section

/-!
# [1, Alg. 4] with "smaller" in the printed order returns the other boundary

For `c = 0`, `g₁ = (-2, 1)`, `g₂ = (-1, 2)` and `γ = -1` the zonogon has the vertices `(3, -3)`,
`(-1, -1)`, `(-3, 3)`, `(1, 1)`, so the lowest point of the section by `x = γ` is `(-1, -1)`.
`bisectLow` returns `-1`; the printed order of line 16 takes `g₂` as the smaller half, follows
the chord `[(3, -3); (1, 1)]`, which misses the line, and ends on the edge `[(1, 1); (-3, 3)]`
at `(-1, 2)`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed bisection gives 2 where the least value is -1

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems Reachability
      Analysis". Hybrid Systems: Computation and Control, 2008.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The angle of the pivot `(-6, 6)` against the generators `(-2, 1)` and `(-1, 2)`: the printed
order has `g₂` below the pivot and `g₁` above it. -/
private theorem Zonotope.aux_bisect_args : -- --- CONCL ---
    Complex.arg ⟨-1, 2⟩ < Complex.arg ⟨-6, 6⟩ ∧
      ¬ Complex.arg ⟨-2, 1⟩ < Complex.arg ⟨-6, 6⟩ := by -- --- PROOF ---
  constructor
  · by_contra h
    have := Zonotope.cross_nonneg_of_arg_le (u := ![-6, 6]) (w := ![-1, 2]) (by norm_num)
      (not_lt.mp h)
    norm_num at this
  · intro h
    have := Zonotope.cross_pos_of_arg_lt (u := ![-2, 1]) (w := ![-6, 6]) (by norm_num)
      (by norm_num) (by simp [funext_iff, Fin.forall_fin_two])
      (by simp [funext_iff, Fin.forall_fin_two]) h
    norm_num at this

/-- The converse comparisons, `Complex.arg ⟨-6, 6⟩ < Complex.arg ⟨-2, 1⟩` and not for `g₂`. -/
private theorem Zonotope.aux_bisect_args' : -- --- CONCL ---
    Complex.arg ⟨-6, 6⟩ < Complex.arg ⟨-2, 1⟩ ∧
      ¬ Complex.arg ⟨-6, 6⟩ < Complex.arg ⟨-1, 2⟩ := by -- --- PROOF ---
  constructor
  · by_contra h
    have := Zonotope.cross_nonneg_of_arg_le (u := ![-2, 1]) (w := ![-6, 6]) (by norm_num)
      (not_lt.mp h)
    norm_num at this
  · intro h
    have := Zonotope.cross_pos_of_arg_lt (u := ![-6, 6]) (w := ![-1, 2]) (by norm_num)
      (by norm_num) (by simp [funext_iff, Fin.forall_fin_two])
      (by simp [funext_iff, Fin.forall_fin_two]) h
    norm_num at this


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.bisectLowPrinted_counterexample : -- --- CONCL ---
    (⟨2, 0, ![![-2, 1], ![-1, 2]]⟩ : Zonotope (Vec ℝ 2)).bisectLow (-1) = -1 ∧
    (⟨2, 0, ![![-2, 1], ![-1, 2]]⟩ : Zonotope (Vec ℝ 2)).bisectLowPrinted (-1) =
      2 := by -- --- PROOF ---
  have hup : (⟨2, 0, ![![-2, 1], ![-1, 2]]⟩ : Zonotope (Vec ℝ 2)).pointUp
      = ⟨2, 0, ![![-2, 1], ![-1, 2]]⟩ := by
    unfold Zonotope.pointUp
    congr
    funext i
    fin_cases i <;> norm_num
  obtain ⟨ha, hb⟩ := Zonotope.aux_bisect_args
  obtain ⟨ha', hb'⟩ := Zonotope.aux_bisect_args'
  set Z0 : Zonotope (Vec ℝ 2) := ⟨2, 0, ![![-2, 1], ![-1, 2]]⟩ with hZ0
  -- next step of the computation
  have hP : Z0.c - ∑ i, Z0.G i = ![3, -3] := by
    show (0 : Vec ℝ 2) - ∑ i : Fin 2, (![![-2, 1], ![-1, 2]] : Fin 2 → Vec ℝ 2) i = _
    ext i
    fin_cases i <;> norm_num [Fin.sum_univ_two]
  have hdec : decide ((![3, -3] : Vec ℝ 2) 0 < -1) = false := by norm_num
  have hGl : (Finset.univ.filter fun i : Fin Z0.h => Z0.G i 0 < 0) = Finset.univ := by
    ext i
    fin_cases i <;> norm_num [Z0]
  have hit : ∀ {α : Type} (f : α → α) (x : α), f^[Z0.h] x = f (f x) := fun _ _ => rfl
  have hs : ∑ i ∈ (Finset.univ : Finset (Fin Z0.h)), (2 : ℝ) • Z0.G i = ![-6, 6] := by
    show ∑ i : Fin 2, (2 : ℝ) • (![![-2, 1], ![-1, 2]] : Fin 2 → Vec ℝ 2) i = _
    ext i
    fin_cases i <;> norm_num [Fin.sum_univ_two]
  -- next step of the computation
  have hseg : ∀ (P d : Vec ℝ 2) (y : ℝ), (![-1, y] : Vec ℝ 2) ∈ segment ℝ P (P + d) ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ P 0 + t * d 0 = -1 ∧ P 1 + t * d 1 = y := by
    intro P d y
    rw [segment_eq_image']
    constructor
    · rintro ⟨t, ⟨h0, h1⟩, ht⟩
      refine ⟨t, h0, h1, ?_, ?_⟩
      · have := congrFun ht 0
        simpa using this
      · have := congrFun ht 1
        simpa using this
    -- next step of the computation
    · rintro ⟨t, h0, h1, hx, hy⟩
      refine ⟨t, ⟨h0, h1⟩, ?_⟩
      ext i
      fin_cases i
      · simpa using hx
      · simpa using hy
  constructor
  · unfold Zonotope.bisectLow
    generalize hZ : Z0.pointUp = Zp
    obtain rfl : Zp = Z0 := hZ.symm.trans hup
    dsimp only
    -- next step of the computation
    rw [hP, hdec]
    simp only [Bool.false_eq_true, if_false, hGl, hs, hit]
    have h1 : Z0.bisectStep (-1) false (![3, -3], Finset.univ, ![-6, 6])
        = (![3, -3], {0}, ![-4, 2]) := by
      -- the pivot splits the generators: only `g₁` is above it in the walk's order
      have hf : (Finset.univ.filter fun i : Fin Z0.h =>
          Complex.arg ⟨(![-6, 6] : Vec ℝ 2) 0, (![-6, 6] : Vec ℝ 2) 1⟩ <
            Complex.arg ⟨Z0.G i 0, Z0.G i 1⟩) = {0} := by
        ext i
        fin_cases i
        · simpa [Z0] using ha'
        · simpa [Z0] using hb'
      have hsp : Z0.splitPivot false Finset.univ ![-6, 6] = ({0}, Finset.univ \ {0}) := by
        unfold Zonotope.splitPivot
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [hf, Finset.singleton_nonempty, ↓reduceIte]
      have h2 : 1 < (Finset.univ : Finset (Fin Z0.h)).card := by simp [Z0]
      have h3 : (2 : ℝ) • Z0.G 0 = ![-4, 2] := by
        ext i
        fin_cases i <;> norm_num [Z0]
      have h4 : (segment ℝ (![3, -3] : Vec ℝ 2) (![3, -3] + ![-4, 2]) ∩
          {z | z 0 = -1}).Nonempty := by
        refine ⟨![-1, -1], ?_, by simp⟩
        rw [hseg]
        exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      -- the chord of `g₁` meets the line, so the pass keeps the lower half
      unfold Zonotope.bisectStep
      rw [hsp]
      dsimp only
      rw [if_pos h2, Finset.sum_singleton, h3, if_pos h4]
    -- next step of the computation
    have h2 : Z0.bisectStep (-1) false (![3, -3], {0}, ![-4, 2]) = (![3, -3], {0}, ![-4, 2]) := by
      simp [Zonotope.bisectStep]
    rw [h1, h2]
    have : {y : ℝ | (![-1, y] : Vec ℝ 2) ∈ segment ℝ (![3, -3] : Vec ℝ 2) (![3, -3] + ![-4, 2])}
        = {-1} := by
      ext y
      simp only [hseg, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨t, h0, h1, hx, hy⟩
        simp at hx hy
        linarith
      · rintro rfl
        exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    -- next step of the computation
    simp only [this, csInf_singleton]
  · unfold Zonotope.bisectLowPrinted
    generalize hZ : Z0.pointUp = Zp
    obtain rfl : Zp = Z0 := hZ.symm.trans hup
    dsimp only
    rw [hP, hdec]
    have hf : (Finset.univ.filter fun i : Fin Z0.h =>
        Complex.arg ⟨Z0.G i 0, Z0.G i 1⟩ <
          Complex.arg ⟨(![-6, 6] : Vec ℝ 2) 0, (![-6, 6] : Vec ℝ 2) 1⟩) = {1} := by
      ext i
      fin_cases i
      · simpa [Z0] using hb
      · simpa [Z0] using ha
    -- next step of the computation
    have hsp : Z0.splitPivot true Finset.univ ![-6, 6] = ({1}, Finset.univ \ {1}) := by
      unfold Zonotope.splitPivot
      simp only [↓reduceIte]
      simp only [hf, Finset.singleton_nonempty, ↓reduceIte]
    have h2 : 1 < (Finset.univ : Finset (Fin Z0.h)).card := by simp [Z0]
    have h3 : (2 : ℝ) • Z0.G 1 = ![-2, 4] := by
      ext i
      fin_cases i <;> norm_num [Z0]
    have h4 : ¬ (segment ℝ (![3, -3] : Vec ℝ 2) (![3, -3] + ![-2, 4]) ∩
        {z | z 0 = -1}).Nonempty := by
      rintro ⟨z, hz, hz0⟩
      obtain ⟨t, h0, h1, hx⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 3 + t * (-2) = -1 := by
        rw [segment_eq_image'] at hz
        obtain ⟨t, ⟨h0, h1⟩, rfl⟩ := hz
        exact ⟨t, h0, h1, by simpa using hz0⟩
      linarith
    -- next step of the computation
    have h5 : (Finset.univ \ {1} : Finset (Fin Z0.h)).card = 1 := by
      rw [Finset.card_sdiff_of_subset (by simp)]
      simp [Z0]
    have h6 : Z0.bisectStep (-1) true (![3, -3], Finset.univ, ![-6, 6])
        = (![3, -3] + ![-2, 4], Finset.univ \ {1}, ![-4, 2]) := by
      unfold Zonotope.bisectStep
      rw [hsp]
      dsimp only
      rw [if_pos h2, Finset.sum_singleton, h3, if_neg h4]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      ext i
      fin_cases i <;> norm_num
    -- next step of the computation
    have h7 : Z0.bisectStep (-1) true (![3, -3] + ![-2, 4], Finset.univ \ {1}, ![-4, 2])
        = (![3, -3] + ![-2, 4], Finset.univ \ {1}, ![-4, 2]) := by
      unfold Zonotope.bisectStep
      simp only [h5, lt_self_iff_false, if_false]
    simp only [Bool.false_eq_true, if_false, hGl, hs]
    rw [hit, h6, h7]
    have : {y : ℝ | (![-1, y] : Vec ℝ 2) ∈ segment ℝ (![3, -3] + ![-2, 4] : Vec ℝ 2)
        (![3, -3] + ![-2, 4] + ![-4, 2])} = {2} := by
      ext y
      simp only [hseg, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨t, h0, h1, hx, hy⟩
        simp at hx hy
        linarith
      · rintro rfl
        exact ⟨1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩
    -- next step of the computation
    simp only [this, csInf_singleton]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
