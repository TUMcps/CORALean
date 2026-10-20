module

public import CORALean.NN.Layers.Definitions.WindowMax
public import CORALean.NN.Layers.Theorems.Real.Basic
public import CORALean.NN.Layers.Theorems.SelectMatMulVec
public import CORALean.NN.Operations.CatMaxSegment
public import CORALean.NN.Theorems.Basic
public import CORALean.ContSet.LevelSet.Real.Theorems.AndExact

@[expose] public section

/-!
# One max-pooling step replaces its window by the maximum

[1, Sec. II (MaxPool to CAT)]: `fᵢ` keeps the coordinates before and after its window and puts
the window's maximum in its place, and maps a point to nothing else. The case that applies is
the first position holding a maximum: its guard holds, every earlier one fails, and its
selection keeps that coordinate. A maximum exists, the window being nonempty.

## Inputs
* `a` – coordinates before the window
* `k` – window size minus one
* `b` – coordinates after the window
* `x` – input point
* `y` – output point

## Hypotheses
* none

## Conclusion
* the step maps the point to the output iff the output replaces the window by its maximum

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The guard is that `x P` dominates every `x (g q)`. -/
theorem aux_holds_foldr_ge {N : ℕ} (P : Fin N) (x : Vec ℝ N) : -- --- CONCL ---
    ∀ {j : ℕ} (g : Fin j → Fin N),
      x ∈ (Fin.foldr j (fun q acc => (CatCond.ge P (g q)).and_ acc) (CatCond.ge P P)).construct
        ↔ ∀ q, x (g q) ≤ x P := by -- --- PROOF ---
  intro j
  induction j with
  | zero => intro g; rw [Fin.foldr_zero, CatCond.mem_ge_iff]; simp
  | succ j ih =>
    intro g
    rw [Fin.foldr_succ, Real.LevelSet.and_exact, Set.mem_inter_iff, CatCond.mem_ge_iff,
      ih (fun q => g q.succ), Fin.forall_fin_succ]

/-- The selection of position `p`, read off coordinate by coordinate. -/
theorem aux_eval_select (a k b : ℕ) (p : Fin (k + 1))
    (x : Vec ℝ (a + (k + 1) + b)) : -- --- CONCL ---
    toRealMat (selectMat (𝕋 := 𝕋) fun r : Fin (a + 1 + b) =>
        (⟨if r.val < a then r.val else if r.val = a then a + p.val else r.val + k,
          by have := r.isLt; have := p.isLt; split_ifs <;> omega⟩ : Fin (a + (k + 1) + b))) *ᵥ x
      + toRealVec (fun _ => (zero : 𝕋))
      = fun r => if _h : r.val < a then x ⟨r.val, by omega⟩
          else if r.val = a then x ⟨a + p.val, by omega⟩
          else x ⟨r.val + k, by have := r.isLt; omega⟩ := by -- --- PROOF ---
  funext r
  rw [Pi.add_apply, selectMat_mulVec]
  show _ + toReal (zero : 𝕋) = _
  rw [toReal_zero, add_zero]
  split_ifs <;> rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem Cat.maxSegment_eval_iff (a k b : ℕ) (x : Vec ℝ (a + (k + 1) + b))
    (y : Vec ℝ (a + 1 + b)) : -- --- CONCL ---
    (Cat.maxSegment (𝕋 := 𝕋) a k b).Eval x y ↔
      y = fun r => if _h : r.val < a then x ⟨r.val, by omega⟩
        else if r.val = a then Real.windowMax (fun q : Fin (k + 1) => x ⟨a + q.val, by omega⟩)
        else x ⟨r.val + k, by have := r.isLt; omega⟩ := by -- --- PROOF ---
  set w : Fin (k + 1) → ℝ := fun q => x ⟨a + q.val, by omega⟩ with hw
  have hguard := fun p : Fin (k + 1) => aux_holds_foldr_ge (⟨a + p.val, by omega⟩ :
    Fin (a + (k + 1) + b)) x (fun q : Fin (k + 1) => ⟨a + q.val, by omega⟩)
  -- at a dominating position, its coordinate is the maximum
  have hmax : ∀ p, (∀ q, w q ≤ w p) → w p = Real.windowMax w := fun p hp =>
    le_antisymm (Real.le_windowMax w p) (Real.windowMax_le hp)
  constructor
  · rintro (_ | ⟨E, f, p, hp, -, hy⟩ | _)
    cases hy
    rw [aux_eval_select]
    have hp' : ∀ q, w q ≤ w p := (hguard p).mp hp
    funext r
    split_ifs with h1 h2
    · rfl
    · exact hmax p hp'
    · rfl
  · rintro rfl
    -- the first position holding a maximum
    classical
    have hex : ∃ n, ∃ h : n < k + 1, ∀ q, w q ≤ w ⟨n, h⟩ := by
      obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
      exact ⟨p.val, p.isLt, fun q => hp q (Finset.mem_univ q)⟩
    obtain ⟨hlt, hp⟩ := Nat.find_spec hex
    set p : Fin (k + 1) := ⟨Nat.find hex, hlt⟩
    refine Cat.Eval.cases _ _ p ((hguard p).mpr hp) (fun j hj hholds => ?_) ?_
    · exact Nat.find_min hex (show j.val < Nat.find hex from hj) ⟨j.isLt, (hguard j).mp hholds⟩
    · have hy := Cat.Eval.affine (selectMat (𝕋 := 𝕋) fun r : Fin (a + 1 + b) =>
        (⟨if r.val < a then r.val else if r.val = a then a + p.val else r.val + k,
          by have := r.isLt; have := p.isLt; split_ifs <;> omega⟩ : Fin (a + (k + 1) + b)))
        (fun _ => zero) x
      rw [aux_eval_select] at hy
      convert hy using 2 with r
      split_ifs with h1 h2
      · rfl
      · exact (hmax p hp).symm
      · rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
