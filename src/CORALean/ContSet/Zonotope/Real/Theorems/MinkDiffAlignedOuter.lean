import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffAligned
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffGenRecExact

/-!
# `Zonotope.minkDiffAligned` also encloses the Minkowski difference

The direction `minkDiffAligned_inner` leaves open, and what [1, Prop. 5]'s word
*exactly* asks for: nothing outside the closed form can absorb `Z₂`.

Read off [1, Thm. 1]'s recursion rather than from halfspaces. At aligned
generators the fold `A ↦ (A + {g}) ∩ (A - {g})` collapses, one generator at a
time, to the zonotope that shortens `g⁽ᵐ'ⁱ⁾` to `(1 - μᵢ) g⁽ᵐ'ⁱ⁾`, so
`minkDiffGenRec_exact` carries the rest. `aux_align_step` is that one step and
the only place a hypothesis is spent: `μᵢ ≤ 1` keeps the shortened generator
from turning around, and convexity of the running set is what averages a point
of one translate with a point of the other into the one the closed form offers.

Both bounds on `μ` are hypotheses [1, Prop. 5] does not print, and outside them
it is false rather than merely unproved — see `MinkDiffAlignedNotInner`.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- Both translates at once: shifting `x` either way along `v` lands in `A`. -/
theorem aux_mem_translate_pair (A : Set α) (v x : α) :
    x ∈ (A + ({v} : Set α)) ∩ (A - ({v} : Set α)) ↔ x - v ∈ A ∧ x + v ∈ A := by -- --- PROOF ---
  constructor
  · rintro ⟨⟨a, ha, b, hb, hx⟩, a', ha', b', hb', hx'⟩
    -- the singleton pins each second witness, so each shift is the witness itself
    rw [Set.mem_singleton_iff] at hb hb'
    refine ⟨?_, ?_⟩
    · rw [← hx, hb]; simpa using ha
    · rw [← hx', hb']; simpa using ha'
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x - v, h1, v, rfl, by simp⟩, x + v, h2, v, rfl, by simp⟩

/-- The segment one generator spans is convex: an average of coefficients is
again a coefficient. -/
theorem aux_convex_seg (g : α) :
    Convex ℝ {y : α | ∃ t : ℝ, |t| ≤ 1 ∧ y = t • g} := by -- --- PROOF ---
  rintro _ ⟨t₁, h₁, rfl⟩ _ ⟨t₂, h₂, rfl⟩ a b ha hb hab
  refine ⟨a * t₁ + b * t₂, ?_, by module⟩
  calc |a * t₁ + b * t₂| ≤ |a * t₁| + |b * t₂| := abs_add_le _ _
    _ = a * |t₁| + b * |t₂| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by linarith

/-- A coefficient of size at most `c` against `g` is one of size at most `1`
against `c • g` — at `c = 0` because both sides are then `0`. -/
theorem aux_seg_mem (c : ℝ) (hc : 0 ≤ c) (g : α) (s : ℝ) (hs : |s| ≤ c) :
    ∃ t : ℝ, |t| ≤ 1 ∧ s • g = t • (c • g) := by -- --- PROOF ---
  rcases hc.eq_or_lt with rfl | hpos
  · have hs0 : s = 0 := abs_eq_zero.mp (le_antisymm hs (abs_nonneg s))
    exact ⟨0, by norm_num, by rw [hs0]; simp⟩
  · refine ⟨s / c, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact hs
    · rw [smul_smul, div_mul_cancel₀ _ hpos.ne']

/-- One step of [1, Thm. 1]'s recursion at an aligned generator: intersecting
both translates along `μ • g` shortens the segment `g` spans to `(1 - μ) • g`. -/
theorem aux_align_step (W : Set α) (hW : Convex ℝ W) (g : α) (μ : ℝ) (h0 : 0 ≤ μ)
    (h1 : μ ≤ 1) :
    ((W + {y : α | ∃ t : ℝ, |t| ≤ 1 ∧ y = t • g}) + ({μ • g} : Set α))
        ∩ ((W + {y : α | ∃ t : ℝ, |t| ≤ 1 ∧ y = t • g}) - ({μ • g} : Set α))
      = W + {y : α | ∃ t : ℝ, |t| ≤ 1 ∧ y = t • ((1 - μ) • g)} := by -- --- PROOF ---
  ext x
  rw [aux_mem_translate_pair]
  constructor
  · rintro ⟨⟨w₁, hw₁, _, ⟨t₁, ht₁, rfl⟩, he₁⟩, w₂, hw₂, _, ⟨t₂, ht₂, rfl⟩, he₂⟩
    -- the two shifts read `x` off `W` twice, at coefficients `t₁ + μ` and `t₂ - μ`
    have hx₁ : x = w₁ + (t₁ + μ) • g := by
      have h : w₁ + t₁ • g = x - μ • g := he₁
      rw [eq_sub_iff_add_eq] at h
      rw [← h]; module
    have hx₂ : x = w₂ + (t₂ - μ) • g := by
      have h : w₂ + t₂ • g = x + μ • g := he₂
      rw [← sub_eq_iff_eq_add.mpr h]; module
    have hb₁ := abs_le.mp ht₁
    have hb₂ := abs_le.mp ht₂
    -- either the first coefficient already fits `[-(1 - μ), 1 - μ]`, or an average hits `1 - μ`
    obtain ⟨w, hw, s, hs, hxs⟩ : ∃ w ∈ W, ∃ s : ℝ, |s| ≤ 1 - μ ∧ x = w + s • g := by
      by_cases hc : t₁ + μ ≤ 1 - μ
      · exact ⟨w₁, hw₁, t₁ + μ, abs_le.mpr ⟨by linarith, hc⟩, hx₁⟩
      · rw [not_le] at hc
        -- it does not, so the second is the one below: the weight where they meet
        obtain ⟨L, hL0, hL1, hmix⟩ :
            ∃ L : ℝ, 0 ≤ L ∧ L ≤ 1 ∧ L * (t₁ + μ) + (1 - L) * (t₂ - μ) = 1 - μ := by
          have hden : (0:ℝ) < t₁ + μ - (t₂ - μ) := by linarith
          refine ⟨(1 - μ - (t₂ - μ)) / (t₁ + μ - (t₂ - μ)), div_nonneg (by linarith) hden.le,
            (div_le_one hden).mpr (by linarith), ?_⟩
          field_simp
          ring
        refine ⟨L • w₁ + (1 - L) • w₂, hW hw₁ hw₂ hL0 (by linarith) (by ring), 1 - μ,
          by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - μ)], ?_⟩
        calc x = L • x + (1 - L) • x := by module
          _ = L • (w₁ + (t₁ + μ) • g) + (1 - L) • (w₂ + (t₂ - μ) • g) := by
              rw [← hx₁, ← hx₂]
          _ = (L • w₁ + (1 - L) • w₂) + (L * (t₁ + μ) + (1 - L) * (t₂ - μ)) • g := by module
          _ = (L • w₁ + (1 - L) • w₂) + (1 - μ) • g := by rw [hmix]
    obtain ⟨t, ht, hts⟩ := aux_seg_mem (1 - μ) (by linarith) g s hs
    refine ⟨w, hw, t • ((1 - μ) • g), ⟨t, ht, rfl⟩, ?_⟩
    show w + t • ((1 - μ) • g) = x
    rw [← hts, hxs]
  · rintro ⟨w, hw, _, ⟨t, ht, rfl⟩, rfl⟩
    -- and back: shifting the shortened coefficient by `∓μ` stays within `[-1, 1]`
    have hb := abs_le.mp ht
    constructor
    · refine ⟨w, hw, (t * (1 - μ) - μ) • g, ⟨t * (1 - μ) - μ, ?_, rfl⟩, by module⟩
      rw [abs_le]; constructor <;> nlinarith
    · refine ⟨w, hw, (t * (1 - μ) + μ) • g, ⟨t * (1 - μ) + μ, ?_, rfl⟩, by module⟩
      rw [abs_le]; constructor <;> nlinarith

/-- The zero-centred zonotope on `n + 1` generators splits its head off: the
segment generator `0` spans, plus the zonotope on the remaining generators. -/
theorem aux_construct_cons (n : ℕ) (g : Fin (n + 1) → α) :
    (⟨n + 1, (0 : α), g⟩ : Zonotope α).construct
      = {y : α | ∃ t : ℝ, |t| ≤ 1 ∧ y = t • g 0}
          + (⟨n, (0 : α), fun i => g i.succ⟩ : Zonotope α).construct := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨β, hβ, rfl⟩
    -- the head coefficient is the segment's, the tail is the smaller zonotope's
    refine ⟨β 0 • g 0, ⟨β 0, hβ 0, rfl⟩, ∑ k : Fin n, β k.succ • g k.succ,
      ⟨fun k => β k.succ, fun k => hβ k.succ, (zero_add _).symm⟩, ?_⟩
    simp only [Fin.sum_univ_succ]
    abel
  · rintro ⟨_, ⟨t, ht, rfl⟩, _, ⟨β, hβ, rfl⟩, rfl⟩
    -- and back: `Fin.cons` is what puts the two coefficient families together
    refine ⟨Fin.cons t β, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ ?_ j
      · simpa using ht
      · intro k; simpa using hβ k
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      abel

/-- The whole fold, at every convex starting set: aligned generators leave the
closed form's shortened ones behind, one step at a time. -/
theorem aux_fold_aligned (n : ℕ) :
    ∀ (W : Set α), Convex ℝ W → ∀ (g : Fin n → α) (μ : Fin n → ℝ),
      (∀ i, 0 ≤ μ i) → (∀ i, μ i ≤ 1) →
      Fin.foldl n (fun A i => (A + {μ i • g i}) ∩ (A - {μ i • g i}))
          (W + (⟨n, (0 : α), g⟩ : Zonotope α).construct)
        = W + (⟨n, (0 : α), fun i => (1 - μ i) • g i⟩ : Zonotope α).construct := by -- --- PROOF ---
  induction n with
  | zero =>
    intro W hW g μ _ _
    -- no generators: both zonotopes are `{0}` and the fold does nothing
    have hz : ∀ g' : Fin 0 → α, (⟨0, (0 : α), g'⟩ : Zonotope α).construct = ({0} : Set α) := by
      intro g'
      ext y
      constructor
      · rintro ⟨β, -, hy⟩
        simpa using hy
      · rintro rfl
        exact ⟨Fin.elim0, fun j => j.elim0, by simp⟩
    rw [Fin.foldl_zero, hz, hz]
  | succ n ih =>
    intro W hW g μ h0 h1
    have hZ : Convex ℝ (⟨n, (0 : α), fun i => g i.succ⟩ : Zonotope α).construct :=
      Zonotope.convex_construct _
    -- peel the head generator, park the tail in the step's own convex set, take the step
    simp only [Fin.foldl_succ]
    rw [aux_construct_cons n g,
      show W + ({y : α | ∃ t : ℝ, |t| ≤ 1 ∧ y = t • g 0}
            + (⟨n, (0 : α), fun i => g i.succ⟩ : Zonotope α).construct)
          = (W + (⟨n, (0 : α), fun i => g i.succ⟩ : Zonotope α).construct)
            + {y : α | ∃ t : ℝ, |t| ≤ 1 ∧ y = t • g 0} from by abel,
      aux_align_step _ (hW.add hZ) (g 0) (μ 0) (h0 0) (h1 0),
      show (W + (⟨n, (0 : α), fun i => g i.succ⟩ : Zonotope α).construct)
            + {y : α | ∃ t : ℝ, |t| ≤ 1 ∧ y = t • ((1 - μ 0) • g 0)}
          = (W + {y : α | ∃ t : ℝ, |t| ≤ 1 ∧ y = t • ((1 - μ 0) • g 0)})
            + (⟨n, (0 : α), fun i => g i.succ⟩ : Zonotope α).construct from by abel,
      ih _ (hW.add (aux_convex_seg _)) (fun i => g i.succ) (fun i => μ i.succ)
        (fun i => h0 _) (fun i => h1 _),
      aux_construct_cons n (fun i => (1 - μ i) • g i)]
    abel

/-- A zonotope shifted by `-v` is the zero-centred one on its generators, moved
to `c - v`. -/
theorem aux_sub_singleton (Z : Zonotope α) (v : α) :
    Z.construct - ({v} : Set α)
      = {Z.c - v} + (⟨Z.h, (0 : α), Z.G⟩ : Zonotope α).construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨a, ⟨β, hβ, rfl⟩, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    refine ⟨Z.c - v, rfl, ∑ j, β j • Z.G j, ⟨β, hβ, (zero_add _).symm⟩, ?_⟩
    show Z.c - v + ∑ j, β j • Z.G j = Z.c + ∑ j, β j • Z.G j - b
    rw [hb]
    abel
  · rintro ⟨_, rfl, _, ⟨β, hβ, rfl⟩, rfl⟩
    refine ⟨Z.c + ∑ j, β j • Z.G j, ⟨β, hβ, rfl⟩, v, rfl, ?_⟩
    show Z.c + ∑ j, β j • Z.G j - v = Z.c - v + (0 + ∑ j, β j • Z.G j)
    abel

/-- And back: moving a zero-centred zonotope to `v` is its centre. -/
theorem aux_singleton_add (v : α) (n : ℕ) (g : Fin n → α) :
    ({v} : Set α) + (⟨n, (0 : α), g⟩ : Zonotope α).construct
      = (⟨n, v, g⟩ : Zonotope α).construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨p, hp, _, ⟨β, hβ, rfl⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hp
    refine ⟨β, hβ, ?_⟩
    show p + (0 + ∑ j, β j • g j) = v + ∑ j, β j • g j
    rw [hp, zero_add]
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨v, rfl, ∑ j, β j • g j, ⟨β, hβ, (zero_add _).symm⟩, rfl⟩

/-- The closed form at an explicit alignment: `g⁽ᵐ'ⁱ⁾ - μᵢ g⁽ᵐ'ⁱ⁾` is
`(1 - μᵢ) g⁽ᵐ'ⁱ⁾`, which is what the fold leaves behind. -/
theorem aux_aligned_eq (n : ℕ) (c₁ c₂ : α) (G₁ : Fin n → α) (μ : Fin n → ℝ) :
    Zonotope.minkDiffAligned (⟨n, c₁, G₁⟩ : Zonotope α) ⟨n, c₂, fun i => μ i • G₁ i⟩ rfl
      = ⟨n, c₁ - c₂, fun i => (1 - μ i) • G₁ i⟩ := by
  simp only [Zonotope.minkDiffAligned, Zonotope.mk.injEq, heq_eq_eq, true_and]
  funext i
  show G₁ i - μ i • G₁ i = (1 - μ i) • G₁ i
  module


-- =======================================  MAIN THEOREM  ======================================= --

/-- The direction [1, Prop. 5]'s *exactly* needs beyond `minkDiffAligned_inner`:
everything the difference holds, the closed form holds too. -/
theorem Zonotope.minkDiffAligned_outer (Z₁ Z₂ : Zonotope α) (hh : Z₁.h = Z₂.h)
    (μ : Fin Z₁.h → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∀ i, μ i ≤ 1)
    (hG : ∀ i, Z₂.G (Fin.cast hh i) = μ i • Z₁.G i) :
    minkowskiDiff Z₁.construct Z₂.construct
      ⊆ (Z₁.minkDiffAligned Z₂ hh).construct := by -- --- PROOF ---
  rw [← Zonotope.minkDiffGenRec_exact]
  -- taking the two counts apart is what turns `Fin.cast hh` into the identity
  obtain ⟨h₁, c₁, G₁⟩ := Z₁
  obtain ⟨h₂, c₂, G₂⟩ := Z₂
  dsimp only at hh hG μ ⊢
  subst hh
  have hGG : G₂ = fun i => μ i • G₁ i := funext fun i => hG i
  subst hGG
  apply Eq.subset
  -- the recursion's own starting set, then the fold, then the centre back on
  rw [Zonotope.minkDiffGenRec]
  dsimp only
  rw [aux_sub_singleton]
  dsimp only
  rw [aux_fold_aligned h₁ _ (convex_singleton _) G₁ μ hμ0 hμ1, aux_singleton_add,
    aux_aligned_eq]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
