module

public import CORALean.ContSet.Zonotope.Real.Definitions.BackpropEnclose
public import CORALean.ContSet.Zonotope.Real.Operations.ImageEnclosure
public import CORALean.ContSet.Zonotope.Real.Theorems.FderivEqGradient
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

/-!
# The gradient set through an image enclosure

[1, Prop. 12] and [1, Prop. 13 (nonlinear)]: through the image enclosure
`H_k = Diag(m) H_{k-1} ⊕ [e, ē]` of a nonlinear layer (`Zonotope.imageEnclosure`) the gradient
set of a set loss is `∇_{H_{k-1}} L = backpropEnclose(ϕ_k, 𝒢_k)` (`Zonotope.backpropEnclose`),
`𝒢_k = ∇_{H_k} L` the output's. As in the paper's proof (Eq. 19-25), entry by entry the chain
rule reads `Σᵢ c'(i) ∂c_k(i) + Σᵢ Σⱼ G'(i,j) ∂G_k(i,j)`; only row `i` of the output moves with
an entry of row `i` of the input, through `m(i)` and the errors, which the product rule
differentiates. That needs the loss differentiable at the layer's output in the center and
generator entries together, and `m(i)`, `e(i)`, `ē(i)` differentiable in the row `H(i)`: the
statement assumes neither, and the secant slope of Def. 7 is not differentiable where a
generator entry is `0`, the bounds `c ∓ Σⱼ |G(i,j)|` having a kink there.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The scalar functions of a row, along its center and along a generator entry. -/
theorem aux_hasDerivAt_row (f : Zonotope (Vec ℝ 1) → ℝ) (R : Zonotope (Vec ℝ 1))
    (hf : DifferentiableAt ℝ (fun p : Vec ℝ 1 × (Fin R.h → Vec ℝ 1) => f ⟨R.h, p.1, p.2⟩)
      (R.c, R.G)) : -- --- STMT ---
    HasDerivAt (fun t => f ⟨R.h, fun _ => t, R.G⟩) ((R.gradient f).c 0) (R.c 0) ∧
      ∀ j, HasDerivAt (fun t => f ⟨R.h, R.c, Function.update R.G j (fun _ => t)⟩)
        ((R.gradient f).G j 0) (R.G j 0) := by -- --- PROOF ---
  have hc1 : ∀ (v : Vec ℝ 1) t, Function.update v 0 t = fun _ => t := fun v t => by
    funext x; rw [Fin.fin_one_eq_zero x, Function.update_self]
  have hcR : R.c = fun _ => R.c 0 := by funext x; rw [Fin.fin_one_eq_zero x]
  constructor
  · have hd : DifferentiableAt ℝ (fun t => f ⟨R.h, fun _ => t, R.G⟩) (R.c 0) := by
      have hl : DifferentiableAt ℝ (fun t : ℝ => ((fun _ => t : Vec ℝ 1), R.G)) (R.c 0) :=
        (differentiableAt_pi.mpr fun _ => differentiableAt_id).prodMk
          (differentiableAt_const _)
      have : (R.c, R.G) = ((fun _ => R.c 0 : Vec ℝ 1), R.G) := by rw [← hcR]
      rw [this] at hf
      have h2 := hf.comp (R.c 0) hl
      exact h2
    have he : (R.gradient f).c 0 = deriv (fun t => f ⟨R.h, fun _ => t, R.G⟩) (R.c 0) := by
      show deriv (fun t => f { R with c := Function.update R.c 0 t }) (R.c 0) = _
      simp only [hc1]
    rw [he]
    exact hd.hasDerivAt
  -- along a generator entry, the same way
  · intro j
    have hGj : R.G j = fun _ => R.G j 0 := by funext x; rw [Fin.fin_one_eq_zero x]
    have hd : DifferentiableAt ℝ (fun t => f ⟨R.h, R.c, Function.update R.G j (fun _ => t)⟩)
        (R.G j 0) := by
      have hl : DifferentiableAt ℝ (fun t : ℝ => (R.c, Function.update R.G j (fun _ => t)))
          (R.G j 0) := by
        refine (differentiableAt_const _).prodMk (differentiableAt_pi.mpr fun l => ?_)
        by_cases hl : l = j
        · subst hl; simp only [Function.update_self]
          exact differentiableAt_pi.mpr fun _ => differentiableAt_id
        · simp only [Function.update_of_ne hl]; exact differentiableAt_const _
      -- the line through the row, the entry unchanged at `t = G(j)`
      have : (R.c, R.G) = (R.c, Function.update R.G j (fun _ => R.G j 0)) := by
        rw [← hGj, Function.update_eq_self]
      rw [this] at hf
      have h2 := hf.comp (R.G j 0) hl
      exact h2
    have he : (R.gradient f).G j 0 =
        deriv (fun t => f ⟨R.h, R.c, Function.update R.G j (fun _ => t)⟩) (R.G j 0) := by
      show deriv (fun t => f { R with G := Function.update R.G j (Function.update (R.G j) 0 t) })
        (R.G j 0) = _
      simp only [hc1]
    rw [he]
    exact hd.hasDerivAt

/-- The output's generators split into the input's `p` and the `n` error ones. -/
theorem aux_sum_univ_imageEnclosure (m eLo eUp : Zonotope (Vec ℝ 1) → ℝ) (H : Zonotope (Vec ℝ n))
    (f : Fin (H.imageEnclosure m eLo eUp).h → ℝ) :
    ∑ l : Fin (H.imageEnclosure m eLo eUp).h, f l =
      ∑ j : Fin H.h, f (Fin.castAdd n j) + ∑ i : Fin n, f (Fin.natAdd H.h i) :=
  Fin.sum_univ_add f

/-- A center entry of the gradient set: the chain rule through the output's row `i`. -/
theorem aux_gradient_c (ℒ : Zonotope (Vec ℝ n) → ℝ) (m eLo eUp : Zonotope (Vec ℝ 1) → ℝ)
    (H : Zonotope (Vec ℝ n))
    (hF : DifferentiableAt ℝ (fun p : Vec ℝ n × (Fin (H.h + n) → Vec ℝ n) =>
      ℒ ⟨H.h + n, p.1, p.2⟩) ((H.imageEnclosure m eLo eUp).c, (H.imageEnclosure m eLo eUp).G))
    (hm : ∀ i, DifferentiableAt ℝ (fun p : Vec ℝ 1 × (Fin H.h → Vec ℝ 1) => m ⟨H.h, p.1, p.2⟩)
      ((H.row i).c, (H.row i).G))
    (heL : ∀ i, DifferentiableAt ℝ (fun p : Vec ℝ 1 × (Fin H.h → Vec ℝ 1) => eLo ⟨H.h, p.1, p.2⟩)
      ((H.row i).c, (H.row i).G))
    (heU : ∀ i, DifferentiableAt ℝ (fun p : Vec ℝ 1 × (Fin H.h → Vec ℝ 1) => eUp ⟨H.h, p.1, p.2⟩)
      ((H.row i).c, (H.row i).G)) (i : Fin n) : -- --- STMT ---
    (H.gradient (fun Z => ℒ (Z.imageEnclosure m eLo eUp))).c i =
      (H.backpropEnclose m eLo eUp ((H.imageEnclosure m eLo eUp).gradient ℒ).c
        ((H.imageEnclosure m eLo eUp).gradient ℒ).G).c i := by -- --- PROOF ---
  set out := H.imageEnclosure m eLo eUp with hout
  set R := H.row i with hR
  set F : Vec ℝ n × (Fin (H.h + n) → Vec ℝ n) → ℝ := fun p => ℒ ⟨H.h + n, p.1, p.2⟩ with hFdef
  obtain ⟨dm, -⟩ := aux_hasDerivAt_row m R (hm i)
  obtain ⟨deL, -⟩ := aux_hasDerivAt_row eLo R (heL i)
  obtain ⟨deU, -⟩ := aux_hasDerivAt_row eUp R (heU i)
  set Dm := (R.gradient m).c 0
  set DL := (R.gradient eLo).c 0
  set DU := (R.gradient eUp).c 0
  -- the input with center entry `i` moved to `t`, and its rows
  let Ht : ℝ → Zonotope (Vec ℝ n) := fun t => { H with c := Function.update H.c i t }
  have hr1 : ∀ t, (Ht t).row i = ⟨H.h, fun _ => t, R.G⟩ := fun t => by
    simp only [Ht, Zonotope.row, Function.update_self]; rfl
  have hr2 : ∀ t i', i' ≠ i → (Ht t).row i' = H.row i' := fun t i' h => by
    simp only [Ht, Zonotope.row, Function.update_of_ne h]
  -- the output's coordinates along the line
  let P : ℝ → Vec ℝ n × (Fin (H.h + n) → Vec ℝ n) := fun t =>
    Prod.mk (fun i' => m ((Ht t).row i') * Function.update H.c i t i' +
        (eLo ((Ht t).row i') + eUp ((Ht t).row i')) / 2)
      (Fin.append (fun j i' => m ((Ht t).row i') * H.G j i')
        (fun i'' => Pi.single i'' ((eUp ((Ht t).row i'') - eLo ((Ht t).row i'')) / 2)))
  let P' : Vec ℝ n × (Fin (H.h + n) → Vec ℝ n) :=
    Prod.mk (Pi.single i (m R + H.c i * Dm + (DL + DU) / 2))
      (Fin.append (fun j => Pi.single i (H.G j i * Dm))
        (fun i' => Pi.single i' (if i' = i then (DU - DL) / 2 else 0)))
  have hP : HasDerivAt P P' (H.c i) := by
    refine HasDerivAt.prodMk ?_ ?_
    -- the center: only row `i` moves, by the product rule
    · rw [hasDerivAt_pi]
      intro i'
      by_cases h : i' = i
      · subst h
        simp only [hr1, Function.update_self, Pi.single_eq_same]
        refine ((dm.mul (hasDerivAt_id' _)).add ((deL.add deU).div_const 2)).congr_deriv ?_
        show Dm * H.c i' + m R * 1 + (DL + DU) / 2 = _
        ring
      · simp only [hr2 _ _ h, Function.update_of_ne h, Pi.single_eq_of_ne h]
        exact hasDerivAt_const _ _
    · rw [hasDerivAt_pi]
      intro l
      rw [hasDerivAt_pi]
      intro i'
      -- the generators: the input's, then the error ones
      refine Fin.addCases (fun j => ?_) (fun i'' => ?_) l
      · simp only [Fin.append_left]
        by_cases h : i' = i
        · subst h
          simp only [hr1, Pi.single_eq_same]
          exact (dm.mul_const (H.G j i')).congr_deriv (by ring)
        · simp only [hr2 _ _ h, Pi.single_eq_of_ne h]
          exact hasDerivAt_const _ _
      · simp only [Fin.append_right, Pi.single_apply]
        by_cases h : i' = i''
        · subst h
          by_cases h' : i' = i
          · subst h'
            simp only [if_true, hr1]
            exact (deU.sub deL).div_const 2
          · simp only [h', if_false, if_true, hr2 _ _ h']
            exact hasDerivAt_const _ _
        · simp only [h, if_false]
          exact hasDerivAt_const _ _
  -- at `t = c(i)` the line passes through the input itself
  have hP0 : ((H.imageEnclosure m eLo eUp).c, (H.imageEnclosure m eLo eUp).G) = P (H.c i) := by
    refine Prod.ext ?_ ?_
    · funext x; simp only [P, Zonotope.imageEnclosure, Zonotope.row, Ht, Function.update_eq_self]
    · funext l x; simp only [P, Zonotope.imageEnclosure, Zonotope.row, Ht,
        Function.update_eq_self]
  have hchain : HasDerivAt (F ∘ P)
      (fderiv ℝ F ((H.imageEnclosure m eLo eUp).c, (H.imageEnclosure m eLo eUp).G) P') (H.c i) :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq (H.c i) hP hP0
  -- the chain rule at the output, read off its gradient set
  show deriv (F ∘ P) (H.c i) = _
  rw [hchain.deriv]
  refine (Zonotope.fderiv_eq_gradient ℒ (H.imageEnclosure m eLo eUp) hF P'.1 P'.2).trans ?_
  rw [aux_sum_univ_imageEnclosure]
  simp only [P', Fin.append_left, Fin.append_right, single_dotProduct, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Zonotope.backpropEnclose]
  rw [show ∑ x, H.G x i * Dm * ((H.imageEnclosure m eLo eUp).gradient ℒ).G (Fin.castAdd n x) i =
      (∑ x, ((H.imageEnclosure m eLo eUp).gradient ℒ).G (Fin.castAdd n x) i * H.G x i) * Dm by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring]
  ring

/-- A generator entry of the gradient set, the same way. -/
theorem aux_gradient_G (ℒ : Zonotope (Vec ℝ n) → ℝ) (m eLo eUp : Zonotope (Vec ℝ 1) → ℝ)
    (H : Zonotope (Vec ℝ n))
    (hF : DifferentiableAt ℝ (fun p : Vec ℝ n × (Fin (H.h + n) → Vec ℝ n) =>
      ℒ ⟨H.h + n, p.1, p.2⟩) ((H.imageEnclosure m eLo eUp).c, (H.imageEnclosure m eLo eUp).G))
    (hm : ∀ i, DifferentiableAt ℝ (fun p : Vec ℝ 1 × (Fin H.h → Vec ℝ 1) => m ⟨H.h, p.1, p.2⟩)
      ((H.row i).c, (H.row i).G))
    (heL : ∀ i, DifferentiableAt ℝ (fun p : Vec ℝ 1 × (Fin H.h → Vec ℝ 1) => eLo ⟨H.h, p.1, p.2⟩)
      ((H.row i).c, (H.row i).G))
    (heU : ∀ i, DifferentiableAt ℝ (fun p : Vec ℝ 1 × (Fin H.h → Vec ℝ 1) => eUp ⟨H.h, p.1, p.2⟩)
      ((H.row i).c, (H.row i).G)) (j : Fin H.h) (i : Fin n) : -- --- STMT ---
    (H.gradient (fun Z => ℒ (Z.imageEnclosure m eLo eUp))).G j i =
      (H.backpropEnclose m eLo eUp ((H.imageEnclosure m eLo eUp).gradient ℒ).c
        ((H.imageEnclosure m eLo eUp).gradient ℒ).G).G j i := by -- --- PROOF ---
  set R := H.row i with hR
  set F : Vec ℝ n × (Fin (H.h + n) → Vec ℝ n) → ℝ := fun p => ℒ ⟨H.h + n, p.1, p.2⟩ with hFdef
  have dm := (aux_hasDerivAt_row m R (hm i)).2 j
  have deL := (aux_hasDerivAt_row eLo R (heL i)).2 j
  have deU := (aux_hasDerivAt_row eUp R (heU i)).2 j
  set Dm := (R.gradient m).G j 0
  set DL := (R.gradient eLo).G j 0
  set DU := (R.gradient eUp).G j 0
  -- the input with generator `j`'s entry `i` moved to `t`, and its rows
  let Ht : ℝ → Zonotope (Vec ℝ n) := fun t =>
    { H with G := Function.update H.G j (Function.update (H.G j) i t) }
  have hr1 : ∀ t, (Ht t).row i = ⟨H.h, R.c, Function.update R.G j (fun _ => t)⟩ := fun t => by
    simp only [Ht, Zonotope.row]
    congr 1
    funext j' x
    by_cases hj : j' = j
    · rw [hj]; simp [R, Zonotope.row]
    · simp [hj, R, Zonotope.row]
  have hr2 : ∀ t i', i' ≠ i → (Ht t).row i' = H.row i' := fun t i' h => by
    simp only [Ht, Zonotope.row]
    congr 1
    funext j' x
    by_cases hj : j' = j
    · rw [hj]; simp [Function.update_of_ne h]
    · simp [hj]
  -- at the unchanged entry the row is the row
  have hRup : ∀ j0, (⟨R.h, R.c, Function.update R.G j0 (fun _ => R.G j0 0)⟩ :
      Zonotope (Vec ℝ 1)) = R := fun j0 => by
    have : (fun _ => R.G j0 0 : Vec ℝ 1) = R.G j0 := by
      funext x; rw [Fin.fin_one_eq_zero x]
    rw [this, Function.update_eq_self]
  have hG : ∀ t j' i', (Ht t).G j' i' = if j' = j ∧ i' = i then t else H.G j' i' := by
    intro t j' i'
    simp only [Ht]
    by_cases hj : j' = j
    · rw [hj]
      by_cases hi : i' = i
      · rw [hi]; simp
      · simp [hi]
    · simp [hj]
  -- the output's coordinates along the line
  let P : ℝ → Vec ℝ n × (Fin (H.h + n) → Vec ℝ n) := fun t =>
    Prod.mk (fun i' => m ((Ht t).row i') * H.c i' + (eLo ((Ht t).row i') + eUp ((Ht t).row i')) / 2)
      (Fin.append (fun j' i' => m ((Ht t).row i') * (Ht t).G j' i')
        (fun i'' => Pi.single i'' ((eUp ((Ht t).row i'') - eLo ((Ht t).row i'')) / 2)))
  let P' : Vec ℝ n × (Fin (H.h + n) → Vec ℝ n) :=
    Prod.mk (Pi.single i (H.c i * Dm + (DL + DU) / 2))
      (Fin.append (fun j' => Pi.single i (H.G j' i * Dm + if j' = j then m R else 0))
        (fun i' => Pi.single i' (if i' = i then (DU - DL) / 2 else 0)))
  have hP : HasDerivAt P P' (H.G j i) := by
    refine HasDerivAt.prodMk ?_ ?_
    -- the center: only row `i` moves, through the slope and the errors
    · rw [hasDerivAt_pi]
      intro i'
      by_cases h : i' = i
      · subst h
        simp only [hr1, Pi.single_eq_same]
        exact ((dm.mul_const (H.c i')).add ((deL.add deU).div_const 2)).congr_deriv (by ring)
      · simp only [hr2 _ _ h, Pi.single_eq_of_ne h]
        exact hasDerivAt_const _ _
    · rw [hasDerivAt_pi]
      intro l
      rw [hasDerivAt_pi]
      intro i'
      -- the generators: the input's, then the error ones
      refine Fin.addCases (fun j' => ?_) (fun i'' => ?_) l
      · simp only [Fin.append_left, hG]
        by_cases h : i' = i
        · subst h
          simp only [hr1, Pi.single_eq_same, and_true]
          by_cases hj : j' = j
          · subst hj
            simp only [if_true]
            refine (dm.mul (hasDerivAt_id' _)).congr_deriv ?_
            rw [hRup]
            show Dm * H.G j' i' + m R * 1 = _
            ring
          · simp only [hj, if_false, add_zero]
            exact (dm.mul_const (H.G j' i')).congr_deriv (by ring)
        · simp only [hr2 _ _ h, Pi.single_eq_of_ne h, h, and_false, if_false]
          exact hasDerivAt_const _ _
      -- an error generator moves only in row `i`
      · simp only [Fin.append_right, Pi.single_apply]
        by_cases h : i' = i''
        · subst h
          by_cases h' : i' = i
          · subst h'
            simp only [if_true, hr1]
            exact (deU.sub deL).div_const 2
          · simp only [h', if_false, if_true, hr2 _ _ h']
            exact hasDerivAt_const _ _
        · simp only [h, if_false]
          exact hasDerivAt_const _ _
  -- at `t = G(i, j)` the line passes through the input itself
  have hP0 : ((H.imageEnclosure m eLo eUp).c, (H.imageEnclosure m eLo eUp).G) = P (H.G j i) := by
    refine Prod.ext ?_ ?_
    · funext x; simp only [P, Zonotope.imageEnclosure, Zonotope.row, Ht, Function.update_eq_self]
    · funext l x; simp only [P, Zonotope.imageEnclosure, Zonotope.row, Ht,
        Function.update_eq_self]
  have hchain : HasDerivAt (F ∘ P)
      (fderiv ℝ F ((H.imageEnclosure m eLo eUp).c, (H.imageEnclosure m eLo eUp).G) P')
        (H.G j i) :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq (H.G j i) hP hP0
  -- the chain rule at the output, read off its gradient set
  show deriv (F ∘ P) (H.G j i) = _
  rw [hchain.deriv]
  refine (Zonotope.fderiv_eq_gradient ℒ (H.imageEnclosure m eLo eUp) hF P'.1 P'.2).trans ?_
  rw [aux_sum_univ_imageEnclosure]
  simp only [P', Fin.append_left, Fin.append_right, single_dotProduct, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Zonotope.backpropEnclose, add_mul,
    Finset.sum_add_distrib]
  rw [show ∑ x, H.G x i * Dm * ((H.imageEnclosure m eLo eUp).gradient ℒ).G (Fin.castAdd n x) i =
      (∑ x, ((H.imageEnclosure m eLo eUp).gradient ℒ).G (Fin.castAdd n x) i * H.G x i) * Dm by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.gradient_imageEnclosure (ℒ : Zonotope (Vec ℝ n) → ℝ)
    (m eLo eUp : Zonotope (Vec ℝ 1) → ℝ) (H : Zonotope (Vec ℝ n))
    (hF : DifferentiableAt ℝ (fun p : Vec ℝ n × (Fin (H.h + n) → Vec ℝ n) =>
      ℒ ⟨H.h + n, p.1, p.2⟩) ((H.imageEnclosure m eLo eUp).c, (H.imageEnclosure m eLo eUp).G))
    (hm : ∀ i, DifferentiableAt ℝ (fun p : Vec ℝ 1 × (Fin H.h → Vec ℝ 1) => m ⟨H.h, p.1, p.2⟩)
      ((H.row i).c, (H.row i).G))
    (heL : ∀ i, DifferentiableAt ℝ (fun p : Vec ℝ 1 × (Fin H.h → Vec ℝ 1) => eLo ⟨H.h, p.1, p.2⟩)
      ((H.row i).c, (H.row i).G))
    (heU : ∀ i, DifferentiableAt ℝ (fun p : Vec ℝ 1 × (Fin H.h → Vec ℝ 1) => eUp ⟨H.h, p.1, p.2⟩)
      ((H.row i).c, (H.row i).G)) : -- --- STMT ---
    H.gradient (fun Z => ℒ (Z.imageEnclosure m eLo eUp)) =
      H.backpropEnclose m eLo eUp ((H.imageEnclosure m eLo eUp).gradient ℒ).c
        ((H.imageEnclosure m eLo eUp).gradient ℒ).G := by -- --- PROOF ---
  show Zonotope.mk H.h (H.gradient (fun Z => ℒ (Z.imageEnclosure m eLo eUp))).c
      (H.gradient (fun Z => ℒ (Z.imageEnclosure m eLo eUp))).G =
    Zonotope.mk H.h (H.backpropEnclose m eLo eUp ((H.imageEnclosure m eLo eUp).gradient ℒ).c
        ((H.imageEnclosure m eLo eUp).gradient ℒ).G).c
      (H.backpropEnclose m eLo eUp ((H.imageEnclosure m eLo eUp).gradient ℒ).c
        ((H.imageEnclosure m eLo eUp).gradient ℒ).G).G
  congr 1
  · funext i; exact aux_gradient_c ℒ m eLo eUp H hF hm heL heU i
  · funext j i; exact aux_gradient_G ℒ m eLo eUp H hF hm heL heU j i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
