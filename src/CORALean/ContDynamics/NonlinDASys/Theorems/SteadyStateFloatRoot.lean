module

public import CORALean.ContDynamics.NonlinDASys.Operations.SteadyStateFloat
public import CORALean.ContDynamics.NonlinDASys.Theorems.NewtonTestFloatSound
public import CORALean.ContSet.Interval.Float.Theorems.AppendConstruct
public import CORALean.ContSet.Interval.Float.Theorems.HorzcatExact
public import CORALean.ContSet.Interval.Float.Theorems.VertcatExact

@[expose] public section

/-!
# What `steadyStateFloat` returns

A returned `(x', y')` lies within `tol`, in the sup norm in each block, of exactly one steady state
of the system at `u₀`: a point with `f = 0` and `g = 0`. The real `steadyState_spec` claims only
CORA's stopping test, a last stacked Newton step below `tol`; here the test the float run adds
(`newtonTestFloat_sound`, on the stacked state through `FloatModel.aux_stackRes` and `aux_stackJac`)
makes the claim about the steady state itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A returned pair is within `tol`, blockwise, of exactly one solution of `f = 0`, `g = 0`. -/
theorem NonlinDASys.FloatModel.Encloses.steadyStateFloat_root {fm : NonlinDASys.FloatModel 𝕋 n p m}
    {sys : NonlinDASys n p m} (hfm : fm.Encloses sys) (tol : 𝕋) (fuel : ℕ) (x₀ : Vec 𝕋 n)
    (y₀ : Vec 𝕋 p) (u₀ : Vec 𝕋 m) : -- --- CONCL ---
    ∀ x' y', (x', y') ∈ fm.steadyStateFloat tol fuel x₀ y₀ u₀ →
      ∃! xy : Vec ℝ n × Vec ℝ p, xy.1 ∈ Metric.closedBall (toRealVec x') (toReal tol) ∧
        xy.2 ∈ Metric.closedBall (toRealVec y') (toReal tol) ∧
        sys.f xy.1 xy.2 (toRealVec u₀) = 0 ∧
        sys.g xy.1 xy.2 (toRealVec u₀) = 0 := by -- --- PROOF ---
  intro x' y' (h : fm.steadyStateFloat tol fuel x₀ y₀ u₀ = some (x', y'))
  unfold NonlinDASys.FloatModel.steadyStateFloat at h
  obtain ⟨zv, -, hz⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at hz
  split_ifs at hz with htest
  set z : Vec 𝕋 (n + p) := fun i => zv[i] with hzdef
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hz)
  have hr0 : 0 ≤ toReal tol := by
    have ht := htest
    unfold NonlinDASys.newtonTestFloat at ht
    simp only [Bool.and_eq_true] at ht
    have := toReal_le_of_le ht.1
    rwa [toReal_zero] at this
  have hu : toRealVec u₀ ∈ (Interval.point u₀).construct := Interval.mem_point u₀
  -- the stacked map, and its two blocks
  set L : Vec ℝ (n + p) → Vec ℝ n := fun w i => w (Fin.castAdd p i) with hL
  set R : Vec ℝ (n + p) → Vec ℝ p := fun w j => w (Fin.natAdd n j) with hR
  set G : Vec ℝ (n + p) → Vec ℝ (n + p) := fun w =>
    Fin.append (sys.f (L w) (R w) (toRealVec u₀)) (sys.g (L w) (R w) (toRealVec u₀)) with hG
  have hLmem : ∀ (Z : Interval (Vec 𝕋 (n + p))), ∀ w ∈ Z.construct,
      L w ∈ (⟨fun i => Z.inf (Fin.castAdd p i), fun i => Z.sup (Fin.castAdd p i)⟩ :
        Interval (Vec 𝕋 n)).construct := fun _ _ hw i => hw (Fin.castAdd p i)
  have hRmem : ∀ (Z : Interval (Vec 𝕋 (n + p))), ∀ w ∈ Z.construct,
      R w ∈ (⟨fun j => Z.inf (Fin.natAdd n j), fun j => Z.sup (Fin.natAdd n j)⟩ :
        Interval (Vec 𝕋 p)).construct := fun _ _ hw j => hw (Fin.natAdd n j)
  -- `aux_stackRes` encloses `G`, and `aux_stackJac` its slopes
  have hGmem : ∀ (Z : Interval (Vec 𝕋 (n + p))), ∀ w ∈ Z.construct,
      G w ∈ (fm.aux_stackRes (Interval.point u₀) Z).construct := by
    intro Z w hw
    unfold NonlinDASys.FloatModel.aux_stackRes
    rw [Interval.append_construct]
    exact ⟨(_, _), ⟨hfm.f_mem _ _ _ _ (hLmem Z w hw) _ (hRmem Z w hw) _ hu,
      hfm.g_mem _ _ _ _ (hLmem Z w hw) _ (hRmem Z w hw) _ hu⟩, rfl⟩
  have hJmem : ∀ (Z : Interval (Vec 𝕋 (n + p))), ∀ w ∈ Z.construct, ∀ w' ∈ Z.construct,
      ∃ M ∈ (fm.aux_stackJac (Interval.point u₀) Z).construct, G w - G w' = M *ᵥ (w - w') := by
    intro Z w hw w' hw'
    obtain ⟨A, hA, C, hC, hf⟩ := hfm.slope_f _ _ _ _ (hLmem Z w hw) _ (hLmem Z w' hw') _
      (hRmem Z w hw) _ (hRmem Z w' hw') _ hu
    obtain ⟨D, hD, F, hF, hg⟩ := hfm.slope_g _ _ _ _ (hLmem Z w hw) _ (hLmem Z w' hw') _
      (hRmem Z w hw) _ (hRmem Z w' hw') _ hu
    -- the block matrix of the four slopes
    refine ⟨Fin.append (fun i => Fin.append (A i) (C i)) (fun i => Fin.append (D i) (F i)), ?_, ?_⟩
    · unfold NonlinDASys.FloatModel.aux_stackJac
      rw [Interval.vertcat_exact]
      refine ⟨(_, _), ⟨?_, ?_⟩, rfl⟩
      · rw [Interval.horzcat_exact]; exact ⟨(_, _), ⟨hA, hC⟩, rfl⟩
      · rw [Interval.horzcat_exact]; exact ⟨(_, _), ⟨hD, hF⟩, rfl⟩
    · funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · have := congrFun hf i
        simpa [hG, hL, hR, Matrix.mulVec, dotProduct, Fin.sum_univ_add] using this
      · have := congrFun hg j
        simpa [hG, hL, hR, Matrix.mulVec, dotProduct, Fin.sum_univ_add] using this
  obtain ⟨w, ⟨hwb, hw0⟩, huniq⟩ := NonlinDASys.newtonTestFloat_sound G _ _ hGmem hJmem z tol htest
  -- the stacked ball is the product of the two, and `G = 0` is `f = 0` and `g = 0`
  have hball : ∀ v : Vec ℝ (n + p), v ∈ Metric.closedBall (toRealVec z) (toReal tol) ↔
      L v ∈ Metric.closedBall (toRealVec fun i => z (Fin.castAdd p i)) (toReal tol) ∧
      R v ∈ Metric.closedBall (toRealVec fun j => z (Fin.natAdd n j)) (toReal tol) := by
    intro v
    simp only [Metric.mem_closedBall, dist_pi_le_iff hr0, Fin.forall_fin_add]
    rfl
  have hzero : ∀ v : Vec ℝ (n + p), G v = 0 ↔
      sys.f (L v) (R v) (toRealVec u₀) = 0 ∧ sys.g (L v) (R v) (toRealVec u₀) = 0 := by
    intro v
    constructor
    · intro h0
      refine ⟨funext fun i => ?_, funext fun j => ?_⟩
      · simpa [hG] using congrFun h0 (Fin.castAdd p i)
      · simpa [hG] using congrFun h0 (Fin.natAdd n j)
    · rintro ⟨hf, hg⟩
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp [hG, hf]
      · simp [hG, hg]
  refine ⟨(L w, R w), ⟨((hball w).mp hwb).1, ((hball w).mp hwb).2, (hzero w).mp hw0⟩, ?_⟩
  -- a second solution, stacked, is the stacked zero
  rintro ⟨x, y⟩ ⟨hx, hy, hfx, hgy⟩
  have hLx : L (Fin.append x y) = x := funext fun i => Fin.append_left x y i
  have hRy : R (Fin.append x y) = y := funext fun j => Fin.append_right x y j
  have heq := huniq (Fin.append x y)
    ⟨(hball _).mpr ⟨by rw [hLx]; exact hx, by rw [hRy]; exact hy⟩,
      (hzero _).mpr ⟨by rw [hLx, hRy]; exact hfx, by rw [hLx, hRy]; exact hgy⟩⟩
  rw [← heq, hLx, hRy]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
