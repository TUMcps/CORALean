# Guarantees for Real Robotic Systems: Unifying Formal Controller Synthesis and Reachset-Conformant Identification

S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems: Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE Transactions on Robotics, 39(5):3776-3790, 2023.

**Source:** https://arxiv.org/pdf/2103.01626 (arXiv:2103.01626v2, 12 Sep 2023, the authors' accepted version with the "© 2023 IEEE" notice, 14 pages including Appendices A-B, read in full; text extracted with `pypdf`). Volume, issue and pages from the DOI record (doi:10.1109/TRO.2023.3277268); the typeset T-RO article was not reachable. CORA cites it as "Liu et al., 202x" in `@linearSysDT/isconform_dyn.m`, `confSynth_dyn.m`, `confSynth_gray.m`, `private/priv_conform_reachableHalfspaces.m` and `priv_conform_unifyTrajectories.m`, by equation number ((14), (15), (17), (21), Thm. 1, Cor. 1), which match this numbering; `isconform_dyn` notes that the signs in (21) "were incorrect in the IEEE early access version" — the arXiv version read here has them right.  
**Inventory:** confirmed (Definitions 1-7, Propositions 1-4, Theorem 1, Corollary 1 and Remarks 1-3, each with its own counter; equations (1)-(33); Tables I-IV; Appendices A-B)

Reachset conformance for a linear plant `x(k+1) = A x + B u + w`, `y = C x + D u + v`, with the
disturbance and noise sets zonotopes stretched from templates, combined with the synthesis of
a tracking controller for a feedback-linearized robot. The conformance half is what CORA's
`linearSysDT/isconform_dyn` and `confSynth_dyn` implement and is formalized in full: the
measurements minus the nominal run against one deviation set `R_a(k)` (`Eq. 15`, `Eq. 16`),
its zonotope (`Eq. 17`, `Eq. 18`), the constraint linear in the identified centers and stretch
factors (`Thm. 1`), and conformance at every horizon from one-step residuals (`Cor. 1`). One
printed formula fails: (7) reverses the powers on the input term (`Eq. 7`). The controller
synthesis — tracking error, invariant sets, input constraints of the robot — is not covered.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotope) `Z = (c, G) := {x = c + Σ_h β_h g(h) \| β_h ∈ [-1, 1]}`; a θ-dimensional zonotope with s generators is an intersection of 2·C(s, θ-1) halfspaces. | n/a — restated from Kühn 1998 and Girard 2005; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Prop. 1` | (H-representation of a zonotope [66]) `{y \| N y ≤ d}`, `N = [N⁺; -N⁺]`, row `n⁺_j = nX(G⟨γ,…,η⟩)/‖nX(G⟨γ,…,η⟩)‖₂` (1)-(2), `d±_j = ±n⁺_jᵀ c + Δd_j`, `Δd_j = Σ_h \|n⁺_jᵀ g(h)\|` (3)-(4). | n/a — restated from Althoff, Stursberg and Buss 2010 [66]; tracked as `Thm. 7` on [Althoff, Stursberg, Buss 2010](../2010/althoff-nahs-zonotopes-polytopes.md) | `restated` |
| `Prop. 2` | (Minkowski sum of zonotopes [67]) `(c₁, G₁) ⊕ (c₂, G₂) = (c₁ + c₂, [G₁, G₂])`. | n/a — restated from Girard 2005 [67], where it is not a numbered result | `restated` |
| `Prop. 3` | (Linear transformation of zonotopes [67]) `A Z = (A c, A G)`. | n/a — restated from Girard 2005 [67], where it is not a numbered result | `restated` |
| `Prop. 4` | (Interval hull of zonotopes [67]) `I(Z) = [c - δ, c + δ]`, `δ = Σ_h \|g(h)\|`. | n/a — restated from Girard 2005 [67], where it is not a numbered result | `restated` |
| `Def. 2` | (Norm of zonotopes) `‖Z‖ := Σᵢ \|δᵢ\|`, the size of the interval hull. | [`IntervalNorm.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/IntervalNorm.lean) — `intervalNorm` at `σ = 1`, `Σ_h Σᵢ \|g(h)ᵢ\| = Σᵢ δᵢ`; a function of the generators | `correct` |
| `Eq. 5` | The plant: `x[k+1] = A x[k] + B u[k] + w[k]`, `y[k] = C x[k] + D u[k] + v[k]`, `w[k] ∈ W = (c_W, G'_W diag(α_W))`, `v[k] ∈ V = (c_V, G'_V diag(α_V))`. | [`Plant.lean`](../../src/CORALean/ContDynamics/Conform/Plant.lean), [`State.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/State.lean), [`TemplateZono.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/TemplateZono.lean) — over ℝ; the stretched templates over any finite generator index | `correct` |
| `Eq. 6` | One step of the reachable set: `R[k+1] = C(A X[k] ⊕ B u[k] ⊕ W) ⊕ D u[k+1] ⊕ V`. | [`ReachOutExactSucc.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ReachOutExactSucc.lean) — an equality, `X[k]` the reachable states | `correct` |
| `Eq. 7` | Unrolled: `R[k+1] = C(A^{k+1} X[0] ⊕ Σ_{i=0}^k Aⁱ B u[i] ⊕ ⨁_{i=0}^k Aⁱ W) ⊕ D u[k+1] ⊕ V`, exact for zonotopes. | [`ReachOutExactNePrinted.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ReachOutExactNePrinted.lean), [`MemReachOutExactIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemReachOutExactIff.lean) — the counterexample; with the powers corrected, (7) is `mem_reachOutExact_iff` at `x0 = 0`, the image under `C` distributed over the sum **Counterexample:** `Conform.Plant.reachOutExact_ne_printed` **Counterexample:** `Conform.Plant.reachOutExact_ne_printed` | `fixed` — `u[i]` enters through `A^{k-i} B`, not `Aⁱ B`: at `A = 2`, `B = C = 1`, `D = 0`, `X[0] = W = V = {0}`, `u = (1, 0)`, `y[2] = 2` is reachable and the printed set is `{1}`; the disturbance term and everything derived from (7) are unaffected; see Findings |
| `Def. 3` | (Test case) `(y_p[0..k*], u_p[0..k*], x_p[0])`. | [`IsConformant.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/IsConformant.lean) — `TestCase`, the sequences over `ℕ` | `correct` |
| `Def. 4` | (Sequential test cases) From one recording, every time step starts a test case: `y⁽ᵐ⁺¹⁾[k] = y⁽ᵐ⁾[k+1]`, `u⁽ᵐ⁺¹⁾[k] = u⁽ᵐ⁾[k+1]`. | [`ConformantOfRecording.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ConformantOfRecording.lean) — test case `m` is the recording from sample `m` on, `(y(m + ·), u(m + ·), x(m))`, which satisfies the relation by construction | `correct` |
| `Def. 5` | (Reachset conformance testing) The model is reachset conformant for `k ∈ {0, …, k*}` if `∀m ∀k: y⁽ᵐ⁾_p[k] ∈ R⁽ᵐ⁾_p[k]`, computed from `x⁽ᵐ⁾[0]` and `u⁽ᵐ⁾[k]`. | [`IsConformant.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/IsConformant.lean), [`ReachOutExact.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/ReachOutExact.lean) — `IsConformant {0} W V T K`: the initial state exact | `correct` |
| `Def. 6` | (Reachable tracking error) `y_cl ∈ y_ref ⊕ R_e`. | n/a — closed-loop controller synthesis for the robot, a subject CORALean does not cover | `not-covered` |
| `Def. 7` | (Reachable input) `R_u`; the controller is safe if `R_u ⊆ U_p`. | n/a — closed-loop controller synthesis for the robot, a subject CORALean does not cover | `not-covered` |
| `Eq. 12` | The combined problem: minimize `‖R_e(p)‖` subject to conformance (12b) and `R_u(p) ⊆ U_p` (12c). | n/a — a problem statement; its constraint (12b) is `Def. 5`, made linear by `Thm. 1` | `not-a-claim` |
| `Eq. 13` | The allowed inputs must satisfy the torque limits `T ⊇ M(Q) U_p ⊕ ψ(Q, dQ)`, checked with Taylor models. | n/a — robot rigid-body dynamics under feedback linearization, a subject CORALean does not cover | `not-covered` |
| `Eq. 14` | `y_a⁽ᵐ⁾[k] := y⁽ᵐ⁾[k] - y_*⁽ᵐ⁾[k]`, `y_*` the nominal solution without `W` and `V`. | [`State.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/State.lean) — `nominal` | `correct` |
| `Eq. 15` | `R_a[k] := R⁽ᵐ⁾[k] - y_*⁽ᵐ⁾[k] = ⨁_{i=0}^{k-1} C Aⁱ W ⊕ V`, independent of the input and the initial state. | [`MemReachOutExactIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemReachOutExactIff.lean), [`DevSet.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/DevSet.lean) — an equivalence at every measurement, with the initial uncertainty `{0}` | `correct` |
| `Eq. 16` | For linear systems (12b) is equal to `∀k: ⋃ₘ {y_a⁽ᵐ⁾[k]} ⊆ R_a[k]`. | [`ConformantIffDevSet.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ConformantIffDevSet.lean) | `correct` |
| `Eq. 17` | The center of `R_a[k]`: `c_k = [Σ_{i<k} Eᵢ, 1][c_W; c_V]`, `Eᵢ = C Aⁱ`. | [`DevSetZeroTemplateZono.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/DevSetZeroTemplateZono.lean) — an equality of sets with (18) | `correct` |
| `Eq. 18` | The generators of `R_a[k]`: `G_k = [E₀ G_W ⋯ E_{k-1} G_W  G_V]`. | [`DevSetZeroTemplateZono.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/DevSetZeroTemplateZono.lean) — `G_W = G'_W diag(α_W)`, `α_W` repeated once per step | `correct` |
| `Thm. 1` | (12b) is linear in `ξ = [c_W, c_V, α_W, α_V]`: `∀k: maxₘ(N_k y_a⁽ᵐ⁾[k]) ≤ D_k ξ` (19), `N_k = [N⁺_k; -N⁺_k]` the normals of `R_a[k]` (independent of `ξ`), `d±_{j,k} = [±Σ n⁺_{j,k} Eᵢ, ±n⁺_{j,k}, Σ \|n⁺_{j,k} Eᵢ G'_W\|, \|n⁺_{j,k} G'_V\|]`. | [`ConformantIffHRep.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ConformantIffHRep.lean), [`MemTemplateZonoIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemTemplateZonoIff.lean), [`MemScaleIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MemScaleIff.lean) — an equivalence, for every `k ≤ K` and every `α ≥ 0`; `N_k` any family carrying both signs of every cross product of `n` template generators up to a positive factor | `underspecified` — the template `[E₀ G'_W ⋯ G'_V]` must span the output space, else every `nX` vanishes and (1) divides by zero; the proof cancels `det(diag(α))` and needs `α > 0`, the statement holds at `α ≥ 0` (a vanished generator's normals are still the template's); see Findings |
| `Cor. 1` | With sequential test cases, the model is reachset conformant for `k* → ∞` if `⋃ₘ {x_a⁽ᵐ⁾[1]} ⊆ W` (20) and `⋃ₘ {y⁽ᵐ⁾[0] - C x⁽ᵐ⁾[0] - D u⁽ᵐ⁾[0]} ⊆ V` (21). | [`ConformantOfRecording.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ConformantOfRecording.lean) — conformance at every horizon `K` of all test cases cut from a recording of states, inputs and outputs; the residuals are the run's own disturbances | `correct` |
| `Remark 1` | The H-representations of `W` and `V` turn Cor. 1's constraints into linear inequalities, as in Thm. 1. | [`MemTemplateZonoIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemTemplateZonoIff.lean) — membership in a stretched template is its template's halfspaces at offsets linear in center and stretch | `correct` |
| `Remark 2` | Cor. 1 is generally more conservative than Thm. 1 (checking states is stricter than checking projected outputs). | n/a — a comparison of the two methods | `not-a-claim` |
| `Remark 3` | In practice, a horizon exists beyond which a larger `k*` does not change Thm. 1's result. | n/a — an observation about experiments | `not-a-claim` |
| `Sec. III-A` | The reachable tracking error and input as projections of the closed loop's converged set `R̃_cl,e[k∞]`, computed with [74, Alg. 2]. | n/a — closed-loop controller synthesis and invariant sets, a subject CORALean does not cover | `not-covered` |
| `Sec. III-C` | The iterative procedure alternating synthesis and re-testing on the robot (Fig. 2). | n/a — a procedure involving experiments on the real system | `not-a-claim` |
| `Sec. III-D` | The program (12) is nonlinear, solved to a local optimum; complexity `O(n³)` per evaluation. | n/a — a nonlinear program's convergence and cost, a subject CORALean does not cover | `not-covered` |
| `Sec. IV` | Experiments on a 6-axis manipulator: combined vs. separate identification, LQG comparison, observers (Tables I-IV, Figs. 3-9, Eqs. (28)-(32)). | n/a — experiments | `not-a-claim` |
| `Appendix A` | The full robot model with disturbance state and the templates of `W_p`, `V_p`. | n/a — the model of the experiments | `not-a-claim` |
| `Appendix B` | Three ways to handle the reference error `y_e,ref` in `R_e`, `R_u` (33). | n/a — closed-loop controller synthesis, a subject CORALean does not cover | `not-covered` |

## Findings

**`Eq. 7` — the input term's powers are reversed.** Unrolling (6) from `X[0]`, the input
`u[i]` reaches `x[k+1]` through `A^{k-i} B`; (7) prints `Aⁱ B u[i]`. For `A = 2`, `B = C = 1`,
`D = 0`, `X[0] = W = V = {0}`, `u[0] = 1`, `u[1] = 0`, the model reaches `y[2] = A B u[0] = 2`,
while (7) gives `{B u[0] + A B u[1]} = {1}`. The disturbance term `⨁ Aⁱ W` is right, since
`W` is the same at every step, and so is everything the paper builds on (7): (15) subtracts
the nominal solution, whose input term cancels whatever its form, and CORA computes the
nominal run by `simulate`.
[`ReachOutExactNePrinted.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ReachOutExactNePrinted.lean),
[`MemReachOutExactIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemReachOutExactIff.lean)

**`Thm. 1` — two hypotheses the proof uses.** The normals (1) divide by `‖nX(·)‖₂`, which
needs the template of `R_a[k]` to span the output space — otherwise every cross product
vanishes and no row of `N_k` is defined (Prop. 1's halfspace representation is of a
full-dimensional zonotope). The proof shows the normals independent of `α` by cancelling
`det(diag(α))`, "since all elements of `α` are positive"; the stretch factors an
identification returns may well be `0`, where a generator and every normal through it
vanish. The statement holds there all the same: the template's normals, at offsets linear
in `α`, still cut out `⟨c, G' diag(α)⟩` for every `α ≥ 0`, because the point lies in every
stretch `α + ε` and these shrink onto the closed zonotope.
[`MemScaleIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MemScaleIff.lean),
[`ConformantIffHRep.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ConformantIffHRep.lean)
