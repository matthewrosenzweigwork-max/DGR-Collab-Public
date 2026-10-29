import DGPS.Examples.RoughBoundary.FreeEnergy
import DGPS.Examples.RoughBoundary.SemicontinuityPotential

/-!
# RUF029: the full free energy remote barrier

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 3.6 (3.11)--(3.12).

Write `G(ρ) = F(ρ m) - κ/2 = H(ρ m | q_{κM} m) + Ψ(κM)` (RUF027).  Let `t_*` be a critical point
of the parameter potential `Ψ` with `D²Ψ ≥ λ I` on `B̄(t_*, r)`, `λ, r > 0`, `0 ∉ B̄(t_*, r)`.
Then `G(ρ) ≥ Ψ(t_*) + (λ/2) |κM(ρ) - t_*|²` when `|κM(ρ) - t_*| ≤ r`, equality at `Ψ(t_*)` forces
`ρ = q_{t_*}`, on the annulus `r/2 ≤ |κM(ρ) - t_*| ≤ r` one has `G ≥ Ψ(t_*) + λ r²/8`, and every
weakly continuous path of probability measures from `q_{t_*} m` to Haar crosses the annulus.

Design choices (R5 notes).
* `G` is written additively over `κ/2` in `EReal`, exactly as in RUF027 (`F(ν) ≥ κ/2 + ...`).
* Hypotheses: the landscape certificate for `U_{L,ε}` (which yields RUF027), `t_*` critical for
  `Ψ`, the Hessian bound `λ ‖v‖² ≤ D²Ψ(x)(v, v)` on the closed ball, and `‖t_*‖ > r`
  (that is `0 ∉ B̄(t_*, r)`).  Positivity of `Δ = Ψ(t_*)` and `t_* ≠ 0` are not needed (`t_* ≠ 0`
  follows from `r < ‖t_*‖`), so the statement is slightly stronger than displayed.
* A weakly continuous path is `γ : ℝ → ProbabilityMeasure (Torus 1)` continuous on `[0, 1]` for the
  weak topology of `ProbabilityMeasure`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal BoundedContinuousFunction ContDiff

namespace DGPS.Examples.RoughBoundary.FreeEnergy

open DGPS.Examples.RoughBoundary.Feature DGPS.Examples.RoughBoundary.Landscape
open DGPS.Examples.RoughBoundary.Model (modelData kappa)
open DGPS.Examples.RoughBoundary.Semicontinuity (featurePotential logPart contDiff_logPart)

/-- Integrating a positive Hessian bound twice about a critical point. -/
lemma taylor_lower_of_hessian (f : E2 → ℝ) (hf : ContDiff ℝ 2 f) (a : E2) (r lam : ℝ)
    (hcrit : fderiv ℝ f a = 0)
    (hH : ∀ x ∈ closedBall a r, ∀ v : E2, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    ∀ t ∈ closedBall a r, f a + lam / 2 * ‖t - a‖ ^ 2 ≤ f t := by
  intro t ht
  set d : E2 := t - a with hd
  have hdr : ‖d‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at ht
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdf' : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => a + s • d) d s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const d).const_add a
  set c : ℝ := lam * ‖d‖ ^ 2 with hc
  set g : ℝ → ℝ := fun s => f (a + s • d) with hg
  set g' : ℝ → ℝ := fun s => fderiv ℝ f (a + s • d) d with hg'
  have hg1 : ∀ s, HasDerivAt g (g' s) s := fun s =>
    (hdf (a + s • d)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hg2 : ∀ s, HasDerivAt g' (fderiv ℝ (fderiv ℝ f) (a + s • d) d d) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ f (a + s • d))
        (fderiv ℝ (fderiv ℝ f) (a + s • d) d) s :=
      (hdf' (a + s • d)).hasFDerivAt.comp_hasDerivAt s (hline s)
    simpa using h1.clm_apply (hasDerivAt_const s d)
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, a + s • d ∈ closedBall a r := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.1]
    calc s * ‖d‖ ≤ 1 * ‖d‖ := by gcongr; exact hs.2
      _ ≤ r := by rw [one_mul]; exact hdr
  -- first integration: `g' s - c s ≥ 0`
  have hψD : ∀ s, HasDerivAt (fun s => g' s - c * s)
      (fderiv ℝ (fderiv ℝ f) (a + s • d) d d - c * 1) s := fun s =>
    (hg2 s).sub ((hasDerivAt_id s).const_mul c)
  have hψ : MonotoneOn (fun s => g' s - c * s) (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun s _ => (hψD s).continuousAt.continuousWithinAt
    · exact fun s _ => (hψD s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hψD s).deriv]
      have := hH _ (hmem s ⟨hs.1.le, hs.2.le⟩) d
      linarith
  have hψ0 : g' 0 - c * 0 = 0 := by simp [hg', hcrit]
  have hψnn : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ g' s - c * s := fun s hs => by
    have := hψ ⟨le_rfl, zero_le_one⟩ hs hs.1
    linarith
  have hh : MonotoneOn (fun s => g s - c * (s ^ 2 / 2)) (Icc 0 1) := by
    have hD : ∀ s, HasDerivAt (fun s => g s - c * (s ^ 2 / 2)) (g' s - c * s) s := fun s => by
      have h : HasDerivAt (fun s => g s - c * (s ^ 2 / 2))
          (g' s - c * (((2 : ℕ) : ℝ) * s ^ (2 - 1) / 2)) s :=
        (hg1 s).sub (((hasDerivAt_pow 2 s).div_const 2).const_mul c)
      convert h using 2; simp
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun s _ => (hD s).continuousAt.continuousWithinAt
    · exact fun s _ => (hD s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hD s).deriv]
      exact hψnn s ⟨hs.1.le, hs.2.le⟩
  have h01 := hh ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hg, zero_smul, add_zero, one_smul, hd, add_sub_cancel] at h01
  rw [hc] at h01
  nlinarith [h01]

/-- The `i`-th feature coordinate as a bounded continuous function on the torus. -/
noncomputable def featureCoordBCF {L : ℝ} (hL : 0 < L) (ε : ℝ) (i : Fin 2) : Torus 1 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y => Ufeat L ε y i, (EuclideanSpace.proj i).continuous.comp (continuous_Ufeat hL ε)⟩

/-- The mean feature `M(ν) = ∫ U dν` is continuous for the weak topology of probability measures
(`U` is continuous and bounded). -/
lemma continuous_meanFeature {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    Continuous fun ν : ProbabilityMeasure (Torus 1) => meanFeature L ε (ν : Measure (Torus 1)) := by
  have hi : ∀ i : Fin 2, Continuous fun ν : ProbabilityMeasure (Torus 1) =>
      meanFeature L ε (ν : Measure (Torus 1)) i := by
    intro i
    have h := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (featureCoordBCF hL ε i)
    refine h.congr fun ν => ?_
    unfold meanFeature
    have := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm (integrable_U hL ε (ν : Measure (Torus 1)))
    have e : (∫ x, featureCoordBCF hL ε i x ∂(ν : Measure (Torus 1))) =
        ∫ x, (Ufeat L ε x) i ∂(ν : Measure (Torus 1)) := rfl
    rw [e]
    simpa using this
  have : (fun ν : ProbabilityMeasure (Torus 1) => meanFeature L ε (ν : Measure (Torus 1))) =
      fun ν : ProbabilityMeasure (Torus 1) =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => meanFeature L ε (ν : Measure (Torus 1)) i) := by
    funext ν; ext i; simp
  rw [this]
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp (continuous_pi hi)

lemma contDiff_featurePotential {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    ContDiff ℝ 2 (featurePotential kappa0 (Ufeat L ε)) := by
  have h1 : ContDiff ℝ 2 (fun t : E2 => ‖t‖ ^ 2 / (2 * kappa0)) :=
    ((contDiff_norm_sq ℝ).div_const _)
  have h2 : ContDiff ℝ 2 (logPart (DGPS.haar 1) (Ufeat L ε)) :=
    (contDiff_logPart (measurable_Ufeat hL ε) (ae_norm_Ufeat L ε)).of_le (by simp)
  exact h1.sub h2

/-- RUF029 (statement kernel).  Under the landscape certificate, a critical point `t_*` of `Ψ` with
`D²Ψ ≥ λ I` on `B̄(t_*, r)` and `0 ∉ B̄(t_*, r)` gives the full free energy barrier; here
`G(ρ) = F(ρ m) - κ/2` is written additively over `κ/2` in `EReal`. -/
theorem full_free_energy_remote_barrier {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (hcert : RoughLandscapeCertificate (Ufeat L ε)) (tstar : E2) (r lam : ℝ)
    (hr : 0 < r) (hlam : 0 < lam)
    (hcrit : fderiv ℝ (featurePotential kappa0 (Ufeat L ε)) tstar = 0)
    (h0 : (0 : E2) ∉ closedBall tstar r)
    (hH : ∀ x ∈ closedBall tstar r, ∀ v : E2,
      lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (featurePotential kappa0 (Ufeat L ε))) x v v) :
    -- (3.11): the local barrier inequality
    (∀ ν : ProbabilityMeasure (Torus 1),
      ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ ≤ r →
        (((kappa / 2 + featurePotential kappa0 (Ufeat L ε) tstar +
          lam / 2 * ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ ^ 2 : ℝ)) : EReal) ≤
          freeEnergy (modelData hL ε) ν) ∧
    -- equality at the level `Δ` forces `ρ = q_{t_*}`, and `q_{t_*}` attains it
    (∀ ν : ProbabilityMeasure (Torus 1),
      ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ ≤ r →
        freeEnergy (modelData hL ε) ν =
          ((kappa / 2 + featurePotential kappa0 (Ufeat L ε) tstar : ℝ) : EReal) →
        ν = gibbsProbability hL ε tstar) ∧
    freeEnergy (modelData hL ε) (gibbsProbability hL ε tstar) =
      ((kappa / 2 + featurePotential kappa0 (Ufeat L ε) tstar : ℝ) : EReal) ∧
    -- (3.12): the annulus bound
    (∀ ν : ProbabilityMeasure (Torus 1),
      r / 2 ≤ ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ →
      ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ ≤ r →
        (((kappa / 2 + featurePotential kappa0 (Ufeat L ε) tstar + lam * r ^ 2 / 8 : ℝ)) : EReal) ≤
          freeEnergy (modelData hL ε) ν) ∧
    -- every weakly continuous path from `q_{t_*}` to Haar crosses the annulus
    (∀ γ : ℝ → ProbabilityMeasure (Torus 1), ContinuousOn γ (Icc 0 1) →
      γ 0 = gibbsProbability hL ε tstar → γ 1 = haarProbability 1 →
        ∃ s ∈ Icc (0 : ℝ) 1,
          r / 2 ≤ ‖kappa • meanFeature L ε (γ s : Measure (Torus 1)) - tstar‖ ∧
          ‖kappa • meanFeature L ε (γ s : Measure (Torus 1)) - tstar‖ ≤ r) := by
  have hdec := freeEnergyDecomposition_of_certificate ε hcert hL
  obtain ⟨hA, -, -, -, -, hG⟩ := hdec
  obtain ⟨-, -, hnn, -, -⟩ := hcert
  set Ψ := featurePotential kappa0 (Ufeat L ε) with hΨ
  have hk : (0 : ℝ) < kappa := kappa_pos
  have htay := taylor_lower_of_hessian Ψ (contDiff_featurePotential hL ε) tstar r lam hcrit hH
  -- the lower bound at the level of reals, from the exact decomposition
  have hgeP : ∀ (ν : ProbabilityMeasure (Torus 1)) (Q : ℝ),
      Q ≤ Ψ (kappa • meanFeature L ε (ν : Measure (Torus 1))) →
        (((kappa / 2 + Q : ℝ)) : EReal) ≤ freeEnergy (modelData hL ε) ν := by
    intro ν Q hQ
    rw [(hA ν).1, EReal.coe_add]
    refine add_le_add le_rfl ?_
    exact (EReal.coe_le_coe_iff.mpr hQ).trans (le_add_of_nonneg_left (EReal.coe_ennreal_nonneg _))
  have hloc : ∀ ν : ProbabilityMeasure (Torus 1),
      ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ ≤ r →
      Ψ tstar + lam / 2 * ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ ^ 2 ≤
        Ψ (kappa • meanFeature L ε (ν : Measure (Torus 1))) := by
    intro ν hν
    exact htay _ (by rwa [mem_closedBall, dist_eq_norm])
  obtain ⟨hself, hFg⟩ := hG tstar hcrit
  have hbar : ∀ ν : ProbabilityMeasure (Torus 1),
      r / 2 ≤ ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ →
      ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ ≤ r →
      (((kappa / 2 + Ψ tstar + lam * r ^ 2 / 8 : ℝ)) : EReal) ≤
        freeEnergy (modelData hL ε) ν := by
    intro ν h1 h2
    have := hgeP ν (Ψ tstar + lam * r ^ 2 / 8) (by
      have h3 := hloc ν h2
      have h4 : lam * r ^ 2 / 8 ≤ lam / 2 * ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ ^ 2 := by
        have : (r / 2) ^ 2 ≤ ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
        nlinarith
      linarith)
    convert this using 2; ring
  refine ⟨fun ν hν => ?_, fun ν hν heq => ?_, ?_, hbar, ?_⟩
  · have := hgeP ν _ (hloc ν hν)
    convert this using 2; ring
  · -- equality case
    have hP := hloc ν hν
    rw [(hA ν).1] at heq
    have hHtop : relativeEntropy (ν : Measure (Torus 1))
        (gibbsMeasure L ε (kappa • meanFeature L ε (ν : Measure (Torus 1)))) ≠ ⊤ := by
      intro h
      rw [h] at heq
      simp at heq
      rw [← EReal.coe_add] at heq
      exact EReal.top_ne_coe _ heq
    rw [coe_eq_toReal hHtop, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_eq_coe_iff] at heq
    have hHnn := ENNReal.toReal_nonneg (a := relativeEntropy (ν : Measure (Torus 1))
        (gibbsMeasure L ε (kappa • meanFeature L ε (ν : Measure (Torus 1)))))
    have hd2 : ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖]
    have hHz : (relativeEntropy (ν : Measure (Torus 1))
        (gibbsMeasure L ε (kappa • meanFeature L ε (ν : Measure (Torus 1))))).toReal = 0 := by
      nlinarith [sq_nonneg ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖]
    have hH0 := (ENNReal.toReal_eq_zero_iff _).mp hHz
    have hH0' : relativeEntropy (ν : Measure (Torus 1))
        (gibbsMeasure L ε (kappa • meanFeature L ε (ν : Measure (Torus 1)))) = 0 :=
      hH0.resolve_right hHtop
    have hM : kappa • meanFeature L ε (ν : Measure (Torus 1)) = tstar := by
      have : ‖kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar‖ = 0 :=
        le_antisymm (by nlinarith [norm_nonneg (kappa • meanFeature L ε (ν : Measure (Torus 1)) - tstar)]) (norm_nonneg _)
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    rw [hM] at hH0'
    have := isProbabilityMeasure_gibbs hL ε tstar
    have hνe : (ν : Measure (Torus 1)) = gibbsMeasure L ε tstar :=
      relativeEntropy_zero_iff.mp hH0'
    exact Subtype.ext hνe
  · rw [hFg]
    norm_cast
  · -- path crossing
    intro γ hγ hγ0 hγ1
    have hcont : ContinuousOn (fun s : ℝ =>
        ‖kappa • meanFeature L ε (γ s : Measure (Torus 1)) - tstar‖) (Icc 0 1) :=
      (((continuous_meanFeature hL ε).comp_continuousOn hγ).const_smul kappa |>.sub
        continuousOn_const).norm
    have hv0 : ‖kappa • meanFeature L ε (γ 0 : Measure (Torus 1)) - tstar‖ = 0 := by
      rw [hγ0]
      show ‖kappa • meanFeature L ε (gibbsMeasure L ε tstar) - tstar‖ = 0
      rw [← hself, sub_self, norm_zero]
    have hv1 : r < ‖kappa • meanFeature L ε (γ 1 : Measure (Torus 1)) - tstar‖ := by
      rw [hγ1]
      show r < ‖kappa • meanFeature L ε (DGPS.haar 1) - tstar‖
      rw [meanFeature_haar_eq_zero hL ε hnn, smul_zero, zero_sub, norm_neg]
      by_contra hc
      exact h0 (by rw [mem_closedBall, dist_comm, dist_eq_norm, sub_zero]; exact not_lt.mp hc)
    obtain ⟨s, hs, hsr⟩ := intermediate_value_Icc (zero_le_one) hcont
      ⟨by rw [hv0]; exact hr.le, hv1.le⟩
    have hsr' : ‖kappa • meanFeature L ε (γ s : Measure (Torus 1)) - tstar‖ = r := hsr
    exact ⟨s, hs, by rw [hsr']; linarith, hsr'.le⟩

end DGPS.Examples.RoughBoundary.FreeEnergy
