import DGPS.Examples.ThreeSpeciesCircle.InteractingOrdinaryScoreBase
import DGPS.Examples.ThreeSpeciesCircle.InteractingScoreUniformControl
import DGPS.Examples.ThreeSpeciesCircle.InteractingLogProfileControl
import DGPS.Examples.ThreeSpeciesCircle.InteractingLogOdeControl
import DGPS.Examples.ThreeSpeciesCircle.InteractingFeedbackDerivativeBounds

/-! Actual-model differential upgrade, retaining the original weak-gradient
metric and the true rank-three feedback. It derives all logarithmic derivative
convergence through order three; no score/logarithmic convergence is a premise.
The actual every-minimizer producer must still supply the systems and choose a
nearby ordinary root before this local upgrade is used. -/

noncomputable section
open MeasureTheory Filter Topology Set Function
open scoped ContDiff
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Examples.ThreeSpeciesCircle

def elementaryPhysicalLogProfile (h : ℝ) (v : Torus 1 → ℝ) (t : ℝ) : ℝ :=
  Real.log (v (pt t)^2)-ellT h (pt t)

private theorem smooth_weakGradient_of_one_derivative {f g : Torus 1 → ℝ}
    (hf : IsSmoothPeriodic f)
    (hd : ∀ t : ℝ, HasDerivAt (fun s => f (pt s)) (g (pt t)) t) :
    IsWeakGradient f (vec1 g) := by
  apply hf.isWeakGradient.congr_ae (ae_eq_refl _)
  exact Eventually.of_forall fun x => by
    obtain ⟨t, rfl⟩ := bs_exists_pt x
    have he := (hasDerivAt_smooth_one hf t).unique (hd t)
    ext i
    fin_cases i
    change smoothGrad f (pt t) 0 = vec1 g (pt t) 0
    rw [smoothGrad_apply, vec1_apply]
    exact he

private theorem uniform_to_physical_usmall {v : ℕ → Torus 1 → ℝ} {u : Torus 1 → ℝ}
    (hu : TendstoUniformly v u atTop) : USmall (fun n t => v n (pt t)-u (pt t)) := by
  intro e he
  filter_upwards [Metric.tendstoUniformly_iff.mp hu e he] with n hn t
  have ht := (hn (pt t)).le
  simpa only [Real.dist_eq, abs_sub_comm] using ht

/-- For the ACTUAL physical feedback, convergence of original root H1 distance,
rate and coupling yields uniform convergence of relative physical log profiles
and their first three derivatives. Smooth positive representatives and the true
classical systems are factual inputs, not assumed logarithmic convergence. All
fields retain their original absolute-density law. -/
theorem elementaryLogProfile_derivatives_small {h : ℝ} (hh : 0 < h)
    (a R m M : ℝ) (hR : 0 ≤ R) (hm : 0 < m) (hmM : m ≤ M)
    (σ : AbsoluteDensity 1) (ρ : ℕ → AbsoluteDensity 1)
    (u S0 : Torus 1 → ℝ) (v S : ℕ → Torus 1 → ℝ) (ε r : ℕ → ℝ)
    (hu : IsSmoothPeriodic u) (hS0 : IsSmoothPeriodic S0)
    (hv : ∀ n, IsSmoothPeriodic (v n)) (hS : ∀ n, IsSmoothPeriodic (S n))
    (hσu : σ.sqrt =ᵐ[haar 1] u) (hρv : ∀ n, (ρ n).sqrt =ᵐ[haar 1] v n)
    (hub : ∀ x, u x ∈ Icc m M) (hvb : ∀ n x, v n x ∈ Icc m M)
    (hud : ∀ t : ℝ, HasDerivAt (fun s => u (pt s))
      ((S0 (pt t)+u (pt t)*sigT h (pt t))/2) t)
    (hS0d : ∀ t : ℝ, HasDerivAt (fun s => S0 (pt s))
      (-(S0 (pt t)*sigT h (pt t))/2-a*interactingLogNonlinearity h (pt t) (u (pt t))) t)
    (hvd : ∀ (n : ℕ) (t : ℝ), HasDerivAt (fun s => v n (pt s))
      ((S n (pt t)+v n (pt t)*sigT h (pt t))/2) t)
    (hSd : ∀ (n : ℕ) (t : ℝ), HasDerivAt (fun s => S n (pt s))
      (elementaryPhysicalScoreRhs h (ε n) (r n) (ρ n) (v n) (S n) (pt t)) t)
    (hrb : ∀ n, |r n| ≤ R) (hεb : ∀ n, 0 ≤ ε n ∧ ε n ≤ 1)
    (hd : Tendsto (fun n => ordinaryRootH1Deviation σ (ρ n) u) atTop (𝓝 0))
    (hr : Tendsto r atTop (𝓝 a)) (hε : Tendsto ε atTop (𝓝 0)) :
    USmall (fun n t => elementaryPhysicalLogProfile h (v n) t-elementaryPhysicalLogProfile h u t) ∧
    USmall (fun n t => deriv (elementaryPhysicalLogProfile h (v n)) t-
      deriv (elementaryPhysicalLogProfile h u) t) ∧
    USmall (fun n t => deriv (deriv (elementaryPhysicalLogProfile h (v n))) t-
      deriv (deriv (elementaryPhysicalLogProfile h u)) t) ∧
    USmall (fun n t => deriv (deriv (deriv (elementaryPhysicalLogProfile h (v n)))) t-
      deriv (deriv (deriv (elementaryPhysicalLogProfile h u))) t) := by
  have hup : ∀ x, 0 < u x := fun x => hm.trans_le (hub x).1
  have hvp : ∀ n x, 0 < v n x := fun n x => hm.trans_le (hvb n x).1
  have hS0e := classicalScore_eq_native_ae h σ hu hσu hud
  have hSe := fun n => classicalScore_eq_native_ae h (ρ n) (hv n) (hρv n) (hvd n)
  have hS0w := smooth_weakGradient_of_one_derivative (g := fun x => -(S0 x * sigT h x) / 2 - a * interactingLogNonlinearity h x (u x)) hS0 hS0d
  have hSw := fun n => smooth_weakGradient_of_one_derivative (g := elementaryPhysicalScoreRhs h (ε n) (r n) (ρ n) (v n) (S n)) (hS n) (hSd n)
  have hVunif := ordinaryRoot_continuous_tendstoUniformly σ ρ hu.continuous_torus
    (fun n => (hv n).continuous_torus) hσu hρv hd
  have hSunif := ordinaryRoot_score_tendstoUniformly h a R m M hR hm hmM σ ρ
    hu.continuous_torus hS0.continuous_torus (fun n => (hv n).continuous_torus)
    (fun n => (hS n).continuous_torus) hσu hρv hub hvb hS0e hSe hS0w hSw hrb hεb hd hr hε
  have hS0b : Bdd (fun t => S0 (pt t)) := periodic_bdd
    (circ_periodic_pt S0) (hS0.continuous_torus.comp continuous_circleParam)
  obtain ⟨h0, h1⟩ := positiveRoot_logProfile_first_small h m hm v S u S0
    (fun n x => (hvb n x).1) (fun x => (hub x).1) hvd hud hS0b
    (uniform_to_physical_usmall hVunif) (uniform_to_physical_usmall hSunif)
  let f := fun n => elementaryPhysicalLogProfile h (v n)
  let f0 := elementaryPhysicalLogProfile h u
  let s := fun t => sigT h (pt t)
  let q := fun n t => elementaryEulerCorrection h (ε n) (r n) (ρ n) (pt t)
  let lam := fun n => elementaryEulerMultiplier h (ε n) (r n) (ρ n)
  have hf (n : ℕ) : ContDiff ℝ ∞ (f n) :=
    (((hv n).comp (contDiff_pi.mpr fun _ => contDiff_id)).pow 2 |>.log
      (fun t => pow_ne_zero 2 (hvp n (pt t)).ne')).sub
        ((isSmoothPeriodic_ellT h).comp (contDiff_pi.mpr fun _ => contDiff_id))
  have hf0 : ContDiff ℝ ∞ f0 :=
    ((hu.comp (contDiff_pi.mpr fun _ => contDiff_id)).pow 2 |>.log
      (fun t => pow_ne_zero 2 (hup (pt t)).ne')).sub
        ((isSmoothPeriodic_ellT h).comp (contDiff_pi.mpr fun _ => contDiff_id))
  have hs : ContDiff ℝ ∞ s :=
    ((isSmoothPeriodic_ellT h).isSmoothPeriodic_coordPartial 0).comp
      (contDiff_pi.mpr fun _ => contDiff_id)
  have hq (n : ℕ) : ContDiff ℝ ∞ (q n) :=
    (isSmooth_elementaryEulerCorrection h (ε n) (r n) (ρ n)).comp
      (contDiff_pi.mpr fun _ => contDiff_id)
  have hE := fun n => elementary_classicalScore_logEuler h (ε n) (r n) (ρ n)
    (hvp n) (hvd n) (hSd n)
  have hE0 : ∀ t, -2*deriv (deriv f0) t-(deriv f0 t)^2-2*s t*deriv f0 t-2*a*f0 t=0 := by
    have ht := elementary_classicalScore_logEuler h 0 a σ hup hud (fun t => by
      simpa [elementaryEulerCorrection, elementaryEulerMultiplier, interactingLogNonlinearity] using hS0d t)
    unfold f0 elementaryPhysicalLogProfile s
    simpa [elementaryEulerCorrection, elementaryEulerMultiplier] using ht
  obtain ⟨K, hK, hfield⟩ := elementaryEulerCorrection_uniform_bound h R hR
  have hlam : Tendsto lam atTop (𝓝 0) := by
    have habs : Tendsto (fun n => |lam n|) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => abs_nonneg _)
        (fun n => (hfield (ρ n) (r n) (hrb n) (ε n) (hεb n).1 (hεb n).2).2)
      simpa using hε.const_mul K
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  have hq0 : USmall q := by
    apply USmall.of_const_mul hε q K
    intro n t
    simpa only [abs_of_nonneg (hεb n).1] using
      (hfield (ρ n) (r n) (hrb n) (ε n) (hεb n).1 (hεb n).2).1 (pt t)
  obtain ⟨Kd, hKd, hderiv⟩ := elementaryEulerCorrection_derivative_uniform_bound hh R hR
  have hqd : USmall (fun n t => deriv (q n) t) := by
    apply USmall.of_const_mul hε _ Kd
    intro n t
    have hdq := (hasDerivAt_smooth_one
      (isSmooth_elementaryEulerCorrection h (ε n) (r n) (ρ n)) t).deriv
    change |deriv (fun s => elementaryEulerCorrection h (ε n) (r n) (ρ n) (pt s)) t| ≤ _
    rw [hdq]
    simpa only [abs_of_nonneg (hεb n).1] using
      hderiv (ρ n) (r n) (hrb n) (ε n) (hεb n).1 (hεb n).2 (pt t)
  obtain ⟨h2, h3⟩ := logScoreODE_second_third_small f f0 s q r lam a hf hf0 hs
    (circ_periodic_pt (fun x => Real.log (u x^2)-ellT h x))
    (circ_periodic_pt (sigT h)) (fun n => (hq n).differentiable (by simp))
    hE hE0 h0 h1 hr hlam hq0 hqd
  exact ⟨h0, h1, h2, h3⟩

end DGPS.Examples.ThreeSpeciesCircle
