import DGRHS.Gaussian.PeriodicD1AbelSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! UNCOMPILED REPAIRED COPY (Claude complete physical d1 return, 2026-10-03).
Repairs: meromorphy via a complex-analytic map restricted along `ofRealCLM` (fun_prop
cannot prove real analyticity of `t ↦ exp(2πit)`); explicit rewrite to the
meromorphic log-norm form; `Circle.ext` for the injectivity step; explicit null
singleton proof; explicit continuity composition. Statements unchanged.
Original header follows.
 Draft proper Haar integrability of the actual circle logarithm, including
the boundary radius. Real-meromorphic logarithm integrability is imported from
the exact pinned native source. The single collision point is removed by Haar
non-atomicity; no integral or Fourier conclusion is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DGRHS.Periodic

lemma periodicD1AbelCircle_measurable (r : ℝ) : Measurable (periodicD1AbelCircle r) := by
  unfold periodicD1AbelCircle
  fun_prop

lemma periodicD1AbelCircle_intervalIntegrable (r : ℝ) :
    IntervalIntegrable (fun t : ℝ => periodicD1AbelCircle r (t:UnitAddCircle)) volume 0 1 := by
  have hm : MeromorphicOn
      (fun t : ℝ => (1:ℂ)-(r:ℂ)*Complex.exp (2*Real.pi*Complex.I*(t:ℂ))) (Set.uIcc (0:ℝ) 1) := by
    intro t _
    apply AnalyticAt.meromorphicAt
    have hg : AnalyticAt ℂ
        (fun z : ℂ => (1:ℂ)-(r:ℂ)*Complex.exp (2*Real.pi*Complex.I*z)) (t:ℂ) := by
      fun_prop
    exact hg.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
  have hfun : (fun t : ℝ => periodicD1AbelCircle r (t:UnitAddCircle)) =
      -(fun t : ℝ => Real.log ‖(1:ℂ)-(r:ℂ)*Complex.exp (2*Real.pi*Complex.I*(t:ℂ))‖) := by
    funext t
    simp only [periodicD1AbelCircle,Pi.neg_apply,fourier_coe_apply,Int.cast_one,mul_one,
      Complex.ofReal_one,div_one]
  rw [hfun]
  exact hm.intervalIntegrable_log_norm.neg

lemma periodicD1AbelCircle_integrable (r : ℝ) :
    Integrable (periodicD1AbelCircle r) AddCircle.haarAddCircle := by
  have hp : MeasurePreserving (fun t : ℝ => (t:UnitAddCircle))
      (volume.restrict (Ioc (0:ℝ) 1)) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 0
  rw [←hp.map_eq]
  apply (integrable_map_measure (periodicD1AbelCircle_measurable r).aestronglyMeasurable hp.aemeasurable).mpr
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
    (periodicD1AbelCircle_intervalIntegrable r)

lemma periodicD1_fourier_one_eq_one_iff (x : UnitAddCircle) : fourier 1 x=1 ↔ x=0 := by
  constructor
  · intro h
    apply AddCircle.injective_toCircle (one_ne_zero : (1:ℝ)≠0)
    apply Circle.ext
    rw [←fourier_one,←fourier_one,fourier_eval_zero]
    exact h
  · intro h
    subst x
    exact fourier_eval_zero _

lemma periodicD1_fourier_one_ne_one_ae :
    ∀ᵐ x : UnitAddCircle ∂AddCircle.haarAddCircle,fourier 1 x≠1 := by
  have hv : (volume : Measure UnitAddCircle)=AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using
      AddCircle.volume_eq_smul_haarAddCircle (T := 1)
  haveI : NullSingletonClass (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    ⟨fun x => by
      have h := AddCircle.volume_closedBall (T := 1) (x := x) 0
      rw [Metric.closedBall_zero,hv] at h
      rw [h,ENNReal.ofReal_eq_zero]
      exact (min_le_right _ _).trans (by norm_num)⟩
  filter_upwards [Measure.ae_ne (AddCircle.haarAddCircle : Measure UnitAddCircle) 0] with x hx
  exact fun h => hx ((periodicD1_fourier_one_eq_one_iff x).mp h)

lemma periodicD1AbelCircle_boundary_tendsto (x : UnitAddCircle) (hx : fourier 1 x≠1) :
    Tendsto (fun r : ℝ => periodicD1AbelCircle r x) (𝓝 1) (𝓝 (periodicD1AbelCircle 1 x)) := by
  apply ContinuousAt.tendsto
  unfold periodicD1AbelCircle
  apply ContinuousAt.neg
  have hn : ‖(1:ℂ)-((1:ℝ):ℂ)*fourier 1 x‖≠0 := by
    rw [Complex.ofReal_one,one_mul]
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hx))
  exact (Real.continuousAt_log hn).comp
    (f := fun r : ℝ => ‖(1:ℂ)-(r:ℂ)*fourier 1 x‖) (by fun_prop)

end DGRHS.Periodic
