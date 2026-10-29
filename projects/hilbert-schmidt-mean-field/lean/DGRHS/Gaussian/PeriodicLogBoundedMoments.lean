import DGRHS.Commutator.SourceLogTransportLocal
import DGRHS.Commutator.SourceLogTransportEnergy

/-!
Packet P9h, unit 3 (LOG, part 8): signed exponential moments of the literal transport energy for any
bounded symmetric measurable kernel on any probability space (the kernel-generic form of
`exists_sourceLogTransport_energy_exponential`, whose proof only uses boundedness, symmetry and
measurability of the kernel).
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian

/-- Proper signed exponential moments of `N A_n` for a bounded symmetric measurable kernel `h`. -/
theorem boundedKernel_energy_exponential {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (h : X × X → ℝ) (hm : Measurable h) (hs : ∀ a b, h (a, b) = h (b, a))
    (L : ℝ) (hL : 0 ≤ L) (hb : ∀ p, |h p| ≤ L) (t : ℝ)
    (ht : |t| * (DGRHS.Attractive.attractiveMomentConstant * (4 * L)) < 1) (N : ℕ) (hN : 0 < N) :
    Integrable (fun x : Fin N → X => Real.exp (t * (N : ℝ) * sourceTransportEnergy μ h N x))
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ x : Fin N → X, Real.exp (t * (N : ℝ) * sourceTransportEnergy μ h N x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      Real.exp (3 * |t| * L) *
        (2 / (1 - (t * (DGRHS.Attractive.attractiveMomentConstant * (4 * L))) ^ 2)) := by
  let H := DGRHS.Gaussian.hoeffdingCentered μ h
  have hi : Integrable h (μ.prod μ) := integrable_of_abs_bound (μ.prod μ) hm hb
  have hH : Measurable H :=
    (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ h hm.stronglyMeasurable).measurable
  have hr := bounded_kernel_rowFactorial μ H hH (4 * L) (by positivity)
    (abs_hoeffdingCentered_le μ h hm L hb)
  obtain ⟨hcan, hbound⟩ := DGRHS.Attractive.attractiveCanonical_uniform_exponential μ H hH
    (4 * L) hr (DGRHS.centeredKernel_symmetric μ (fun a b => h (a, b)) hs)
    (DGRHS.integral_centeredKernel_left μ (fun a b => h (a, b)) hi) (-t)
    (by simpa [mul_assoc] using ht) N
  let f := fun x : Fin N → X => Real.exp
    (t * (N : ℝ) * sourceTransportEnergy μ h N x)
  let B := Real.exp (3 * |t| * L)
  have hf : Measurable f := by
    have he : f = fun x => Real.exp
        ((-t) * DGRHS.Attractive.attractiveNormalizedStatistic N H x +
          t * sourceTransportCorrection μ h N x) := by
      funext x
      unfold f
      rw [mul_assoc, sourceTransportEnergy_scaled μ h N hN]
      congr 1
      dsimp [H]
      ring
    rw [he]
    exact Real.measurable_exp.comp
      (((DGRHS.Attractive.attractiveNormalizedStatistic_measurable N H hH).const_mul (-t)).add
        ((measurable_sourceTransportCorrection μ h hm N).const_mul t))
  have hpoint (x : Fin N → X) : f x ≤ B *
      Real.exp ((-t) * DGRHS.Attractive.attractiveNormalizedStatistic N H x) := by
    have hR := abs_sourceTransportCorrection_le μ h hm L hb N hN x
    have hc : t * sourceTransportCorrection μ h N x ≤ 3 * |t| * L := by
      have hprod := le_abs_self (t * sourceTransportCorrection μ h N x)
      rw [abs_mul] at hprod
      nlinarith [mul_le_mul_of_nonneg_left hR (abs_nonneg t)]
    unfold f B
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [mul_assoc, sourceTransportEnergy_scaled μ h N hN]
    linarith
  have hfi : Integrable f (Measure.pi (fun _ : Fin N => μ)) :=
    (hcan.const_mul B).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        change |Real.exp (t * (N : ℝ) * sourceTransportEnergy μ h N x)| ≤ _
        rw [abs_of_pos (Real.exp_pos _)]
        exact hpoint x)
  refine ⟨hfi, ?_⟩
  calc
    _ ≤ ∫ x : Fin N → X, B * Real.exp
        ((-t) * DGRHS.Attractive.attractiveNormalizedStatistic N H x)
        ∂Measure.pi (fun _ : Fin N => μ) :=
      integral_mono_ae hfi (hcan.const_mul B) (Filter.Eventually.of_forall hpoint)
    _ = B * ∫ x : Fin N → X, Real.exp
        ((-t) * DGRHS.Attractive.attractiveNormalizedStatistic N H x)
        ∂Measure.pi (fun _ : Fin N => μ) := integral_const_mul _ _
    _ ≤ B * (2 / (1 - ((-t) * (DGRHS.Attractive.attractiveMomentConstant * (4 * L))) ^ 2)) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = _ := by simp [B, mul_assoc]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.boundedKernel_energy_exponential
