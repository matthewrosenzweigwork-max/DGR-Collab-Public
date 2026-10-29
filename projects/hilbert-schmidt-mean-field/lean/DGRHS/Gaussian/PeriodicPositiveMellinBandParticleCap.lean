import DGRHS.Gaussian.PeriodicPositiveMellinBandSup
import DGRHS.Gaussian.PeriodicMellinTailParticleCap

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Proper parameter centering and the actual
heat Gram cap give a particle-number-independent positive-band cap. The raw
heat retains its zero mode; its cancellation is pointwise after properness.
No product-AE assertion is restricted to a particle diagonal. This is a
time-band adaptation, not the source's literal Fourier-cutoff lemma. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicRieszPositivePairIntegrand (s τ : ℝ)
    (q : ℝ × (PeriodicTorus ι × PeriodicTorus ι)) : ℝ :=
  periodicPositiveMellinIntegrand (((Fintype.card ι : ℝ)-s)/2-1) τ q.1 (q.2.1-q.2.2)

lemma periodicRieszPositivePairIntegrand_measurable (s τ : ℝ) :
    Measurable (periodicRieszPositivePairIntegrand (ι := ι) s τ) :=
  (periodicPositiveMellinIntegrand_measurable _ τ).comp
    (show Measurable (fun q : ℝ × (PeriodicTorus ι × PeriodicTorus ι) =>
      (q.1,q.2.1-q.2.2)) by fun_prop)

lemma periodicPositiveMellinBand_centering_commutes (s τ δ a : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    Integrable (fun t => hoeffdingCentered μ
      (fun q => periodicRieszPositivePairIntegrand s τ (t,q)) p) (volume.restrict (Ioc δ a)) ∧
    hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicPositiveMellinBand (((Fintype.card ι : ℝ)-s)/2-1) τ δ a (q.1-q.2)) p =
      ∫ t : ℝ in Ioc δ a,
        hoeffdingCentered μ (fun q => periodicRieszPositivePairIntegrand s τ (t,q)) p := by
  let ν : Measure ℝ := volume.restrict (Ioc δ a)
  let B : ℝ → ℝ := fun t => periodicHeatDiagonalSmallConstant ι * t^(-s/2-1)
  have hm := (periodicRieszPositivePairIntegrand_measurable (ι := ι) s τ).stronglyMeasurable
  have hi : Integrable B ν :=
    IntegrableOn.mono_set
      ((integrableOn_Ioi_rpow_of_lt (by linarith : -s/2-1 < -1) hδ).const_mul
        (periodicHeatDiagonalSmallConstant ι)) (fun _ ht => ht.1)
  have hb : ∀ᵐ t ∂ν, ∀ q : PeriodicTorus ι × PeriodicTorus ι,
      ‖periodicRieszPositivePairIntegrand s τ (t,q)‖ ≤ B t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro q
    exact periodicPositiveMellinIntegrand_small_norm_bound s τ t
      (hδ.trans ht.1) (ht.2.trans ha1) hτ (q.1-q.2)
  exact ⟨integrable_parameter_hoeffdingCentered_of_envelope ν μ _ hm B hi hb p,
    hoeffdingCentered_integral_parameter_of_envelope ν μ _ hm B hi hb p⟩

/-- The constant removed from the full heat is canceled after each actual
row and pair integral is proper. This equality holds at every spatial pair. -/
lemma periodicRieszPositivePairIntegrand_centered_eq_tail (s τ t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hτ : 0 ≤ τ)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    hoeffdingCentered μ (fun q => periodicRieszPositivePairIntegrand s τ (t,q)) p =
      hoeffdingCentered μ (fun q => periodicRieszPairTailIntegrand s τ (t,q)) p := by
  let H : PeriodicTorus ι × PeriodicTorus ι → ℝ :=
    fun q => periodicRieszPositivePairIntegrand s τ (t,q)
  let c : ℝ := t^(((Fintype.card ι : ℝ)-s)/2-1)
  have hm : StronglyMeasurable H :=
    (periodicRieszPositivePairIntegrand_measurable s τ).stronglyMeasurable.comp_measurable
      (show Measurable (fun q : PeriodicTorus ι × PeriodicTorus ι => (t,q)) by fun_prop)
  have hb (q : PeriodicTorus ι × PeriodicTorus ι) :
      ‖H q‖ ≤ periodicHeatDiagonalSmallConstant ι * t^(-s/2-1) :=
    periodicPositiveMellinIntegrand_small_norm_bound s τ t ht ht1 hτ (q.1-q.2)
  have he : (fun q => H q-c) = (fun q => periodicRieszPairTailIntegrand s τ (t,q)) := by
    funext q
    dsimp [H,c,periodicRieszPositivePairIntegrand,periodicPositiveMellinIntegrand,
      periodicRieszPairTailIntegrand]
    ring
  have hc := hoeffdingCentered_sub_const_of_pointwise_bound μ H hm _ hb c p
  rw [he] at hc
  exact hc.symm

lemma periodicPositiveMellinBand_particle_cap (s τ δ a : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    iidNegativeStatistic N (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι =>
        periodicPositiveMellinBand (((Fintype.card ι : ℝ)-s)/2-1) τ δ a (q.1-q.2))) x ≤
      2*periodicHeatDiagonalGlobalConstant ι * (δ^(-s/2)/(s/2)) := by
  let ν : Measure ℝ := volume.restrict (Ioc δ a)
  let H := fun (t : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) =>
    hoeffdingCentered μ (fun q => periodicRieszPositivePairIntegrand s τ (t,q)) p
  have hi (p : PeriodicTorus ι × PeriodicTorus ι) : Integrable (fun t => H t p) ν :=
    (periodicPositiveMellinBand_centering_commutes s τ δ a hs hτ hδ ha1 μ p).1
  have he : hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicPositiveMellinBand (((Fintype.card ι : ℝ)-s)/2-1) τ δ a (q.1-q.2)) =
      fun q => ∫ t, H t q ∂ν := by
    funext q
    exact (periodicPositiveMellinBand_centering_commutes s τ δ a hs hτ hδ ha1 μ q).2
  rw [he, ← integral_iidNegativeStatistic_parameter ν H hi N x]
  have heIoi : Integrable (fun t : ℝ => 2*periodicHeatDiagonalGlobalConstant ι*t^(-s/2-1))
      (volume.restrict (Ioi δ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s/2-1 < -1) hδ).const_mul _
  have heIoc : Integrable (fun t : ℝ => 2*periodicHeatDiagonalGlobalConstant ι*t^(-s/2-1)) ν :=
    IntegrableOn.mono_set heIoi (fun _ ht => ht.1)
  calc
    _ ≤ ∫ t, 2*periodicHeatDiagonalGlobalConstant ι*t^(-s/2-1) ∂ν := by
      apply integral_mono_ae (integrable_iidNegativeStatistic_parameter ν H hi N x) heIoc
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hEq : H t = hoeffdingCentered μ (fun q => periodicRieszPairTailIntegrand s τ (t,q)) := by
        funext q
        exact periodicRieszPositivePairIntegrand_centered_eq_tail s τ t
          (hδ.trans ht.1) (ht.2.trans ha1) hτ μ q
      rw [hEq]
      exact periodicRieszTailIntegrand_particle_cap s τ t (hδ.trans ht.1) hτ μ N hN x
    _ ≤ ∫ t : ℝ in Ioi δ, 2*periodicHeatDiagonalGlobalConstant ι*t^(-s/2-1) := by
      apply setIntegral_mono_set heIoi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (mul_nonneg (by norm_num) periodicHeatDiagonalGlobalConstant_nonneg)
          (Real.rpow_nonneg (hδ.trans ht).le _)
      · exact Eventually.of_forall (fun t ht => ht.1)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s/2-1 < -1) hδ]
      rw [show -s/2-1+1 = -(s/2) by ring]
      congr 1
      simp only [div_neg, neg_div, neg_neg]

lemma periodicRieszPositiveBand_particle_cap (s τ δ a : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    iidNegativeStatistic N (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (q.1-q.2))) x ≤
      2*periodicRieszMellinFactor ι s*periodicHeatDiagonalGlobalConstant ι * (δ^(-s/2)/(s/2)) := by
  have hF := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
  have he : hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (q.1-q.2)) =
      periodicRieszMellinFactor ι s • hoeffdingCentered μ
        (fun q : PeriodicTorus ι × PeriodicTorus ι =>
          periodicPositiveMellinBand (((Fintype.card ι : ℝ)-s)/2-1) τ δ a (q.1-q.2)) := by
    funext q
    exact hoeffdingCentered_const_mul_pointwise μ _ _ q
  rw [he, physical_iidNegativeStatistic_const_smul]
  convert mul_le_mul_of_nonneg_left
    (periodicPositiveMellinBand_particle_cap s τ δ a hs hτ hδ ha1 μ N hN x) hF using 1 <;> ring

end DGRHS.Periodic
