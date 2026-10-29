import DGRHS.Gaussian.PeriodicMellinCenteringFubini
import DGRHS.Gaussian.PeriodicCenteredHeatGram
import DGRHS.Gaussian.PhysicalStatisticAlgebra

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. The actual positive-cutoff Mellin tail has a
uniform-in-N deterministic negative-statistic cap. Proper centering/Fubini,
the finite off-diagonal sum and the actual nonzero heat Gram bound are used.
This cutoff-dependent cap alone is NOT a uniform exponential-moment theorem. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Gaussian
open DGRHS.Concentration
universe u v
variable {T : Type u} {X : Type v} [MeasurableSpace T]

lemma integrable_iidNegativeStatistic_parameter (ν : Measure T)
    (H : T → X × X → ℝ) (hH : ∀ p, Integrable (fun t => H t p) ν)
    (N : ℕ) (x : Fin N → X) :
    Integrable (fun t => iidNegativeStatistic N (H t) x) ν := by
  have hi (i j : Fin N) : Integrable (fun t => if i ≠ j then H t (x i,x j) else 0) ν := by
    by_cases hij : i ≠ j
    · simpa only [if_pos hij] using hH (x i,x j)
    · simp only [if_neg hij]
      exact integrable_const_iff.2 (Or.inl rfl)
  exact ((integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))).neg).div_const _

lemma integral_iidNegativeStatistic_parameter (ν : Measure T)
    (H : T → X × X → ℝ) (hH : ∀ p, Integrable (fun t => H t p) ν)
    (N : ℕ) (x : Fin N → X) :
    (∫ t, iidNegativeStatistic N (H t) x ∂ν) =
      iidNegativeStatistic N (fun p => ∫ t, H t p ∂ν) x := by
  have hi (i j : Fin N) : Integrable (fun t => if i ≠ j then H t (x i,x j) else 0) ν := by
    by_cases hij : i ≠ j
    · simpa only [if_pos hij] using hH (x i,x j)
    · simp only [if_neg hij]
      exact integrable_const_iff.2 (Or.inl rfl)
  unfold iidNegativeStatistic iidCoupledSum DGRHS.Decoupling.offDiagonalSum
  rw [integral_div, integral_neg,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i ≠ j
  · simp only [if_pos hij]
  · simp only [if_neg hij, integral_zero]

end DGRHS.Gaussian

namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicRieszTailIntegrand_particle_cap (s τ t : ℝ)
    (ht : 0 < t) (hτ : 0 ≤ τ)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    iidNegativeStatistic N (hoeffdingCentered μ
      (fun p => periodicRieszPairTailIntegrand s τ (t,p))) x ≤
      2 * periodicHeatDiagonalGlobalConstant ι * t ^ (-s / 2 - 1) := by
  let c : ℝ := t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1)
  let W : PeriodicTorus ι × PeriodicTorus ι → ℝ :=
    fun p => (periodicGaussianHeat (t + τ) (p.1 - p.2)).re - 1
  have hc : 0 ≤ c := Real.rpow_nonneg ht.le _
  have htτ := add_pos_of_pos_of_nonneg ht hτ
  have hcap : iidNegativeStatistic N (hoeffdingCentered μ W) x ≤
      2 * ((periodicGaussianHeat (t + τ) (0 : PeriodicTorus ι)).re - 1) := by
    simpa only [iidNegativeStatistic, iidCoupledSum, DGRHS.Decoupling.offDiagonalSum,
      ite_not] using periodicCenteredHeat_centered_particle_cap (t + τ) htτ μ N hN x
  have hdiag : (periodicGaussianHeat (t + τ) (0 : PeriodicTorus ι)).re - 1 ≤
      periodicHeatDiagonalGlobalConstant ι * t ^ (-((Fintype.card ι : ℝ) / 2)) := by
    have hre := Complex.abs_re_le_norm (periodicGaussianHeat (t + τ) (0 : PeriodicTorus ι) - 1)
    simp only [Complex.sub_re, Complex.one_re] at hre
    exact (le_abs_self _).trans (hre.trans
      (periodicGaussianHeat_centered_shifted_power_bound t τ ht hτ 0))
  have he : hoeffdingCentered μ (fun p => periodicRieszPairTailIntegrand s τ (t,p)) =
      c • hoeffdingCentered μ W := by
    funext p
    exact hoeffdingCentered_const_mul_pointwise μ W c p
  rw [he, physical_iidNegativeStatistic_const_smul]
  calc
    _ ≤ c * (2 * ((periodicGaussianHeat (t + τ) (0 : PeriodicTorus ι)).re - 1)) :=
      mul_le_mul_of_nonneg_left hcap hc
    _ ≤ c * (2 * (periodicHeatDiagonalGlobalConstant ι *
        t ^ (-((Fintype.card ι : ℝ) / 2)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiag (by norm_num)) hc
    _ = _ := by
      dsimp [c]
      rw [show t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
          (2 * (periodicHeatDiagonalGlobalConstant ι * t ^ (-((Fintype.card ι : ℝ) / 2)))) =
          (2 * periodicHeatDiagonalGlobalConstant ι) *
            (t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
             t ^ (-((Fintype.card ι : ℝ) / 2))) by ring,
        ← Real.rpow_add ht]
      congr 2
      ring

lemma periodicRieszMellinTail_particle_cap (s τ ε : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    iidNegativeStatistic N (hoeffdingCentered μ
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinTail s τ ε (p.1 - p.2))) x ≤
      2 * periodicHeatDiagonalGlobalConstant ι * (ε ^ (-s / 2) / (s / 2)) := by
  let ν : Measure ℝ := volume.restrict (Ioi ε)
  let H := fun (t : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) =>
    hoeffdingCentered μ (fun q => periodicRieszPairTailIntegrand s τ (t,q)) p
  have hi (p : PeriodicTorus ι × PeriodicTorus ι) : Integrable (fun t => H t p) ν :=
    (periodicRieszMellinTail_centering_commutes s τ ε hs hτ hε μ p).1
  have he : hoeffdingCentered μ
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinTail s τ ε (p.1 - p.2)) =
      fun p => ∫ t, H t p ∂ν := by
    funext p
    exact (periodicRieszMellinTail_centering_commutes s τ ε hs hτ hε μ p).2
  rw [he, ← integral_iidNegativeStatistic_parameter ν H hi N x]
  have henv : Integrable (fun t : ℝ =>
      2 * periodicHeatDiagonalGlobalConstant ι * t ^ (-s / 2 - 1)) ν :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s / 2 - 1 < -1) hε).const_mul _
  calc
    _ ≤ ∫ t, 2 * periodicHeatDiagonalGlobalConstant ι * t ^ (-s / 2 - 1) ∂ν := by
      apply integral_mono_ae (integrable_iidNegativeStatistic_parameter ν H hi N x) henv
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact periodicRieszTailIntegrand_particle_cap s τ t (hε.trans ht) hτ μ N hN x
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s / 2 - 1 < -1) hε]
      rw [show -s / 2 - 1 + 1 = -(s / 2) by ring]
      congr 1
      simp only [div_neg, neg_div, neg_neg]

lemma periodicRieszPhysicalTail_particle_cap (s τ ε : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    iidNegativeStatistic N (hoeffdingCentered μ
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s τ ε (p.1 - p.2))) x ≤
      2 * periodicRieszMellinFactor ι s * periodicHeatDiagonalGlobalConstant ι *
        (ε ^ (-s / 2) / (s / 2)) := by
  have hc := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
  have he : hoeffdingCentered μ
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s τ ε (p.1 - p.2)) =
      periodicRieszMellinFactor ι s • hoeffdingCentered μ
        (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinTail s τ ε (p.1 - p.2)) := by
    funext p
    exact hoeffdingCentered_const_mul_pointwise μ _ _ p
  rw [he, physical_iidNegativeStatistic_const_smul]
  convert mul_le_mul_of_nonneg_left
    (periodicRieszMellinTail_particle_cap s τ ε hs hτ hε μ N hN x) hc using 1 <;> ring

end DGRHS.Periodic
