import DGRHS.Gaussian.PeriodicRieszLowerCutRemainder
import DGRHS.Gaussian.PeriodicRieszAdaptiveComparison
import DGRHS.Gaussian.PeriodicRieszMasterData

/-!
Packet P9f, unit 2 (part 1): near-field/band/tail decomposition of the lower-cut family
`g_ε = periodicRieszPhysicalTail s 0 ε` and its particle comparison.

For `0 < ε ≤ δ ≤ a ≤ 1` the lower cut splits (a.e. Haar, then a.e. on distinct iid particles) as
`g_ε = Band(δ,a) + Band(ε,δ) + Tail(a) + const`: the middle piece is nonnegative with exact mass
`F (δ^h - ε^h)/h`, hence its centered negative statistic obeys the same bounded-density bound as the
short-time piece of the heat-shift family; the lower cut never sees heat times below `ε`, which is the
reason for the full-range moment bound.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicRieszPositiveShort_ae_split (s τ ε δ : ℝ) (hsd : s < (Fintype.card ι : ℝ))
    (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hεδ : ε ≤ δ) :
    periodicRieszPositiveShort (ι := ι) s τ δ =ᵐ[periodicHaar ι]
      (fun x => periodicRieszPositiveShort s τ ε x + periodicRieszPositiveBand s τ ε δ x) := by
  filter_upwards [periodicPositiveMellinShort_ae_split (ι := ι) (((Fintype.card ι : ℝ) - s) / 2 - 1)
    τ ε δ (periodicUnshiftedMellin_spectralExponent _ s hsd) hτ hε hεδ] with x hx
  unfold periodicRieszPositiveShort periodicRieszPositiveBand
  rw [hx]; ring

lemma periodicRieszPositiveBand_integrable (s τ ε δ : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    Integrable (periodicRieszPositiveBand (ι := ι) s τ ε δ) (periodicHaar ι) := by
  have hF := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
  refine (periodicRieszPositiveShort_integrable (ι := ι) s τ δ hsd hτ).mono'
    (periodicRieszPositiveBand_measurable (ι := ι) s τ ε δ).aestronglyMeasurable ?_
  filter_upwards [periodicPositiveMellinBand_ae_le_short (ι := ι) (((Fintype.card ι : ℝ) - s) / 2 - 1)
    τ ε δ (periodicUnshiftedMellin_spectralExponent _ s hsd) hτ hε] with x hx
  have hb0 : 0 ≤ periodicRieszPositiveBand (ι := ι) s τ ε δ x :=
    mul_nonneg hF (periodicPositiveMellinBand_nonneg _ τ ε δ hτ hε x)
  rw [Real.norm_of_nonneg hb0]
  unfold periodicRieszPositiveBand periodicRieszPositiveShort
  exact mul_le_mul_of_nonneg_left hx hF

lemma periodicRieszPositiveBand_nonneg (s τ ε δ : ℝ) (hs : 0 < s) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (x : PeriodicTorus ι) : 0 ≤ periodicRieszPositiveBand s τ ε δ x :=
  mul_nonneg (periodicRieszMellinFactor_pos (ι := ι) s hs).le
    (periodicPositiveMellinBand_nonneg _ τ ε δ hτ hε x)

/-- Exact mass of a heat-time band. -/
lemma periodicRieszPositiveBand_mass (s τ ε δ : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hεδ : ε ≤ δ) :
    (∫ x, periodicRieszPositiveBand s τ ε δ x ∂periodicHaar ι) =
      periodicRieszMellinFactor ι s *
        (δ ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)) -
      periodicRieszMellinFactor ι s *
        (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)) := by
  have hδ : 0 ≤ δ := hε.trans hεδ
  have h1 := integral_congr_ae (periodicRieszPositiveShort_ae_split (ι := ι) s τ ε δ hsd hτ hε hεδ)
  rw [integral_add (periodicRieszPositiveShort_integrable s τ ε hsd hτ)
    (periodicRieszPositiveBand_integrable s τ ε δ hs hsd hτ hε),
    periodicRieszPositiveShort_mass s τ δ hsd hτ hδ, periodicRieszPositiveShort_mass s τ ε hsd hτ hε] at h1
  linarith

lemma periodicRieszPositiveBand_density_particle_bound (s τ ε δ : ℝ)
    (hs : 0 < s) (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q => periodicRieszPositiveBand s τ ε δ (q.1 - q.2))) x ≤
      (N : ℝ) * (M * (periodicRieszMellinFactor ι s *
        (δ ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)) -
        periodicRieszMellinFactor ι s *
        (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)))) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hh : 0 < ((Fintype.card ι : ℝ) - s) / 2 := by linarith
  have hmass := periodicRieszPositiveBand_mass (ι := ι) s τ ε δ hs hsd hτ hε hεδ
  apply ae_physical_iidNegativeStatistic_bound (periodicCappedDensityMeasure ρ) N hN
  · rw [← hmass]
    exact mul_nonneg hM (integral_nonneg fun x => periodicRieszPositiveBand_nonneg s τ ε δ hs hτ hε x)
  · refine Eventually.of_forall (fun p => ?_)
    have h := periodicDensityCentered_nonnegative_lower ρ M hM hρ _
      (periodicRieszPositiveBand_integrable s τ ε δ hs hsd hτ hε)
      (periodicRieszPositiveBand_nonneg s τ ε δ hs hτ hε) p
    rwa [hmass] at h

/-- The lower-cut tail splits into band, intermediate band and upper tail (a.e. Haar). -/
lemma periodicRieszPhysicalTail_ae_band_split (s ε δ a : ℝ) (hsd : s < (Fintype.card ι : ℝ))
    (hε : 0 < ε) (hεδ : ε ≤ δ) (hδa : δ ≤ a) :
    periodicRieszPhysicalTail (ι := ι) s 0 ε =ᵐ[periodicHaar ι]
      (fun x => ((periodicRieszPositiveBand s 0 δ a x + periodicRieszPositiveBand s 0 ε δ x) +
        periodicRieszPhysicalTail s 0 a x) +
        (periodicRieszMellinFactor ι s *
          (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)) -
         periodicRieszMellinFactor ι s *
          (a ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)))) := by
  filter_upwards [periodicRieszMellinGreen_sub_tail_ae (ι := ι) s 0 ε hsd le_rfl hε.le,
    periodicRieszMellinGreen_ae_time_split (ι := ι) s 0 δ a hsd le_rfl (hε.le.trans hεδ) hδa,
    periodicRieszPositiveShort_ae_split (ι := ι) s 0 ε δ hsd le_rfl hε.le hεδ] with x h1 h2 h3
  try dsimp only at h1 h2 h3 ⊢
  linarith

lemma periodicRieszPhysicalTail_centered_ae_split (s ε δ a : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (hεδ : ε ≤ δ) (hδa : δ ≤ a) (ha1 : a ≤ 1)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 ε (q.1 - q.2))
      =ᵐ[(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s 0 δ a (q.1 - q.2)) +
         hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s 0 ε δ (q.1 - q.2))) +
         hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 a (q.1 - q.2)) := by
  let μ := periodicCappedDensityMeasure ρ
  have hδ : 0 < δ := hε.trans_le hεδ
  have ha : 0 < a := hδ.trans_le hδa
  let W : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun q => periodicRieszPositiveBand s 0 δ a (q.1 - q.2)
  let V : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun q => periodicRieszPositiveBand s 0 ε δ (q.1 - q.2)
  let R : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun q => periodicRieszPhysicalTail s 0 a (q.1 - q.2)
  let C : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun _ =>
    periodicRieszMellinFactor ι s *
          (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)) -
         periodicRieszMellinFactor ι s *
          (a ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2))
  have hW : Integrable W (μ.prod μ) :=
    (periodicRieszPositiveBand_pair_proper s 0 δ a hs le_rfl hδ ha1 μ).2.2
  have hV : Integrable V (μ.prod μ) :=
    (periodicRieszPositiveBand_pair_proper s 0 ε δ hs le_rfl hε (hδa.trans ha1) μ).2.2
  have hR : Integrable R (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _
      (periodicRieszPhysicalTail_integrable s 0 a hsd le_rfl ha.le)
  have he : (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszPhysicalTail s 0 ε (q.1 - q.2)) =ᵐ[μ.prod μ] ((W + V) + R) + C :=
    periodicDensity_pair_ae_of_haar ρ _
      (periodicRieszPhysicalTail_ae_band_split s ε δ a hsd hε hεδ hδa)
  have h1 := ae_hoeffdingCentered_congr μ _ _ he
  have h2 := ae_hoeffdingCentered_add μ ((W + V) + R) C ((hW.add hV).add hR) (integrable_const _)
  have h3 := ae_hoeffdingCentered_add μ (W + V) R (hW.add hV) hR
  have h4 := ae_hoeffdingCentered_add μ W V hW hV
  have hC : hoeffdingCentered μ C = 0 := periodicHoeffdingCentered_constant μ _
  filter_upwards [h1, h2, h3, h4] with q hq1 hq2 hq3 hq4
  rw [hq1, hq2]
  simp only [Pi.add_apply, hC, Pi.zero_apply, add_zero]
  rw [hq3]
  simp only [Pi.add_apply]
  rw [hq4]
  rfl

lemma periodicRieszPhysicalTail_particle_ae_split (s ε δ a : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (hεδ : ε ≤ δ) (hδa : δ ≤ a) (ha1 : a ≤ 1)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 ε (q.1 - q.2))) x =
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s 0 δ a (q.1 - q.2))) x +
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s 0 ε δ (q.1 - q.2))) x +
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 a (q.1 - q.2))) x := by
  have he := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) N _ _
    (periodicRieszPhysicalTail_centered_ae_split s ε δ a hs hsd hε hεδ hδa ha1 ρ M hρ)
  filter_upwards [he] with x hx
  rw [hx, physical_iidNegativeStatistic_add, physical_iidNegativeStatistic_add]

/-- The particle comparison for the lower cut (analogue of `periodicRieszMellinGreen_particle_comparison`). -/
lemma periodicRieszPhysicalTail_particle_comparison (s ε δ a β : ℝ)
    (hs : 0 < s) (hsd : s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (hεδ : ε ≤ δ) (hδa : δ ≤ a)
    (ha1 : a ≤ 1) (hβ : 0 ≤ β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      β * iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 ε (q.1 - q.2))) x ≤
      β * iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s 0 δ a (q.1 - q.2))) x +
      β * (N : ℝ) * (M * (periodicRieszMellinFactor ι s *
        (δ ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)) -
        periodicRieszMellinFactor ι s *
        (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)))) +
      β * (2 * periodicRieszMellinFactor ι s * periodicHeatDiagonalGlobalConstant ι *
        (a ^ (-s / 2) / (s / 2))) := by
  have hδ : 0 < δ := hε.trans_le hεδ
  have ha : 0 < a := hδ.trans_le hδa
  filter_upwards [periodicRieszPhysicalTail_particle_ae_split s ε δ a hs hsd hε hεδ hδa ha1 ρ M hρ N,
    periodicRieszPositiveBand_density_particle_bound s 0 ε δ hs hsd le_rfl hε.le hεδ ρ M hM hρ N hN]
    with x hsplit hnear
  have htail := periodicRieszPhysicalTail_particle_cap s 0 a hs le_rfl ha
    (periodicCappedDensityMeasure ρ) N hN x
  rw [hsplit]
  have hn := mul_le_mul_of_nonneg_left hnear hβ
  have ht := mul_le_mul_of_nonneg_left htail hβ
  nlinarith

end DGRHS.Periodic
