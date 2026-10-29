import DGRHS.Gaussian.PeriodicPositiveMellinBandParticleCap
import DGRHS.Gaussian.PeriodicPositiveMellinNearField
import DGRHS.Gaussian.GaussianRieszParticleSplit

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Actual near/band/tail decomposition of the
physical Mellin representative. The zero-mode mass is retained until proper
centering. Haar-AE identities transfer through actual absolute continuity
and only DISTINCT iid coordinates; no diagonal version is asserted. This
positive-time-band argument is a labeled alternative to the supplied
Fourier-cutoff proof, whose separate original obligations remain open. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicPositiveMellinShort_ae_split (p τ δ a : ℝ) (hp : -1 < p)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hδa : δ ≤ a) :
    periodicPositiveMellinShort (ι := ι) p τ a =ᵐ[periodicHaar ι]
      (fun x => periodicPositiveMellinShort p τ δ x + periodicPositiveMellinBand p τ δ a x) := by
  have hset : Ioc (0 : ℝ) δ ∪ Ioc δ a = Ioc 0 a := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact ⟨ht.1,ht.2.trans hδa⟩
      · exact ⟨hδ.trans_lt ht.1,ht.2⟩
    · rintro ⟨ht0,hta⟩
      by_cases htδ : t ≤ δ
      · exact Or.inl ⟨ht0,htδ⟩
      · exact Or.inr ⟨lt_of_not_ge htδ,hta⟩
  have hdis : Disjoint (Ioc (0 : ℝ) δ) (Ioc δ a) :=
    Set.disjoint_left.mpr (fun t ht hy => (not_lt_of_ge ht.2) hy.1)
  filter_upwards [(periodicPositiveMellinIntegrand_product_integrable
    (ι := ι) p τ a hp hτ).prod_left_ae] with x hx
  have hleft := IntegrableOn.mono_set hx (show Ioc (0 : ℝ) δ ⊆ Ioc 0 a from
    fun t ht => ⟨ht.1,ht.2.trans hδa⟩)
  have hright := IntegrableOn.mono_set hx (show Ioc δ a ⊆ Ioc (0 : ℝ) a from
    fun t ht => ⟨hδ.trans_lt ht.1,ht.2⟩)
  change (∫ t : ℝ in Ioc 0 a, periodicPositiveMellinIntegrand p τ t x) =
    (∫ t : ℝ in Ioc 0 δ, periodicPositiveMellinIntegrand p τ t x) +
      (∫ t : ℝ in Ioc δ a, periodicPositiveMellinIntegrand p τ t x)
  rw [← hset]
  exact setIntegral_union hdis measurableSet_Ioc hleft hright

lemma periodicRieszMellinGreen_ae_time_split (s τ δ a : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hδa : δ ≤ a) :
    periodicRieszMellinGreen (ι := ι) s τ =ᵐ[periodicHaar ι]
      (fun x => (periodicRieszPositiveBand s τ δ a x + periodicRieszPositiveShort s τ δ x) +
        periodicRieszPhysicalTail s τ a x - periodicRieszMellinFactor ι s *
          (a^(((Fintype.card ι : ℝ)-s)/2)/(((Fintype.card ι : ℝ)-s)/2))) := by
  filter_upwards [periodicPositiveMellinShort_ae_split
    (ι := ι) (((Fintype.card ι : ℝ)-s)/2-1) τ δ a
    (periodicUnshiftedMellin_spectralExponent _ s hsd) hτ hδ hδa,
    periodicRieszMellinGreen_sub_tail_ae s τ a hsd hτ (hδ.trans hδa)] with x hsplit htail
  change periodicRieszMellinGreen s τ x - periodicRieszPhysicalTail s τ a x = _ at htail
  dsimp only [periodicRieszPositiveShort] at htail
  rw [hsplit] at htail
  dsimp only [periodicRieszPositiveShort,periodicRieszPositiveBand]
  linarith

lemma periodicDensity_pair_ae_of_haar (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (P : PeriodicTorus ι → Prop) (hP : ∀ᵐ x ∂periodicHaar ι,P x) :
    ∀ᵐ q : PeriodicTorus ι × PeriodicTorus ι
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ), P (q.1-q.2) := by
  have hac : periodicCappedDensityMeasure ρ ≪ periodicHaar ι :=
    withDensity_absolutelyContinuous _ _
  exact (hac.prod hac).ae_le
    ((periodicHaar_preserving_difference (ι := ι)).quasiMeasurePreserving.ae hP)

lemma periodicHoeffdingCentered_constant
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (c : ℝ) :
    hoeffdingCentered μ (fun _ => c) = 0 := by
  funext q
  simp [hoeffdingCentered,DGRHS.centeredKernel,DGRHS.potential,DGRHS.secondPotential]

lemma periodicRieszMellinGreen_centered_ae_time_split (s τ δ a : ℝ)
    (hs : 0 < s) (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) (hδa : δ ≤ a) (ha1 : a ≤ 1)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1-q.2))
      =ᵐ[(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (q.1-q.2)) +
          hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveShort s τ δ (q.1-q.2))) +
          hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s τ a (q.1-q.2)) := by
  let μ := periodicCappedDensityMeasure ρ
  let W : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun q => periodicRieszPositiveBand s τ δ a (q.1-q.2)
  let V : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun q => periodicRieszPositiveShort s τ δ (q.1-q.2)
  let R : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun q => periodicRieszPhysicalTail s τ a (q.1-q.2)
  let C : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun _ =>
    periodicRieszMellinFactor ι s * (a^(((Fintype.card ι : ℝ)-s)/2)/(((Fintype.card ι : ℝ)-s)/2))
  have hW : Integrable W (μ.prod μ) :=
    (periodicRieszPositiveBand_pair_proper s τ δ a hs hτ hδ ha1 μ).2.2
  have hV : Integrable V (μ.prod μ) :=
    periodicRieszPositiveShort_density_pair_integrable s τ δ hsd hτ ρ M hρ
  have hR : Integrable R (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _
      (periodicRieszPhysicalTail_integrable s τ a hsd hτ (hδ.le.trans hδa))
  have he : (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszMellinGreen s τ (q.1-q.2)) =ᵐ[μ.prod μ] ((W+V)+R)-C :=
    periodicDensity_pair_ae_of_haar ρ _
      (periodicRieszMellinGreen_ae_time_split s τ δ a hsd hτ hδ.le hδa)
  have h1 := ae_hoeffdingCentered_congr μ _ _ he
  have h2 := ae_hoeffdingCentered_sub μ ((W+V)+R) C ((hW.add hV).add hR) (integrable_const _)
  have h3 := ae_hoeffdingCentered_add μ (W+V) R (hW.add hV) hR
  have h4 := ae_hoeffdingCentered_add μ W V hW hV
  have hC : hoeffdingCentered μ C = 0 := periodicHoeffdingCentered_constant μ _
  filter_upwards [h1,h2,h3,h4] with q hq1 hq2 hq3 hq4
  rw [hq1,hq2]
  simp only [Pi.sub_apply,hC,Pi.zero_apply,sub_zero]
  rw [hq3]
  simp only [Pi.add_apply]
  rw [hq4]
  rfl

lemma periodicRieszMellinGreen_particle_ae_time_split (s τ δ a : ℝ)
    (hs : 0 < s) (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) (hδa : δ ≤ a) (ha1 : a ≤ 1)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1-q.2))) x =
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (q.1-q.2))) x +
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveShort s τ δ (q.1-q.2))) x +
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s τ a (q.1-q.2))) x := by
  have he := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) N _ _
    (periodicRieszMellinGreen_centered_ae_time_split s τ δ a hs hsd hτ hδ hδa ha1 ρ M hρ)
  filter_upwards [he] with x hx
  rw [hx,physical_iidNegativeStatistic_add,physical_iidNegativeStatistic_add]

lemma periodicRieszMellinGreen_particle_comparison (s τ δ a β : ℝ)
    (hs : 0 < s) (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) (hδa : δ ≤ a) (ha1 : a ≤ 1) (hβ : 0 ≤ β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      β * iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1-q.2))) x ≤
      β * iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (q.1-q.2))) x +
      β*(N : ℝ)*(M*(periodicRieszMellinFactor ι s *
        (δ^(((Fintype.card ι : ℝ)-s)/2)/(((Fintype.card ι : ℝ)-s)/2)))) +
      β*(2*periodicRieszMellinFactor ι s*periodicHeatDiagonalGlobalConstant ι * (a^(-s/2)/(s/2))) := by
  filter_upwards [periodicRieszMellinGreen_particle_ae_time_split s τ δ a hs hsd hτ hδ hδa ha1 ρ M hρ N,
    periodicRieszPositiveShort_density_particle_bound s τ δ hs hsd hτ hδ.le ρ M hM hρ N hN] with x hsplit hnear
  have htail := periodicRieszPhysicalTail_particle_cap s τ a hs hτ (hδ.trans_le hδa)
    (periodicCappedDensityMeasure ρ) N hN x
  rw [hsplit]
  have hn := mul_le_mul_of_nonneg_left hnear hβ
  have ht := mul_le_mul_of_nonneg_left htail hβ
  nlinarith

end DGRHS.Periodic
