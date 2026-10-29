import DGRHS.Gaussian.PeriodicRieszCutoffNorms
import DGRHS.Gaussian.PeriodicRieszCanonicalRate
import DGRHS.Gaussian.PeriodicCenteredAbsorb
import DGRHS.Gaussian.PeriodicRieszSingularPartition
import DGRHS.Commutator.SourceRieszLocalStatisticAlgebra

/-!
Packet P9h, unit 2 (part 23): a.e. identification of the torus Riesz kernel with the smooth pair
kernel, integrability of the transport/pair kernels against the capped-density law, the centered
splits `h̃_κ = h̃_{κ^short} + h̃_{κ^long}`, `h̃_W = h̃_{f_{2η}} + h̃_{g_{2η}}`, and the finite-particle
statistic identity of the local cutoff (torus version of `SourceRieszLocalDecomposition` and
`SourceRieszLocalStatisticAlgebra`).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma periodic_energy_normalization {X : Type*} [MeasurableSpace X] (β : ℝ) (h : X × X → ℝ) (N : ℕ) (ω : Fin N → X) :
    β * iidNegativeStatistic N h ω =
      -β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h ω := by
  have hSum : iidCoupledSum N h ω = ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else h (ω i, ω j) := by
    unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    simp only [ne_eq, ite_not]
  rw [← sourceKernelParticleStatistic_eq_normalized]
  unfold iidNegativeStatistic sourceKernelParticleStatistic
  rw [hSum]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma periodic_normalized_pair_le {X : Type*} (N : ℕ) (hN : 1 ≤ N) (U V : X × X → ℝ)
    (c d B : ℝ) (hB : 0 ≤ B) (hp : ∀ p, c * U p + d * V p ≤ B) (ω : Fin N → X) :
    -2 * c * iidNegativeStatistic N U ω - 2 * d * iidNegativeStatistic N V ω ≤ (N : ℝ) * B := by
  have h := sourceRieszLocal_normalized_pair_linear N U V c d ω
  have hn : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN)
  have hb : (∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else c * U (ω i, ω j) + d * V (ω i, ω j)) ≤
      ∑ _i : Fin N, ∑ _j : Fin N, B :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      split_ifs
      · exact hB
      · exact hp _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have h2 : 1 / (N : ℝ) * (∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else
      c * U (ω i, ω j) + d * V (ω i, ω j)) ≤ 1 / (N : ℝ) * ((N : ℝ) * ((N : ℝ) * B)) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  rw [h] at h2
  refine h2.trans (le_of_eq ?_)
  field_simp

lemma periodic_pair_ae_of_haar_ae (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) {f g : PeriodicTorus ι → ℝ}
    (h : f =ᵐ[periodicHaar ι] g) :
    (fun q : PeriodicTorus ι × PeriodicTorus ι => f (q.1 - q.2)) =ᵐ[
      (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      (fun q => g (q.1 - q.2)) := by
  have h1 := (periodicHaar_preserving_difference (ι := ι)).quasiMeasurePreserving.ae_eq_comp h
  have hac : (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ) ≪
      (periodicHaar ι).prod (periodicHaar ι) :=
    Measure.absolutelyContinuous_of_le_smul (periodicCappedDensityMeasure_prod_le ρ M hρ)
  exact hac.ae_eq h1

lemma periodicRieszKernel_pair_ae (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)) =ᵐ[
      (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      periodicRieszPair s := by
  have hG : periodicRieszKernel s hs2 =ᵐ[periodicHaar ι]
      (fun x : PeriodicTorus ι => if x = 0 then 0 else periodicRieszSmooth s (periodicCenteredLift x)) := by
    have h := periodicRieszSmoothLift_ae (ι := ι) s periodicRieszTau hs hs2 periodicRieszTau_pos
    haveI := periodicHaar_nullSingletonClass (ι := ι)
    filter_upwards [h, (periodicHaar ι).ae_ne 0] with x hx hx0
    rw [ite_eq_right hx0]
    exact hx.symm
  refine (periodic_pair_ae_of_haar_ae ρ M hρ hG).trans (Filter.Eventually.of_forall fun q => ?_)
  unfold periodicRieszPair
  simp only [sub_eq_zero]

lemma integrable_of_haar_majorant (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (g : PeriodicTorus ι → ℝ)
    (hg : Integrable g (periodicHaar ι))
    {W : PeriodicTorus ι × PeriodicTorus ι → ℝ}
    (hm : AEStronglyMeasurable W
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)))
    (hb : ∀ p, |W p| ≤ g (p.1 - p.2)) :
    Integrable W ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) :=
  (periodicDensityPair_integrable_of_haar ρ M hρ g hg).mono' hm
    (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hb p)

lemma periodicRieszShortPair_eq_fun (s η : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszShortPair s η p = periodicRieszShortFun s η (p.1 - p.2) :=
  periodicRieszShortPair_eq s η p

/-- The full transport kernel is dominated by the profile majorant (as a function on the torus). -/
lemma periodicRieszTransportKernel_bound_fun (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    |periodicRieszTransportKernel n s v p| ≤ (K : ℝ) ^ n * (periodicRieszProfileC ι s n *
      (periodicRieszMajorantFun s (p.1 - p.2) + 1)) := by
  have hC := periodicRieszProfileC_ge (ι := ι) s hs n
  have hΨ0 : 0 ≤ periodicRieszMajorantFun s (p.1 - p.2) := periodicRieszShortFun_nonneg s 1 hs _
  have hKn : 0 ≤ (K : ℝ) ^ n := by positivity
  by_cases hp : p.1 = p.2
  · simp only [periodicRieszTransportKernel, ite_eq_left hp, abs_zero]
    have := hC.2.2
    positivity
  have hκ := periodicRieszTransportKernel_bound n hn s hs hs2 hv p
  have hΨeq : periodicRieszMajorant s (periodicCenteredLift (p.1 - p.2)) =
      periodicRieszMajorantFun s (p.1 - p.2) := by
    unfold periodicRieszMajorantFun periodicRieszShortFun periodicRieszShortSum periodicRieszMajorant
    rw [ite_eq_right (sub_ne_zero.mpr hp)]
  rw [hΨeq] at hκ
  refine hκ.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hKn
  nlinarith [mul_le_mul_of_nonneg_right hC.1 hΨ0]

lemma periodicRieszShortTransport_bound_fun (n : ℕ) (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    |periodicRieszShortTransport n s η v p| ≤ sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s *
      (K : ℝ) ^ n * periodicRieszShortFun s (2 * η) (p.1 - p.2) := by
  have hCn := (sourceRieszGaussianDerivativeConstant_pos n).le
  have hf0 := periodicRieszShortFun_nonneg (ι := ι) s (2 * η) hs (p.1 - p.2)
  by_cases hp : p.1 = p.2
  · simp only [periodicRieszShortTransport, ite_eq_left hp, abs_zero]
    positivity
  have h := periodicRieszShortTransport_bound n s η hs hη hv p
  refine h.trans (le_of_eq ?_)
  unfold periodicRieszShortFun
  rw [ite_eq_right (sub_ne_zero.mpr hp)]

lemma periodicRieszShortFun_even (s η : ℝ) (x : PeriodicTorus ι) :
    periodicRieszShortFun s η (-x) = periodicRieszShortFun s η x := by
  have h := periodicRieszShortPair_symm (ι := ι) s η (x, 0)
  simp only [periodicRieszShortPair_eq, Prod.fst_swap, Prod.snd_swap, zero_sub, sub_zero] at h
  exact h

/-! ### Integrability -/


lemma integrable_periodicRieszShortPair (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (s η : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hη : 0 < η) :
    Integrable (periodicRieszShortPair (ι := ι) s η)
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) := by
  have h := periodicDensityPair_integrable_of_haar ρ M hρ _ (periodicRieszShortFun_integrable s η hs hs2 hη)
  exact h.congr (Filter.Eventually.of_forall fun p => (periodicRieszShortPair_eq s η p).symm)

lemma integrable_periodicRieszShortTransport (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (n : ℕ) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) {K : ℝ≥0} {v : PeriodicTorus ι → E}
    (hv : LipschitzWith K v) :
    Integrable (periodicRieszShortTransport (ι := ι) n s η v)
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) := by
  have hCn := (sourceRieszGaussianDerivativeConstant_pos n).le
  have hg := (periodicRieszShortFun_integrable (ι := ι) s (2 * η) hs hs2 (by positivity)).const_mul
    (sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s * (K : ℝ) ^ n)
  refine integrable_of_haar_majorant ρ M hρ _ hg
    (measurable_periodicRieszShortTransport n s η hs hη hv).aestronglyMeasurable ?_
  intro p
  exact periodicRieszShortTransport_bound_fun n s η hs hη hv p

lemma integrable_periodicRieszTransportKernel (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) {K : ℝ≥0} {v : PeriodicTorus ι → E}
    (hv : LipschitzWith K v) :
    Integrable (periodicRieszTransportKernel (ι := ι) n s v)
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) := by
  have hΨ := periodicRieszShortFun_integrable (ι := ι) s 1 hs hs2 one_pos
  have hg := (hΨ.add (integrable_const (1 : ℝ))).const_mul
    ((K : ℝ) ^ n * periodicRieszProfileC ι s n)
  refine integrable_of_haar_majorant ρ M hρ _ hg
    (periodicRieszTransportKernel_measurable n hn s hs hs2 hv).aestronglyMeasurable ?_
  intro p
  have h := periodicRieszTransportKernel_bound_fun n hn s hs hs2 hv p
  refine h.trans (le_of_eq ?_)
  simp only [Pi.add_apply]
  unfold periodicRieszMajorantFun
  ring

lemma integrable_periodicRieszLongTransport (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (n : ℕ) (hn : 1 ≤ n) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hητ : η ≤ periodicRieszTau)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) :
    Integrable (periodicRieszLongTransport (ι := ι) n s η v)
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) := by
  have h := (integrable_periodicRieszTransportKernel ρ M hρ n hn s hs hs2 hv).sub
    (integrable_periodicRieszShortTransport ρ M hρ n s η hs hs2 hη hv)
  exact h.congr (Filter.Eventually.of_forall fun p =>
    (periodicRieszLongTransport_eq_sub n hn s η hs hs2 hη hητ v p).symm)

lemma integrable_periodicRieszLongPair (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (s η : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hη : 0 < η) (hητ : η ≤ periodicRieszTau) :
    Integrable (periodicRieszLongPair (ι := ι) s η)
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) := by
  have hΨ := periodicRieszShortFun_integrable (ι := ι) s 1 hs hs2 one_pos
  have hg := (hΨ.add (integrable_const (periodicRieszLongBound (ι := ι) s 0 +
    periodicRieszMeanConst ι s)))
  refine integrable_of_haar_majorant ρ M hρ _ hg
    (measurable_periodicRieszLongPair s η hs hs2 hη).aestronglyMeasurable ?_
  intro p
  have h := periodicRieszLongPair_bound s η hs hs2 hη hητ p
  refine h.trans (le_of_eq ?_)
  simp only [Pi.add_apply]
  unfold periodicRieszMajorantFun
  ring

/-! ### Centered splits -/

lemma ae_periodicCenteredTransport_split (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (n : ℕ) (hn : 1 ≤ n) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hητ : η ≤ periodicRieszTau)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszTransportKernel n s v) =ᵐ[
      (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortTransport n s η v) +
        hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszLongTransport n s η v) := by
  have hS := integrable_periodicRieszShortTransport ρ M hρ n s η hs hs2 hη hv
  have hL := integrable_periodicRieszLongTransport ρ M hρ n hn s η hs hs2 hη hητ hv
  have he : periodicRieszTransportKernel n s v =ᵐ[
      (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      periodicRieszShortTransport n s η v + periodicRieszLongTransport n s η v :=
    Filter.Eventually.of_forall (fun p => periodicRieszTransportKernel_split n hn s η hs hs2 hη hητ v p)
  exact (ae_hoeffdingCentered_congr _ _ _ he).trans (sourceRieszLocal_centered_add _ _ _ hS hL)

lemma ae_periodicCenteredEnergy_split (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (s η : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hη : 0 < η) (hητ : η ≤ periodicRieszTau)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ) =ᵐ[
      (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortPair s η) +
        hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszLongPair s η) := by
  have hS := integrable_periodicRieszShortPair ρ M hρ s η hs hs2 hη
  have hL := integrable_periodicRieszLongPair ρ M hρ s η hs hs2 hη hητ
  have he : (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)) =ᵐ[
      (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      periodicRieszShortPair s η + periodicRieszLongPair s η := by
    refine (periodicRieszKernel_pair_ae s hs hs2 ρ M hρ).trans (Filter.Eventually.of_forall fun p => ?_)
    exact periodicRieszPair_split s η hs hη hητ p
  exact (ae_hoeffdingCentered_congr _ _ _ he).trans (sourceRieszLocal_centered_add _ _ _ hS hL)

lemma ae_periodicRieszCenteredCutoff_linear (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (n : ℕ) (hn : 1 ≤ n) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s η n γ σ K v =ᵐ[
      (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      (fun p => -4 * σ * periodicRieszCoefficient ι s n K γ *
          hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszLongTransport n s η v) p +
        2 * γ * hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (periodicRieszLongPair s (2 * η)) p) := by
  have hL := integrable_periodicRieszLongTransport ρ M hρ n hn s η hs hs2 hη (by linarith) hv
  have hG := integrable_periodicRieszLongPair ρ M hρ s (2 * η) hs hs2 (by positivity) hη2
  have h := sourceRieszLocal_centered_add (periodicCappedDensityMeasure ρ)
    (fun p => -4 * σ * periodicRieszCoefficient ι s n K γ * periodicRieszLongTransport n s η v p)
    (fun p => 2 * γ * periodicRieszLongPair s (2 * η) p) (hL.const_mul _) (hG.const_mul _)
  filter_upwards [h] with p hp
  change hoeffdingCentered (periodicCappedDensityMeasure ρ)
    (fun p => -4 * σ * periodicRieszCoefficient ι s n K γ * periodicRieszLongTransport n s η v p +
      2 * γ * periodicRieszLongPair s (2 * η) p) p = _ at hp ⊢
  rw [hp]
  simp only [Pi.add_apply, sourceRieszLocal_centered_const_mul]

lemma ae_periodicRieszCutoff_statistic (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (n : ℕ) (hn : 1 ≤ n) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      (1 / 2 : ℝ) * iidNegativeStatistic N
          (periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s η n γ σ K v) ω =
        -2 * σ * periodicRieszCoefficient ι s n K γ * iidNegativeStatistic N
            (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszLongTransport n s η v)) ω +
          γ * iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
            (periodicRieszLongPair s (2 * η))) ω := by
  have h := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) N _ _
    (ae_periodicRieszCenteredCutoff_linear ρ M hρ n hn s η hs hs2 hη hη2 γ σ hv)
  filter_upwards [h] with ω hω
  rw [hω]
  change (1 / 2 : ℝ) * iidNegativeStatistic N
    ((-4 * σ * periodicRieszCoefficient ι s n K γ) •
        hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszLongTransport n s η v) +
      (2 * γ) • hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (periodicRieszLongPair s (2 * η))) ω = _
  rw [physical_iidNegativeStatistic_add, physical_iidNegativeStatistic_const_smul,
    physical_iidNegativeStatistic_const_smul]
  ring


/-! ### The pointwise smooth representative on the torus -/

/-- The smooth pointwise representative of the periodic Riesz kernel as a function on the torus. -/
def periodicRieszPairFun (s : ℝ) (z : PeriodicTorus ι) : ℝ :=
  if z = 0 then 0 else periodicRieszSmooth s (periodicCenteredLift z)

lemma periodicRieszPair_eq_fun (s : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszPair s p = periodicRieszPairFun s (p.1 - p.2) := by
  unfold periodicRieszPair periodicRieszPairFun
  simp only [sub_eq_zero]

lemma periodicRieszPairFun_ae (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    periodicRieszPairFun s =ᵐ[periodicHaar ι] periodicRieszKernel s hs2 := by
  have h := periodicRieszSmoothLift_ae (ι := ι) s periodicRieszTau hs hs2 periodicRieszTau_pos
  haveI := periodicHaar_nullSingletonClass (ι := ι)
  filter_upwards [h, (periodicHaar ι).ae_ne 0] with x hx hx0
  unfold periodicRieszPairFun
  rw [ite_eq_right hx0]
  exact hx

lemma measurable_periodicRieszPairFun (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    Measurable (periodicRieszPairFun (ι := ι) s) := by
  have h := (measurable_periodicRieszPair (ι := ι) s hs hs2).comp
    (measurable_id.prodMk measurable_const : Measurable fun x : PeriodicTorus ι => (x, (0 : PeriodicTorus ι)))
  have he : periodicRieszPairFun (ι := ι) s = (periodicRieszPair s ∘
      fun x : PeriodicTorus ι => (x, (0 : PeriodicTorus ι))) := by
    funext x
    simp [periodicRieszPair_eq_fun]
  rw [he]
  exact h

lemma integrable_periodicRieszPairFun (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    Integrable (periodicRieszPairFun (ι := ι) s) (periodicHaar ι) :=
  (periodicRieszKernel_integrable s hs2).congr (periodicRieszPairFun_ae s hs hs2).symm

lemma integral_abs_periodicRieszPairFun (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ∫ z, |periodicRieszPairFun (ι := ι) s z| ∂periodicHaar ι =
      ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι := by
  refine integral_congr_ae ?_
  filter_upwards [periodicRieszPairFun_ae s hs hs2] with x hx
  rw [hx]

lemma ae_periodicCenteredPair_split (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hητ : η ≤ periodicRieszTau)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszPair s) =ᵐ[
      (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortPair s η) +
        hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszLongPair s η) := by
  have hS := integrable_periodicRieszShortPair ρ M hρ s η hs hs2 hη
  have hL := integrable_periodicRieszLongPair ρ M hρ s η hs hs2 hη hητ
  have he : periodicRieszPair s =ᵐ[
      (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      periodicRieszShortPair s η + periodicRieszLongPair s η :=
    Filter.Eventually.of_forall (fun p => periodicRieszPair_split s η hs hη hητ p)
  exact (ae_hoeffdingCentered_congr _ _ _ he).trans (sourceRieszLocal_centered_add _ _ _ hS hL)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_normalized_pair_le
#print axioms DGRHS.Periodic.periodicRieszKernel_pair_ae
#print axioms DGRHS.Periodic.integrable_periodicRieszLongPair
#print axioms DGRHS.Periodic.ae_periodicCenteredTransport_split
#print axioms DGRHS.Periodic.ae_periodicCenteredEnergy_split
#print axioms DGRHS.Periodic.ae_periodicRieszCutoff_statistic
