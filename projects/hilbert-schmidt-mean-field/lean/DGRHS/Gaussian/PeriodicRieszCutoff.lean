import DGRHS.Gaussian.PeriodicRieszNorms
import DGRHS.Commutator.SourceRieszLocalAdaptiveSize

/-!
Packet P9h, unit 2 (part 20): the cutoff kernel family of the local numerator estimate on the torus
(TeX 3380-3440): coefficient `ε_γ = γ/(4 C K^n)`, raw kernel
`r_η = -4σ ε κ^{long}_η + 2γ g_{2η}`, its centering `q_η`, pointwise majorant bound
`|r_η| ≤ γ C_r (Ψ + 1)` (uniform in `η`), diagonal cap `|r_η| ≤ γ C_cap η^{-s}`, symmetry, measurability.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The profile constant `C ≥ max(A_n, B_n)` with `|κ^{long}| ≤ K^n C (Ψ + 1)`. -/
def periodicRieszProfileC (ι : Type u) [Fintype ι] [Nonempty ι] (s : ℝ) (n : ℕ) : ℝ :=
  1 + max (sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s)
    (periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n)

lemma periodicRieszProfileC_ge (s : ℝ) (hs : 0 < s) (n : ℕ) :
    sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s ≤ periodicRieszProfileC ι s n ∧
    periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n ≤ periodicRieszProfileC ι s n ∧
    1 ≤ periodicRieszProfileC ι s n := by
  have hB := periodicRieszLongBound_nonneg (ι := ι) s hs n
  have hCn := (sourceRieszGaussianDerivativeConstant_pos n).le
  unfold periodicRieszProfileC
  have h1 := le_max_left (sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s)
    (periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n)
  have h2 := le_max_right (sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s)
    (periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n)
  have h3 : 0 ≤ max (sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s)
    (periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n) := le_trans (by positivity) h1
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The transport coefficient `ε = γ/(4 C K^n)`. -/
def periodicRieszCoefficient (ι : Type u) [Fintype ι] [Nonempty ι] (s : ℝ) (n : ℕ) (K γ : ℝ) : ℝ :=
  γ / (4 * periodicRieszProfileC ι s n * K ^ n)

lemma periodicRieszCoefficient_nonneg (s : ℝ) (hs : 0 < s) (n : ℕ) {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 ≤ γ) :
    0 ≤ periodicRieszCoefficient ι s n K γ := by
  have := (periodicRieszProfileC_ge (ι := ι) s hs n).2.2
  unfold periodicRieszCoefficient
  positivity

lemma periodicRieszCoefficient_mul_le (s : ℝ) (hs : 0 < s) (n : ℕ) {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 ≤ γ) :
    4 * periodicRieszCoefficient ι s n K γ * (periodicRieszProfileC ι s n * K ^ n) ≤ γ := by
  have hC := (periodicRieszProfileC_ge (ι := ι) s hs n).2.2
  by_cases h : K ^ n = 0
  · simp [periodicRieszCoefficient, h, hγ]
  · unfold periodicRieszCoefficient
    have : 4 * (γ / (4 * periodicRieszProfileC ι s n * K ^ n)) * (periodicRieszProfileC ι s n * K ^ n) = γ := by
      field_simp
    exact this.le

/-- The raw cutoff kernel at scale `η`. -/
def periodicRieszRawCutoff (s η : ℝ) (n : ℕ) (γ σ : ℝ) (K : ℝ≥0) (v : PeriodicTorus ι → E)
    (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ :=
  -4 * σ * periodicRieszCoefficient ι s n K γ * periodicRieszLongTransport n s η v p +
    2 * γ * periodicRieszLongPair s (2 * η) p

/-- The `μ`-centered cutoff kernel. -/
def periodicRieszCenteredCutoff (μ : Measure (PeriodicTorus ι)) (s η : ℝ) (n : ℕ) (γ σ : ℝ) (K : ℝ≥0)
    (v : PeriodicTorus ι → E) : PeriodicTorus ι × PeriodicTorus ι → ℝ :=
  hoeffdingCentered μ (periodicRieszRawCutoff s η n γ σ K v)

lemma periodicProfileSum_mono (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) {S S' : Set ℝ}
    (hSm : MeasurableSet S) (hS'm : MeasurableSet S') (hS : S ⊆ Ioc 0 η) (hS' : S' ⊆ Ioc 0 η)
    (hSS : S ⊆ S') {z : E} (hz : z ∈ (periodicOffLattice : Set E)) :
    periodicProfileSum c s S z ≤ periodicProfileSum c s S' z := by
  unfold periodicProfileSum
  refine Summable.tsum_le_tsum (fun m => ?_) (summable_periodicProfile_translate c s η hc hs hη S hSm hS hz)
    (summable_periodicProfile_translate c s η hc hs hη S' hS'm hS' hz)
  unfold periodicProfile
  refine mul_le_mul_of_nonneg_left ?_ hc
  have hy := hz m
  have hi : IntegrableOn (fun t : ℝ => t ^ (-s - 1) * sourceRieszGaussianScale t (z + periodicFrequencyVector m))
      (Ioi 0) := DGRHS.Gaussian.integrableOn_gaussianRieszEuclidean_full_scale s hs _ hy
  exact setIntegral_mono_set (hi.mono_set (fun t ht => (hS' ht).1))
    (by
      filter_upwards [self_mem_ae_restrict hS'm] with t ht
      exact mul_nonneg (Real.rpow_nonneg (hS' ht).1.le _) (by unfold sourceRieszGaussianScale; positivity))
    (Filter.Eventually.of_forall hSS)


/-- The constant `F ε^{(d-s)/2}/((d-s)/2)` subtracted in the smooth lift (at the fixed scale). -/
def periodicRieszMeanConst (ι : Type u) [Fintype ι] [Nonempty ι] (s : ℝ) : ℝ :=
  periodicRieszMellinFactor ι s * (periodicHeatCut periodicRieszTau) ^ (((Fintype.card ι : ℝ) - s) / 2) /
    (((Fintype.card ι : ℝ) - s) / 2)

lemma periodicRieszMeanConst_nonneg (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    0 ≤ periodicRieszMeanConst ι s := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hF := periodicRieszMellinFactor_pos (ι := ι) s hs
  have := periodicHeatCut_pos periodicRieszTau_pos
  have : 0 < ((Fintype.card ι : ℝ) - s) / 2 := by linarith
  unfold periodicRieszMeanConst
  positivity

/-- The raw constant `C_r = 3 + 2 B₀ + 2 c₀`. -/
def periodicRieszRawConst (ι : Type u) [Fintype ι] [Nonempty ι] (s : ℝ) : ℝ :=
  3 + 2 * periodicRieszLongBound (ι := ι) s 0 + 2 * periodicRieszMeanConst ι s

/-- The diagonal-cap constant. -/
def periodicRieszCapConst (ι : Type u) [Fintype ι] [Nonempty ι] (s : ℝ) : ℝ :=
  3 * periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι / s + 1 +
    2 * periodicRieszLongBound (ι := ι) s 0 + 2 * periodicRieszMeanConst ι s

lemma periodicRieszLongPair_bound (s η : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hη : 0 < η) (hητ : η ≤ periodicRieszTau) (p : PeriodicTorus ι × PeriodicTorus ι) :
    |periodicRieszLongPair s η p| ≤ periodicRieszMajorantFun s (p.1 - p.2) +
      periodicRieszLongBound (ι := ι) s 0 + periodicRieszMeanConst ι s := by
  have hc0 := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have hB0 := periodicRieszLongBound_nonneg (ι := ι) s hs 0
  have hm0 := periodicRieszMeanConst_nonneg (ι := ι) s hs hs2
  have hΨ0 : 0 ≤ periodicRieszMajorantFun s (p.1 - p.2) := periodicRieszShortFun_nonneg s 1 hs _
  by_cases hp : p.1 = p.2
  · simp only [periodicRieszLongPair, ite_eq_left hp, abs_zero]
    linarith
  simp only [periodicRieszLongPair, ite_eq_right hp]
  have hsub : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hz := periodicCenteredLift_mem_offLattice (ι := ι) hsub
  set z := periodicCenteredLift (p.1 - p.2) with hzdef
  have hband0 : 0 ≤ periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau) z := by
    unfold periodicProfileSum
    exact tsum_nonneg fun m => periodicProfile_nonneg _ s _ hc0 measurableSet_Ioc
      (fun t ht => lt_of_lt_of_le hη ht.1.le) _
  have hband : periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau) z ≤
      periodicRieszMajorantFun s (p.1 - p.2) := by
    have hMaj : periodicRieszMajorantFun s (p.1 - p.2) = periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc 0 1) z := by
      unfold periodicRieszMajorantFun periodicRieszShortFun periodicRieszShortSum
      rw [ite_eq_right hsub]
    rw [hMaj]
    refine periodicProfileSum_mono _ s 1 hc0 hs one_pos measurableSet_Ioc measurableSet_Ioc
      (fun t ht => ⟨lt_of_lt_of_le hη ht.1.le, ht.2.trans (by norm_num [periodicRieszTau])⟩) (subset_refl _)
      (fun t ht => ⟨lt_of_lt_of_le hη ht.1.le, ht.2.trans (by norm_num [periodicRieszTau])⟩) hz
  have hL : |periodicRieszLongKernel s (periodicHeatCut periodicRieszTau) z| ≤
      periodicRieszLongBound (ι := ι) s 0 := by
    have := norm_iteratedFDeriv_periodicRieszLongKernel_le (ι := ι) s (periodicHeatCut periodicRieszTau)
      hs hs2 (periodicHeatCut_pos periodicRieszTau_pos) 0 z
    simpa [norm_iteratedFDeriv_zero, periodicRieszLongBound] using this
  have hconst : periodicRieszMellinFactor ι s * (periodicHeatCut periodicRieszTau) ^ (((Fintype.card ι : ℝ) - s) / 2) /
      (((Fintype.card ι : ℝ) - s) / 2) = periodicRieszMeanConst ι s := rfl
  rw [hconst]
  calc _ ≤ |periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau) z +
        periodicRieszLongKernel s (periodicHeatCut periodicRieszTau) z| + |periodicRieszMeanConst ι s| := abs_sub _ _
    _ ≤ (periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau) z +
        |periodicRieszLongKernel s (periodicHeatCut periodicRieszTau) z|) + periodicRieszMeanConst ι s := by
        rw [abs_of_nonneg hm0]
        gcongr
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg hband0]
    _ ≤ _ := by linarith

/-- Pointwise majorant bound of the raw cutoff kernel (uniform in `η`). -/
lemma periodicRieszRawCutoff_bound (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ)
    (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    |periodicRieszRawCutoff s η n γ σ K v p| ≤
      γ * periodicRieszRawConst ι s * (periodicRieszMajorantFun s (p.1 - p.2) + 1) := by
  have hητ : η ≤ periodicRieszTau := by linarith
  have hC := periodicRieszProfileC_ge (ι := ι) s hs n
  have hB0 := periodicRieszLongBound_nonneg (ι := ι) s hs 0
  have hm0 := periodicRieszMeanConst_nonneg (ι := ι) s hs hs2
  have hΨ0 : 0 ≤ periodicRieszMajorantFun s (p.1 - p.2) := periodicRieszShortFun_nonneg s 1 hs _
  have hε0 := periodicRieszCoefficient_nonneg (ι := ι) s hs n (K := (K : ℝ)) (γ := γ) K.coe_nonneg hγ
  have hεK := periodicRieszCoefficient_mul_le (ι := ι) s hs n (K := (K : ℝ)) (γ := γ) K.coe_nonneg hγ
  have hκ := periodicRieszLongTransport_bound n s η hs hs2 hη hητ hv p
  have hΨeq : periodicRieszMajorant s (periodicCenteredLift (p.1 - p.2)) =
      periodicRieszMajorantFun s (p.1 - p.2) ∨ p.1 = p.2 := by
    by_cases hp : p.1 = p.2
    · exact Or.inr hp
    · left
      unfold periodicRieszMajorantFun periodicRieszShortFun periodicRieszShortSum periodicRieszMajorant
      rw [ite_eq_right (sub_ne_zero.mpr hp)]
  have hg := periodicRieszLongPair_bound s (2 * η) hs hs2 (by positivity) hη2 p
  have hΨ := periodicRieszMajorantFun s (p.1 - p.2)
  by_cases hp : p.1 = p.2
  · simp only [periodicRieszRawCutoff, periodicRieszLongTransport, periodicRieszLongPair, ite_eq_left hp,
      mul_zero, add_zero, abs_zero]
    have hr0 : 0 ≤ periodicRieszRawConst ι s := by unfold periodicRieszRawConst; positivity
    exact mul_nonneg (mul_nonneg hγ hr0) (by linarith)
  have hΨeq' : periodicRieszMajorant s (periodicCenteredLift (p.1 - p.2)) =
      periodicRieszMajorantFun s (p.1 - p.2) := hΨeq.resolve_right hp
  rw [hΨeq'] at hκ
  have hκ' : |periodicRieszLongTransport n s η v p| ≤ (K : ℝ) ^ n * (periodicRieszProfileC ι s n *
      (periodicRieszMajorantFun s (p.1 - p.2) + 1)) := by
    refine hκ.trans ?_
    have hA := hC.1
    have hB := hC.2.1
    have hKn : 0 ≤ (K : ℝ) ^ n := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hKn
    nlinarith [mul_le_mul_of_nonneg_right hA hΨ0]
  unfold periodicRieszRawCutoff
  have h1 : |-4 * σ * periodicRieszCoefficient ι s n K γ * periodicRieszLongTransport n s η v p| ≤
      γ * (periodicRieszMajorantFun s (p.1 - p.2) + 1) := by
    rw [abs_mul, show (-4 * σ * periodicRieszCoefficient ι s n K γ) = -(4 * σ * periodicRieszCoefficient ι s n K γ) by ring,
      abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg hε0]
    calc 4 * |σ| * periodicRieszCoefficient ι s n K γ * |periodicRieszLongTransport n s η v p|
        ≤ 4 * 1 * periodicRieszCoefficient ι s n K γ * ((K : ℝ) ^ n * (periodicRieszProfileC ι s n *
          (periodicRieszMajorantFun s (p.1 - p.2) + 1))) := by
          gcongr
      _ = (4 * periodicRieszCoefficient ι s n K γ * (periodicRieszProfileC ι s n * (K : ℝ) ^ n)) *
          (periodicRieszMajorantFun s (p.1 - p.2) + 1) := by ring
      _ ≤ γ * (periodicRieszMajorantFun s (p.1 - p.2) + 1) := by
          gcongr
  have h2 : |2 * γ * periodicRieszLongPair s (2 * η) p| ≤
      2 * γ * (periodicRieszMajorantFun s (p.1 - p.2) + periodicRieszLongBound (ι := ι) s 0 + periodicRieszMeanConst ι s) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * γ)]
    gcongr
  refine (abs_add_le _ _).trans ?_
  unfold periodicRieszRawConst
  nlinarith [h1, h2, mul_nonneg hγ hΨ0, mul_nonneg hγ hB0, mul_nonneg hγ hm0]


/-- Diagonal cap of the raw cutoff kernel. -/
lemma periodicRieszRawCutoff_cap (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ)
    (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    |periodicRieszRawCutoff s η n γ σ K v p| ≤ γ * periodicRieszCapConst ι s * η ^ (-s) := by
  have hητ : η ≤ periodicRieszTau := by linarith
  have hC := periodicRieszProfileC_ge (ι := ι) s hs n
  have hcF := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have hΛ := periodicLatticeGaussConst_pos (ι := ι)
  have hB0 := periodicRieszLongBound_nonneg (ι := ι) s hs 0
  have hBn := periodicRieszLongBound_nonneg (ι := ι) s hs n
  have hm0 := periodicRieszMeanConst_nonneg (ι := ι) s hs hs2
  have hCn := (sourceRieszGaussianDerivativeConstant_pos n).le
  have hε0 := periodicRieszCoefficient_nonneg (ι := ι) s hs n (K := (K : ℝ)) (γ := γ) K.coe_nonneg hγ
  have hεK := periodicRieszCoefficient_mul_le (ι := ι) s hs n (K := (K : ℝ)) (γ := γ) K.coe_nonneg hγ
  have hηs : 1 ≤ η ^ (-s) := by
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη (by linarith [periodicRieszTau, show periodicRieszTau = 1/2 from rfl]) (by linarith)
  have hηs0 : 0 ≤ η ^ (-s) := le_trans zero_le_one hηs
  have h2ηs : (2 * η) ^ (-s) ≤ η ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hη (by linarith) (by linarith)
  have hκ := periodicRieszLongTransport_cap n s η hs hs2 hη hητ hv p
  have hg : |periodicRieszLongPair s (2 * η) p| ≤ periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι *
      ((2 * η) ^ (-s) / s) + periodicRieszLongBound (ι := ι) s 0 + periodicRieszMeanConst ι s :=
    periodicRieszLongPair_cap s (2 * η) hs hs2 (by positivity) hη2 p
  unfold periodicRieszRawCutoff
  have hcapA : periodicRieszSmoothCoeff ι s * sourceRieszGaussianDerivativeConstant n *
        periodicLatticeGaussConst ι * (η ^ (-s) / s) + periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n
      ≤ periodicRieszProfileC ι s n * (periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) + 1) := by
    have hCnle : sourceRieszGaussianDerivativeConstant n ≤ periodicRieszProfileC ι s n := by
      have h2s : (1 : ℝ) ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs.le
      calc sourceRieszGaussianDerivativeConstant n ≤ sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s :=
            le_mul_of_one_le_right hCn h2s
        _ ≤ _ := hC.1
    have hq : 0 ≤ periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hCnle hq, hC.2.1]
  have h1 : |-4 * σ * periodicRieszCoefficient ι s n K γ * periodicRieszLongTransport n s η v p| ≤
      γ * (periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) + 1) := by
    rw [abs_mul, show (-4 * σ * periodicRieszCoefficient ι s n K γ) = -(4 * σ * periodicRieszCoefficient ι s n K γ) by ring,
      abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg hε0]
    have hκ2 : |periodicRieszLongTransport n s η v p| ≤ (K : ℝ) ^ n * (periodicRieszProfileC ι s n *
        (periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) + 1)) :=
      hκ.trans (mul_le_mul_of_nonneg_left hcapA (by positivity))
    calc 4 * |σ| * periodicRieszCoefficient ι s n K γ * |periodicRieszLongTransport n s η v p|
        ≤ 4 * 1 * periodicRieszCoefficient ι s n K γ * ((K : ℝ) ^ n * (periodicRieszProfileC ι s n *
          (periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) + 1))) := by
          gcongr
      _ = (4 * periodicRieszCoefficient ι s n K γ * (periodicRieszProfileC ι s n * (K : ℝ) ^ n)) *
          (periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) + 1) := by ring
      _ ≤ γ * (periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) + 1) := by
          gcongr
  have h2 : |2 * γ * periodicRieszLongPair s (2 * η) p| ≤ 2 * γ * (periodicRieszSmoothCoeff ι s *
      periodicLatticeGaussConst ι * (η ^ (-s) / s) + periodicRieszLongBound (ι := ι) s 0 + periodicRieszMeanConst ι s) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * γ)]
    gcongr
    refine hg.trans ?_
    have : periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * ((2 * η) ^ (-s) / s) ≤
        periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) := by
      gcongr
    linarith
  refine (abs_add_le _ _).trans ?_
  unfold periodicRieszCapConst
  have hq0 : 0 ≤ periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) := by positivity
  have hrest : γ * (1 + 2 * periodicRieszLongBound (ι := ι) s 0 + 2 * periodicRieszMeanConst ι s) ≤
      γ * (1 + 2 * periodicRieszLongBound (ι := ι) s 0 + 2 * periodicRieszMeanConst ι s) * η ^ (-s) :=
    le_mul_of_one_le_right (by positivity) hηs
  have e : γ * (3 * periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι / s + 1 +
      2 * periodicRieszLongBound (ι := ι) s 0 + 2 * periodicRieszMeanConst ι s) * η ^ (-s) =
      γ * (3 * (periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s))) +
      γ * (1 + 2 * periodicRieszLongBound (ι := ι) s 0 + 2 * periodicRieszMeanConst ι s) * η ^ (-s) := by
    field_simp
    ring
  rw [e]
  nlinarith [h1, h2, hrest]

lemma periodicRieszRawCutoff_symm (n : ℕ) (hn : 1 ≤ n) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ) (K : ℝ≥0)
    (v : PeriodicTorus ι → E) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszRawCutoff s η n γ σ K v p.swap = periodicRieszRawCutoff s η n γ σ K v p := by
  unfold periodicRieszRawCutoff
  rw [periodicRieszLongTransport_symm n hn s η hs hs2 hη (by linarith), periodicRieszLongPair_symm]

lemma measurable_periodicRieszRawCutoff (n : ℕ) (hn : 1 ≤ n) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (γ σ : ℝ) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) :
    Measurable (periodicRieszRawCutoff (ι := ι) s η n γ σ K v) := by
  unfold periodicRieszRawCutoff
  exact (((measurable_periodicRieszLongTransport n s η hs hs2 hη hv).const_mul _)).add
    ((measurable_periodicRieszLongPair s (2 * η) hs hs2 (by positivity)).const_mul _)

end DGRHS.Periodic
