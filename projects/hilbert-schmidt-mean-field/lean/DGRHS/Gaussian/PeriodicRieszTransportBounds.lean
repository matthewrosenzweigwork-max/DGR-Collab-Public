import DGRHS.Gaussian.PeriodicRieszTransportKernel
import DGRHS.Gaussian.PeriodicRieszShortSum
import DGRHS.Commutator.SourceRieszTruncatedTransportKernelBound

/-!
Packet P9h, unit 2 (part 12): pointwise bounds of the lattice sums of transported profile
derivatives.  The Euclidean all-order bound `sourceRieszGaussian_scale_integral_transport_bound` holds
for a globally Lipschitz field; for the torus the field is only controlled by the minimal image
(`‖w‖ ≤ K ‖z + m‖` for every lattice vector `m`), which is applied termwise through the linear field
`u ↦ ⟨a,u⟩/‖a‖² · w` (it has Lipschitz constant `‖w‖/‖a‖ ≤ K` and sends `a ↦ w`, `0 ↦ 0`).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The rank-one linear field `u ↦ ⟨a,u⟩/‖a‖² · w`. -/
def periodicRankOneField (a w : E) : E →L[ℝ] E :=
  ((‖a‖ ^ 2)⁻¹ : ℝ) • (innerSL ℝ a).smulRight w

lemma periodicRankOneField_apply (a w u : E) :
    periodicRankOneField a w u = ((‖a‖ ^ 2)⁻¹ * inner ℝ a u) • w := by
  simp [periodicRankOneField, smul_smul]

lemma periodicRankOneField_self {a : E} (ha : a ≠ 0) (w : E) : periodicRankOneField a w a = w := by
  rw [periodicRankOneField_apply, real_inner_self_eq_norm_sq]
  have : (‖a‖ ^ 2)⁻¹ * ‖a‖ ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  rw [this, one_smul]

lemma periodicRankOneField_lipschitz {a w : E} (ha : a ≠ 0) {K : ℝ≥0} (hw : ‖w‖ ≤ K * ‖a‖) :
    LipschitzWith K (periodicRankOneField a w) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, periodicRankOneField_apply, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖a‖ ^ 2)⁻¹)]
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have h1 : |inner ℝ a (x - y)| ≤ ‖a‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
  calc (‖a‖ ^ 2)⁻¹ * |inner ℝ a (x - y)| * ‖w‖ ≤ (‖a‖ ^ 2)⁻¹ * (‖a‖ * ‖x - y‖) * ‖w‖ := by gcongr
    _ = (‖w‖ / ‖a‖) * ‖x - y‖ := by field_simp
    _ ≤ K * ‖x - y‖ := by
        gcongr
        rw [div_le_iff₀ hapos]; linarith

/-- Transport bound of a single profile derivative at a point `a ≠ 0` and a vector `w` with
`‖w‖ ≤ K ‖a‖`. -/
lemma periodicProfile_transport_bound (n : ℕ) (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (S : Set ℝ) (hSm : MeasurableSet S) (hS : S ⊆ Ioc 0 η) (K : ℝ≥0) {a w : E} (ha : a ≠ 0)
    (hw : ‖w‖ ≤ K * ‖a‖) :
    |iteratedFDeriv ℝ n (periodicProfile c s S) a (fun _ => w)| ≤
      c * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
        ((2 : ℝ) ^ s * periodicProfile 1 s (Ioc 0 (2 * η)) a) := by
  have hS0 : S ⊆ Ioi 0 := fun t ht => (hS ht).1
  have hlip := periodicRankOneField_lipschitz ha hw
  have h := sourceRieszGaussian_scale_integral_transport_bound n c s S hc hs hSm hS0 hlip
    (x := a) (y := 0) ha
  simp only [sub_zero, map_zero, periodicRankOneField_self ha] at h
  have hI : (∫ t in S, t ^ (-s - 1) * Real.exp (-‖a‖ ^ 2 / (8 * t ^ 2))) ≤
      ∫ t in Ioc 0 η, t ^ (-s - 1) * Real.exp (-‖a‖ ^ 2 / (8 * t ^ 2)) := by
    have hint : IntegrableOn (fun t : ℝ => t ^ (-s - 1) * Real.exp (-‖a‖ ^ 2 / (8 * t ^ 2))) (Ioc 0 η) := by
      have hh := (DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale s (‖a‖ ^ 2 / 8) hs
        (by have := norm_pos_iff.mpr ha; positivity)).mono_set (fun t (ht : t ∈ Ioc (0 : ℝ) η) => (ht.1 : t ∈ Ioi (0 : ℝ)))
      refine hh.congr_fun (fun t ht => ?_) measurableSet_Ioc
      congr 2; ring
    exact setIntegral_mono_set hint (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
        exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le)
      (Filter.Eventually.of_forall hS)
  rw [sourceRieszShortScale_widen s η ‖a‖ hη] at hI
  have hCK : 0 ≤ c * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n :=
    mul_nonneg (mul_nonneg hc (sourceRieszGaussianDerivativeConstant_pos n).le) (by positivity)
  have hp : periodicProfile 1 s (Ioc 0 (2 * η)) a =
      ∫ t in Ioc 0 (2 * η), t ^ (-s - 1) * Real.exp (-‖a‖ ^ 2 / (2 * t ^ 2)) := by
    unfold periodicProfile sourceRieszGaussianScale; rw [one_mul]
  rw [hp]
  exact h.trans (mul_le_mul_of_nonneg_left hI hCK)


lemma norm_apply_const_le {n : ℕ} (D : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) (w : E) :
    |D (fun _ => w)| ≤ ‖D‖ * ‖w‖ ^ n := by
  have h := D.le_opNorm (fun _ => w)
  simpa [Real.norm_eq_abs, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

/-- Bound of the lattice sum of transported profile derivatives, in terms of the widened profile sum. -/
lemma periodicProfileSum_transport_bound (n : ℕ) (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (S : Set ℝ) (hSm : MeasurableSet S) (hS : S ⊆ Ioc 0 η) (K : ℝ≥0) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) {w : E}
    (hw : ∀ m : PeriodicFrequency ι, ‖w‖ ≤ K * ‖z + periodicFrequencyVector m‖) :
    |(∑' m : PeriodicFrequency ι,
        iteratedFDeriv ℝ n (periodicProfile c s S) (z + periodicFrequencyVector m)) (fun _ => w)| ≤
      c * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
        ((2 : ℝ) ^ s * periodicProfileSum 1 s (Ioc 0 (2 * η)) z) := by
  obtain ⟨r, hr, -, hk⟩ := periodicProfile_translate_local_bounds c s η hc hs hη S hSm hS z hz
  obtain ⟨u, hu, hub⟩ := hk n
  have hsumD : Summable (fun m : PeriodicFrequency ι =>
      iteratedFDeriv ℝ n (periodicProfile c s S) (z + periodicFrequencyVector m)) :=
    Summable.of_norm_bounded hu (fun m => hub m z (mem_ball_self hr))
  rw [ContinuousMultilinearMap.tsum_eval hsumD]
  have hb : ∀ m : PeriodicFrequency ι,
      |iteratedFDeriv ℝ n (periodicProfile c s S) (z + periodicFrequencyVector m) (fun _ => w)| ≤
        c * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
          ((2 : ℝ) ^ s * periodicProfile 1 s (Ioc 0 (2 * η)) (z + periodicFrequencyVector m)) :=
    fun m => periodicProfile_transport_bound n c s η hc hs hη S hSm hS K (hz m) (hw m)
  have hsum2 : Summable (fun m : PeriodicFrequency ι =>
      periodicProfile 1 s (Ioc 0 (2 * η)) (z + periodicFrequencyVector m)) :=
    summable_periodicProfile_translate 1 s (2 * η) zero_le_one hs (by positivity) (Ioc 0 (2 * η))
      measurableSet_Ioc (subset_refl _) hz
  have hsum3 := (hsum2.mul_left ((2 : ℝ) ^ s)).mul_left
    (c * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n)
  have hsn : Summable (fun m : PeriodicFrequency ι =>
      |iteratedFDeriv ℝ n (periodicProfile c s S) (z + periodicFrequencyVector m) (fun _ => w)|) :=
    hsum3.of_nonneg_of_le (fun m => abs_nonneg _) hb
  calc |∑' m, iteratedFDeriv ℝ n (periodicProfile c s S) (z + periodicFrequencyVector m) (fun _ => w)|
      ≤ ∑' m, |iteratedFDeriv ℝ n (periodicProfile c s S) (z + periodicFrequencyVector m) (fun _ => w)| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun m : PeriodicFrequency ι =>
          iteratedFDeriv ℝ n (periodicProfile c s S) (z + periodicFrequencyVector m) (fun _ => w))
          (by simpa only [Real.norm_eq_abs] using hsn)
    _ ≤ ∑' m : PeriodicFrequency ι, c * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
          ((2 : ℝ) ^ s * periodicProfile 1 s (Ioc 0 (2 * η)) (z + periodicFrequencyVector m)) :=
        hsn.tsum_le_tsum hb hsum3
    _ = _ := by
        unfold periodicProfileSum
        rw [tsum_mul_left, tsum_mul_left]


/-- The positive majorant `Ψ = F K₀ Σ_m ∫_{0<t≤1} t^{-s-1} e^{-|z+m|²/(2t²)} dt` of the transport kernels. -/
def periodicRieszMajorant (s : ℝ) (z : E) : ℝ :=
  periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc 0 1) z

lemma periodicRieszMajorant_nonneg (s : ℝ) (hs : 0 < s) (z : E) : 0 ≤ periodicRieszMajorant s z := by
  unfold periodicRieszMajorant periodicProfileSum
  exact tsum_nonneg fun m => periodicProfile_nonneg _ s _ (periodicRieszSmoothCoeff_pos s hs).le
    measurableSet_Ioc (fun t ht => ht.1) _

/-- Bound for all derivatives of the smooth long kernel. -/
def periodicRieszLongBound (s : ℝ) (n : ℕ) : ℝ :=
  ∑' k : PeriodicFrequency ι, periodicRieszLCCoeff s (periodicHeatCut periodicRieszTau) k *
    (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ n

lemma periodicRieszLongBound_nonneg (s : ℝ) (hs : 0 < s) (n : ℕ) : 0 ≤ periodicRieszLongBound (ι := ι) s n :=
  tsum_nonneg fun k => mul_nonneg (periodicRieszLCCoeff_nonneg s _ hs
    (periodicHeatCut_pos periodicRieszTau_pos).le k) (by positivity)

lemma norm_periodicCenteredLift_le (x : PeriodicTorus ι) : ‖periodicCenteredLift x‖ ≤ Fintype.card ι := by
  have h : ‖periodicCenteredLift x‖ ^ 2 ≤ (Fintype.card ι : ℝ) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    calc ∑ i, ‖periodicCenteredLift x i‖ ^ 2 ≤ ∑ _i : ι, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]
          have := periodicCenteredLift_abs_le x i
          nlinarith [abs_nonneg (periodicCenteredLift x i), sq_abs (periodicCenteredLift x i)]
      _ = _ := by simp
  have hd : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  nlinarith [norm_nonneg (periodicCenteredLift x)]

lemma periodicRieszTau_double : 2 * periodicRieszTau = 1 := by unfold periodicRieszTau; norm_num

lemma periodicRieszSmooth_iteratedFDeriv (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (n : ℕ) (hn : 1 ≤ n) {z : E} (hz : z ∈ (periodicOffLattice : Set E)) :
    iteratedFDeriv ℝ n (periodicRieszSmooth s) z =
      ∑' m : PeriodicFrequency ι, iteratedFDeriv ℝ n
          (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc 0 periodicRieszTau))
          (z + periodicFrequencyVector m) +
        iteratedFDeriv ℝ n (periodicRieszLongKernel (ι := ι) s (periodicHeatCut periodicRieszTau)) z :=
  periodicRieszSmoothLift_iteratedFDeriv s periodicRieszTau hs hs2 periodicRieszTau_pos n hn hz

/-- Pointwise bound of the torus Riesz transport kernel by the positive majorant. -/
theorem periodicRieszTransportKernel_bound (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    |periodicRieszTransportKernel n s v p| ≤ (K : ℝ) ^ n *
      (sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s *
          periodicRieszMajorant s (periodicCenteredLift (p.1 - p.2)) +
        periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n) := by
  have hc0 := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have hCn := (sourceRieszGaussianDerivativeConstant_pos n).le
  by_cases hp : p.1 = p.2
  · simp only [periodicRieszTransportKernel, ite_eq_left hp, abs_zero]
    have h1 := periodicRieszMajorant_nonneg s hs (periodicCenteredLift (p.1 - p.2))
    have h2 := periodicRieszLongBound_nonneg (ι := ι) s hs n
    positivity
  simp only [periodicRieszTransportKernel, ite_eq_right hp]
  have hsub : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hz := periodicCenteredLift_mem_offLattice (ι := ι) hsub
  set z := periodicCenteredLift (p.1 - p.2) with hzdef
  set w := v p.1 - v p.2 with hwdef
  have hw : ∀ m : PeriodicFrequency ι, ‖w‖ ≤ K * ‖z + periodicFrequencyVector m‖ :=
    fun m => norm_sub_le_of_lipschitz hv p.1 p.2 m
  rw [periodicRieszSmooth_iteratedFDeriv s hs hs2 n hn hz, add_apply]
  have h1 := periodicProfileSum_transport_bound n (periodicRieszSmoothCoeff ι s) s periodicRieszTau hc0 hs
    periodicRieszTau_pos (Ioc 0 periodicRieszTau) measurableSet_Ioc (subset_refl _) K hz hw
  rw [periodicRieszTau_double] at h1
  have h2 : |iteratedFDeriv ℝ n (periodicRieszLongKernel (ι := ι) s (periodicHeatCut periodicRieszTau)) z
      (fun _ => w)| ≤ periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n * (K : ℝ) ^ n := by
    refine (norm_apply_const_le _ w).trans ?_
    have hL := norm_iteratedFDeriv_periodicRieszLongKernel_le (ι := ι) s (periodicHeatCut periodicRieszTau)
      hs hs2 (periodicHeatCut_pos periodicRieszTau_pos) n z
    have hw0 : ‖w‖ ≤ K * Fintype.card ι := by
      have := hw 0
      simp only [periodicFrequencyVector_zero, add_zero] at this
      exact this.trans (mul_le_mul_of_nonneg_left (norm_periodicCenteredLift_le _) K.coe_nonneg)
    have hL' : ‖iteratedFDeriv ℝ n (periodicRieszLongKernel (ι := ι) s (periodicHeatCut periodicRieszTau)) z‖ ≤
        periodicRieszLongBound (ι := ι) s n := hL
    calc ‖iteratedFDeriv ℝ n (periodicRieszLongKernel (ι := ι) s (periodicHeatCut periodicRieszTau)) z‖ * ‖w‖ ^ n
        ≤ periodicRieszLongBound (ι := ι) s n * ((K : ℝ) * Fintype.card ι) ^ n :=
          mul_le_mul hL' (pow_le_pow_left₀ (norm_nonneg w) hw0 n) (by positivity)
            (periodicRieszLongBound_nonneg s hs n)
      _ = _ := by rw [mul_pow]; ring
  have h3 : periodicRieszMajorant s z =
      periodicRieszSmoothCoeff ι s * periodicProfileSum 1 s (Ioc 0 1) z := by
    unfold periodicRieszMajorant
    rw [periodicProfileSum_const_mul, mul_one]
  have h4 : sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s * periodicRieszMajorant s z =
      periodicRieszSmoothCoeff ι s * sourceRieszGaussianDerivativeConstant n *
        ((2 : ℝ) ^ s * periodicProfileSum 1 s (Ioc 0 1) z) := by
    rw [h3]; ring
  refine (abs_add_le _ _).trans ?_
  calc _ ≤ periodicRieszSmoothCoeff ι s * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
        ((2 : ℝ) ^ s * periodicProfileSum 1 s (Ioc 0 1) z) +
      periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n * (K : ℝ) ^ n := add_le_add h1 h2
    _ = (K : ℝ) ^ n * (sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s * periodicRieszMajorant s z +
        periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n) := by
        rw [h4]; ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszTransportKernel_bound
