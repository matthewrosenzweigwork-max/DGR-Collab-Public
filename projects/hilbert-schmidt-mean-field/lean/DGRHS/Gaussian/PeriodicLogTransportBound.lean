import DGRHS.Gaussian.PeriodicLogTransportKernel
import DGRHS.Gaussian.PeriodicRieszTransportBounds
import DGRHS.Gaussian.PeriodicRieszDiagonalCap
import DGRHS.Commutator.SourceLogGaussianLongDerivative

/-!
Packet P9h, unit 3 (LOG, part 7): the torus LOG transport kernel is bounded by `C K^n`, with `C`
independent of the Lipschitz constant `K` and of the field `v` (the torus analogue of
`exists_sourceLogTransportKernel_bound`).

Proof: off the diagonal with `z` the centered lift of `x - y` and `w = v x - v y`, `‖w‖ ≤ K‖z+m‖` for
every lattice vector `m` (minimal image).  `D^n g(z)[w^n]` is the lattice sum of profile derivatives plus
the derivative of the smooth long kernel.  The `m = 0` profile term is bounded by the uniform Euclidean
LOG bound (physical LOG transport kernel and its Gaussian complement, through the rank-one field
`u ↦ <a,u>/|a|² w`); the terms `m ≠ 0` (`‖z+m‖ ≥ 1/2`) by the absorbed Gaussian bound and Gaussian
decay; the long kernel by its sup bound.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Uniform Euclidean bound of a derivative of the LOG short-range profile along a rank-one field. -/
lemma gaussianLogShortRange_transport_uniform (n : ℕ) (hn : 1 ≤ n) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (η : ℝ), 0 < η → ∀ {K : ℝ≥0} {a w : E}, a ≠ 0 → ‖w‖ ≤ K * ‖a‖ →
      |iteratedFDeriv ℝ n (gaussianLogShortRange η) a (fun _ => w)| ≤ C0 * (K : ℝ) ^ n := by
  obtain ⟨Cex, hCex, hex⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℝ≥0} {v : E → E}, LipschitzWith K v →
      ∀ p : E × E, |sourceLogTransportKernel n v p| ≤ C * (K : ℝ) ^ n :=
    exists_sourceLogTransportKernel_bound n hn
  obtain ⟨Cc, hCc, hcomp⟩ := exists_sourceLogGaussianComplementTransportKernel_uniform_bound (ι := ι) n hn
  refine ⟨Cex + Cc, by linarith, ?_⟩
  intro η hη K a w ha hw
  have hlip := periodicRankOneField_lipschitz ha hw
  have hva : (periodicRankOneField a w) a = w := periodicRankOneField_self ha w
  have hv0 : (periodicRankOneField a w) 0 = 0 := map_zero _
  have hshort : sourceLogGaussianShortTransportKernel n η (periodicRankOneField a w) (a, 0) =
      iteratedFDeriv ℝ n (gaussianLogShortRange η) a (fun _ => w) := by
    simp [sourceLogGaussianShortTransportKernel, ha, hva, hv0]
  have h1 := hex hlip (a, 0)
  have h2 := hcomp η hη K (periodicRankOneField a w) hlip (a, 0)
  rw [← hshort]
  have h3 : |sourceLogGaussianShortTransportKernel n η (periodicRankOneField a w) (a, 0)| ≤
      |sourceLogTransportKernel n (periodicRankOneField a w) (a, 0)| +
        |sourceLogTransportKernel n (periodicRankOneField a w) (a, 0) -
          sourceLogGaussianShortTransportKernel n η (periodicRankOneField a w) (a, 0)| := by
    have := abs_sub (sourceLogTransportKernel n (periodicRankOneField a w) (a, 0))
      (sourceLogTransportKernel n (periodicRankOneField a w) (a, 0) -
          sourceLogGaussianShortTransportKernel n η (periodicRankOneField a w) (a, 0))
    simpa only [sub_sub_cancel] using this
  linarith [h1, h2, h3]

lemma half_le_norm_add_lattice {z : E} (hz : ∀ i, |z i| ≤ 1 / 2) {m : PeriodicFrequency ι}
    (hm : m ≠ 0) : 1 / 2 ≤ ‖z + periodicFrequencyVector m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm (funext h)
  have h1 : (1 : ℝ) ≤ |(m i : ℝ)| := by
    have : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
    exact_mod_cast this
  have h2 : ‖z i + (m i : ℝ)‖ ≤ ‖z + periodicFrequencyVector m‖ := by
    have := PiLp.norm_apply_le (z + periodicFrequencyVector m) i
    simpa [periodicFrequencyVector_apply] using this
  have h3 : |(m i : ℝ)| ≤ |z i + (m i : ℝ)| + |z i| := by
    have := abs_sub (z i + (m i : ℝ)) (z i)
    simpa using this
  rw [Real.norm_eq_abs] at h2
  linarith [hz i]

/-- Gaussian decay of the unit-scale LOG profile away from the origin. -/
def periodicLogJ : ℝ := Real.exp (1 / 8) * ∫ t in Ioc 0 (1 : ℝ), t⁻¹ * Real.exp (-(1 / 8) / t ^ 2)

lemma periodicLogJ_nonneg : 0 ≤ periodicLogJ := by
  unfold periodicLogJ
  refine mul_nonneg (Real.exp_pos _).le (setIntegral_nonneg measurableSet_Ioc (fun t ht => ?_))
  exact mul_nonneg (inv_nonneg.mpr ht.1.le) (Real.exp_pos _).le

lemma gaussianLogShortRange_one_le (y : E) (hy : 1 / 2 ≤ ‖y‖) :
    gaussianLogShortRange 1 y ≤ periodicLogJ * Real.exp (-‖y‖ ^ 2 / 2) := by
  have hy0 : 0 < ‖y‖ := by linarith
  have hL := DGRHS.Gaussian.integrableOn_gaussianLog_profile_short 1 ‖y‖ one_pos hy0
  have hR0 : IntegrableOn (fun t : ℝ => t⁻¹ * Real.exp (-(1 / 8) / t ^ 2)) (Ioc 0 (1 : ℝ)) := by
    have h := integrableOn_Ioc_rpow_exp 0 (1 / 8) 1 le_rfl (by norm_num) one_pos
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioc
    simp only [neg_zero, zero_sub, Real.rpow_neg_one]
  have hR : IntegrableOn (fun t : ℝ => Real.exp (1 / 8) * Real.exp (-‖y‖ ^ 2 / 2) *
      (t⁻¹ * Real.exp (-(1 / 8) / t ^ 2))) (Ioc 0 (1 : ℝ)) := hR0.const_mul _
  unfold gaussianLogShortRange
  calc ∫ t in Ioc 0 (1 : ℝ), t⁻¹ * Real.exp (-‖y‖ ^ 2 / (2 * t ^ 2))
      ≤ ∫ t in Ioc 0 (1 : ℝ), Real.exp (1 / 8) * Real.exp (-‖y‖ ^ 2 / 2) *
          (t⁻¹ * Real.exp (-(1 / 8) / t ^ 2)) := by
        refine setIntegral_mono_on hL hR measurableSet_Ioc (fun t ht => ?_)
        have ht0 : 0 < t := ht.1
        have ht1 : t ≤ 1 := ht.2
        have hu : 1 ≤ 1 / t ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        have hy2 : 1 / 4 ≤ ‖y‖ ^ 2 := by nlinarith
        have hexp : Real.exp (-‖y‖ ^ 2 / (2 * t ^ 2)) ≤
            Real.exp (1 / 8) * Real.exp (-‖y‖ ^ 2 / 2) * Real.exp (-(1 / 8) / t ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have e1 : -‖y‖ ^ 2 / (2 * t ^ 2) = -(‖y‖ ^ 2 / 2) * (1 / t ^ 2) := by
            field_simp
          have e2 : -(1 / 8) / t ^ 2 = -(1 / 8) * (1 / t ^ 2) := by field_simp
          rw [e1, e2]
          nlinarith [mul_nonneg (by linarith : 0 ≤ ‖y‖ ^ 2 / 2 - 1 / 8) (by linarith : 0 ≤ 1 / t ^ 2 - 1)]
        calc t⁻¹ * Real.exp (-‖y‖ ^ 2 / (2 * t ^ 2))
            ≤ t⁻¹ * (Real.exp (1 / 8) * Real.exp (-‖y‖ ^ 2 / 2) * Real.exp (-(1 / 8) / t ^ 2)) :=
              mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr ht0.le)
          _ = _ := by ring
    _ = periodicLogJ * Real.exp (-‖y‖ ^ 2 / 2) := by
        rw [integral_const_mul]
        unfold periodicLogJ
        ring

/-- The torus LOG transport kernel is bounded by `C K^n` (Lipschitz constant `K`), `C` independent of
`K` and `v`. -/
theorem periodicLogTransportKernel_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {K : ℝ≥0} {v : PeriodicTorus ι → E}, LipschitzWith K v →
      ∀ p : PeriodicTorus ι × PeriodicTorus ι,
        |periodicLogTransportKernel n v p| ≤ C * (K : ℝ) ^ n := by
  obtain ⟨C0, hC0, hC0b⟩ := gaussianLogShortRange_transport_uniform (ι := ι) n hn
  set Cn := sourceRieszGaussianDerivativeConstant n with hCn
  have hCn0 := (sourceRieszGaussianDerivativeConstant_pos n).le
  set J := periodicLogJ with hJ
  have hJ0 := periodicLogJ_nonneg
  set Λ := periodicLatticeGaussConst ι with hΛ
  have hΛ0 := (periodicLatticeGaussConst_pos (ι := ι)).le
  set F0 := periodicLogSmoothCoeff ι with hF0
  have hF00 := (periodicLogSmoothCoeff_pos (ι := ι)).le
  set B := ∑' k : PeriodicFrequency ι, periodicLogLCCoeff (periodicHeatCut periodicRieszTau) k *
    (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ n with hB
  have hB0 : 0 ≤ B := tsum_nonneg fun k => mul_nonneg
    (periodicLogLCCoeff_nonneg _ (periodicHeatCut_pos periodicRieszTau_pos).le k) (by positivity)
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  refine ⟨F0 * (C0 + Cn * J * Λ) + B * d ^ n + 1, by positivity, ?_⟩
  intro K v hv p
  have hKn : 0 ≤ (K : ℝ) ^ n := by positivity
  by_cases hp : p.1 = p.2
  · simp only [periodicLogTransportKernel, ite_eq_left hp, abs_zero]
    positivity
  simp only [periodicLogTransportKernel, ite_eq_right hp]
  have hsub : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hz := periodicCenteredLift_mem_offLattice (ι := ι) hsub
  have hzc : ∀ i, |periodicCenteredLift (p.1 - p.2) i| ≤ 1 / 2 := fun i => periodicCenteredLift_abs_le _ i
  set z := periodicCenteredLift (p.1 - p.2) with hzdef
  set w := v p.1 - v p.2 with hwdef
  have hw : ∀ m : PeriodicFrequency ι, ‖w‖ ≤ K * ‖z + periodicFrequencyVector m‖ :=
    fun m => norm_sub_le_of_lipschitz hv p.1 p.2 m
  have hτ := periodicRieszTau_pos
  -- the derivative formula
  have hform := periodicLogSmoothLift_iteratedFDeriv periodicRieszTau hτ n hn hz
  obtain ⟨r, hr, -, hk⟩ := periodicLogProfile_translate_local_bounds periodicRieszTau hτ z hz
  obtain ⟨u, hu, hub⟩ := hk n
  have hsumD : Summable (fun m : PeriodicFrequency ι =>
      iteratedFDeriv ℝ n (gaussianLogShortRange periodicRieszTau) (z + periodicFrequencyVector m)) :=
    Summable.of_norm_bounded hu (fun m => hub m z (mem_ball_self hr))
  have hκ : iteratedFDeriv ℝ n (periodicLogSmooth (ι := ι)) z (fun _ => w) =
      F0 * ∑' m : PeriodicFrequency ι, iteratedFDeriv ℝ n (gaussianLogShortRange periodicRieszTau)
          (z + periodicFrequencyVector m) (fun _ => w) +
        iteratedFDeriv ℝ n (periodicLogLongKernel (ι := ι) (periodicHeatCut periodicRieszTau)) z
          (fun _ => w) := by
    change iteratedFDeriv ℝ n (periodicLogSmoothLift (ι := ι) periodicRieszTau) z (fun _ => w) = _
    rw [hform, add_apply, smul_apply,
      ContinuousMultilinearMap.tsum_eval hsumD]
    rfl
  rw [hκ]
  -- per-term bound
  have hterm : ∀ m : PeriodicFrequency ι,
      |iteratedFDeriv ℝ n (gaussianLogShortRange periodicRieszTau) (z + periodicFrequencyVector m)
        (fun _ => w)| ≤
      C0 * (K : ℝ) ^ n * (if m = 0 then 1 else 0) + Cn * (K : ℝ) ^ n * J *
        Real.exp (-(1 / 2) * ‖z + periodicFrequencyVector m‖ ^ 2) := by
    intro m
    have ha : z + periodicFrequencyVector m ≠ 0 := hz m
    by_cases hm : m = 0
    · subst hm
      have h0 := hC0b periodicRieszTau hτ (K := K) (a := z + periodicFrequencyVector 0) (w := w) ha
        (hw 0)
      have hone : (if (0 : PeriodicFrequency ι) = 0 then (1 : ℝ) else 0) = 1 := by simp
      rw [hone, mul_one]
      have hn' : 0 ≤ Cn * (K : ℝ) ^ n * J * Real.exp (-(1 / 2) * ‖z + periodicFrequencyVector 0‖ ^ 2) := by
        positivity
      linarith
    · simp only [ite_eq_right hm, mul_zero, zero_add]
      have hlip := periodicRankOneField_lipschitz ha (hw m)
      have h1 := sourceLogShortRange_all_order_transport_bound n periodicRieszTau hτ hlip
        (x := z + periodicFrequencyVector m) (y := 0) ha
      have hva : (periodicRankOneField (z + periodicFrequencyVector m) w) (z + periodicFrequencyVector m) = w :=
        periodicRankOneField_self ha w
      have hv0 : (periodicRankOneField (z + periodicFrequencyVector m) w) 0 = 0 := map_zero _
      simp only [sub_zero, hva, hv0] at h1
      have h2 : 2 * periodicRieszTau = 1 := periodicRieszTau_double
      rw [h2] at h1
      have hhalf := half_le_norm_add_lattice (ι := ι) hzc hm
      have h3 := gaussianLogShortRange_one_le (z + periodicFrequencyVector m) hhalf
      calc _ ≤ Cn * (K : ℝ) ^ n * gaussianLogShortRange 1 (z + periodicFrequencyVector m) := h1
        _ ≤ Cn * (K : ℝ) ^ n * (J * Real.exp (-‖z + periodicFrequencyVector m‖ ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by
          have : -‖z + periodicFrequencyVector m‖ ^ 2 / 2 = -(1 / 2) * ‖z + periodicFrequencyVector m‖ ^ 2 := by
            ring
          rw [this]; ring
  have hg1 : Summable (fun m : PeriodicFrequency ι => C0 * (K : ℝ) ^ n * (if m = 0 then (1 : ℝ) else 0)) :=
    (hasSum_ite_eq (0 : PeriodicFrequency ι) (C0 * (K : ℝ) ^ n)).summable.congr (fun m => by
      split_ifs <;> simp)
  obtain ⟨hg2s, hg2⟩ := periodic_lattice_gauss_le (ι := ι) (1 / 2) le_rfl z hzc
  have hg2' : Summable (fun m : PeriodicFrequency ι => Cn * (K : ℝ) ^ n * J *
      Real.exp (-(1 / 2) * ‖z + periodicFrequencyVector m‖ ^ 2)) := hg2s.mul_left _
  have hgs := hg1.add hg2'
  have hnorm : Summable (fun m : PeriodicFrequency ι => |iteratedFDeriv ℝ n
      (gaussianLogShortRange periodicRieszTau) (z + periodicFrequencyVector m) (fun _ => w)|) :=
    hgs.of_nonneg_of_le (fun m => abs_nonneg _) hterm
  have hsumg : (∑' m : PeriodicFrequency ι, (C0 * (K : ℝ) ^ n * (if m = 0 then (1 : ℝ) else 0) +
      Cn * (K : ℝ) ^ n * J * Real.exp (-(1 / 2) * ‖z + periodicFrequencyVector m‖ ^ 2))) ≤
      C0 * (K : ℝ) ^ n + Cn * (K : ℝ) ^ n * J * Λ := by
    rw [hg1.tsum_add hg2']
    have e1 : ∑' m : PeriodicFrequency ι, C0 * (K : ℝ) ^ n * (if m = 0 then (1 : ℝ) else 0) =
        C0 * (K : ℝ) ^ n := by
      simp [mul_ite, tsum_ite_eq]
    have e2 : ∑' m : PeriodicFrequency ι, Cn * (K : ℝ) ^ n * J *
        Real.exp (-(1 / 2) * ‖z + periodicFrequencyVector m‖ ^ 2) =
        Cn * (K : ℝ) ^ n * J * ∑' m : PeriodicFrequency ι,
          Real.exp (-(1 / 2) * ‖z + periodicFrequencyVector m‖ ^ 2) := tsum_mul_left
    rw [e1, e2]
    have : 0 ≤ Cn * (K : ℝ) ^ n * J := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hg2 this]
  have hsum_le : |∑' m : PeriodicFrequency ι, iteratedFDeriv ℝ n (gaussianLogShortRange periodicRieszTau)
        (z + periodicFrequencyVector m) (fun _ => w)| ≤
      C0 * (K : ℝ) ^ n + Cn * (K : ℝ) ^ n * J * Λ := by
    have hnorm' : Summable (fun m : PeriodicFrequency ι => ‖iteratedFDeriv ℝ n
        (gaussianLogShortRange periodicRieszTau) (z + periodicFrequencyVector m) (fun _ => w)‖) := by
      simpa only [Real.norm_eq_abs] using hnorm
    have h1 := norm_tsum_le_tsum_norm hnorm'
    simp only [Real.norm_eq_abs] at h1
    exact h1.trans ((hnorm.tsum_le_tsum hterm hgs).trans hsumg)
  -- the long kernel
  have hε := periodicHeatCut_pos hτ
  have hLnorm := norm_iteratedFDeriv_periodicLogLongKernel_le (ι := ι) (periodicHeatCut periodicRieszTau) hε n z
  have hwz : ‖w‖ ≤ K * d := by
    have h0 := hw 0
    simp only [periodicFrequencyVector_zero, add_zero] at h0
    have h1 := norm_periodicCenteredLift_le (ι := ι) (p.1 - p.2)
    exact h0.trans (mul_le_mul_of_nonneg_left h1 K.coe_nonneg)
  have hLb : |iteratedFDeriv ℝ n (periodicLogLongKernel (ι := ι) (periodicHeatCut periodicRieszTau)) z
      (fun _ => w)| ≤ B * d ^ n * (K : ℝ) ^ n := by
    refine (norm_apply_const_le _ w).trans ?_
    calc _ ≤ B * ‖w‖ ^ n := mul_le_mul_of_nonneg_right hLnorm (by positivity)
      _ ≤ B * ((K : ℝ) * d) ^ n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hwz n) hB0
      _ = B * d ^ n * (K : ℝ) ^ n := by rw [mul_pow]; ring
  calc |F0 * ∑' m : PeriodicFrequency ι, iteratedFDeriv ℝ n (gaussianLogShortRange periodicRieszTau)
          (z + periodicFrequencyVector m) (fun _ => w) +
        iteratedFDeriv ℝ n (periodicLogLongKernel (ι := ι) (periodicHeatCut periodicRieszTau)) z
          (fun _ => w)|
      ≤ |F0 * ∑' m : PeriodicFrequency ι, iteratedFDeriv ℝ n (gaussianLogShortRange periodicRieszTau)
          (z + periodicFrequencyVector m) (fun _ => w)| +
        |iteratedFDeriv ℝ n (periodicLogLongKernel (ι := ι) (periodicHeatCut periodicRieszTau)) z
          (fun _ => w)| := abs_add_le _ _
    _ ≤ F0 * (C0 * (K : ℝ) ^ n + Cn * (K : ℝ) ^ n * J * Λ) + B * d ^ n * (K : ℝ) ^ n := by
        rw [abs_mul, abs_of_nonneg hF00]
        exact add_le_add (mul_le_mul_of_nonneg_left hsum_le hF00) hLb
    _ ≤ (F0 * (C0 + Cn * J * Λ) + B * d ^ n + 1) * (K : ℝ) ^ n := by
        nlinarith [hKn]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogTransportKernel_bound
