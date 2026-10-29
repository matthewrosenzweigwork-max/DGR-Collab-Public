import DGRHS.Gaussian.PeriodicTsumIntegralLe
import DGRHS.Gaussian.PeriodicProfileLatticeSum
import DGRHS.Gaussian.PeriodicShortHeatLatticeSum
import DGRHS.Gaussian.RieszGaussianFullScale

/-!
Packet P9h, unit 2 (part 15): uniform bounds of lattice Gaussian sums and diagonal caps of the band
integrals `Σ_m ∫_{η<t≤1/2} t^{-s-1} e^{-|z+m|²/(a t²)} dt ≤ Λ η^{-s}/s` for `a ≤ 8` and `z` in the
centered cell.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Uniform bound `Λ₀ = 1 + Σ_k e^{-‖k‖²/16}` of centered-cell lattice Gaussian sums. -/
def periodicLatticeGaussConst (ι : Type u) [Fintype ι] [Nonempty ι] : ℝ :=
  1 + ∑' k : PeriodicFrequency ι, Real.exp (-‖periodicFrequencyVector k‖ ^ 2 / 16)

lemma periodicLatticeGaussConst_pos : 0 < periodicLatticeGaussConst ι := by
  unfold periodicLatticeGaussConst
  have : 0 ≤ ∑' k : PeriodicFrequency ι, Real.exp (-‖periodicFrequencyVector k‖ ^ 2 / 16) :=
    tsum_nonneg fun k => (Real.exp_pos _).le
  linarith

lemma periodic_lattice_gauss_le (B : ℝ) (hB : 1 / 2 ≤ B) (z : E) (hz : ∀ i, |z i| ≤ 1 / 2) :
    Summable (fun m : PeriodicFrequency ι => Real.exp (-B * ‖z + periodicFrequencyVector m‖ ^ 2)) ∧
    ∑' m : PeriodicFrequency ι, Real.exp (-B * ‖z + periodicFrequencyVector m‖ ^ 2) ≤
      periodicLatticeGaussConst ι := by
  obtain ⟨hs, hle⟩ := periodic_short_gaussian_spatial_bound z hz 1 one_pos le_rfl
  have hmono : ∀ m : PeriodicFrequency ι, Real.exp (-B * ‖z + periodicFrequencyVector m‖ ^ 2) ≤
      Real.exp (-‖z + periodicFrequencyVector m‖ ^ 2 / (2 * 1 ^ 2)) := by
    intro m
    apply Real.exp_le_exp.mpr
    have h0 := sq_nonneg ‖z + periodicFrequencyVector m‖
    nlinarith
  have hsum : Summable (fun m : PeriodicFrequency ι => Real.exp (-B * ‖z + periodicFrequencyVector m‖ ^ 2)) :=
    hs.of_nonneg_of_le (fun m => (Real.exp_pos _).le) hmono
  refine ⟨hsum, ?_⟩
  calc _ ≤ ∑' m : PeriodicFrequency ι, Real.exp (-‖z + periodicFrequencyVector m‖ ^ 2 / (2 * 1 ^ 2)) :=
        hsum.tsum_le_tsum hmono hs
    _ ≤ Real.exp (-‖z‖ ^ 2 / (2 * 1 ^ 2)) + Real.exp (-1 / (16 * 1 ^ 2)) *
        ∑' k : PeriodicFrequency ι, Real.exp (-‖periodicFrequencyVector k‖ ^ 2 / 16) := hle
    _ ≤ periodicLatticeGaussConst ι := by
        unfold periodicLatticeGaussConst
        have h1 : Real.exp (-‖z‖ ^ 2 / (2 * 1 ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
          have := sq_nonneg ‖z‖; nlinarith [this])
        have h2 : Real.exp (-1 / (16 * 1 ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
        have h3 : 0 ≤ ∑' k : PeriodicFrequency ι, Real.exp (-‖periodicFrequencyVector k‖ ^ 2 / 16) :=
          tsum_nonneg fun k => (Real.exp_pos _).le
        nlinarith


/-- Diagonal cap of the band lattice Gaussian integrals. -/
theorem periodic_band_lattice_integral_le (a : ℝ) (ha0 : 0 < a) (ha8 : a ≤ 8) (s η : ℝ) (hs : 0 < s)
    (hη : 0 < η) (z : E) (hzc : ∀ i, |z i| ≤ 1 / 2) (hz : z ∈ (periodicOffLattice : Set E)) :
    Summable (fun m : PeriodicFrequency ι => ∫ t in Ioc η (1 / 2 : ℝ),
        t ^ (-s - 1) * Real.exp (-‖z + periodicFrequencyVector m‖ ^ 2 / (a * t ^ 2))) ∧
    ∑' m : PeriodicFrequency ι, (∫ t in Ioc η (1 / 2 : ℝ),
        t ^ (-s - 1) * Real.exp (-‖z + periodicFrequencyVector m‖ ^ 2 / (a * t ^ 2))) ≤
      periodicLatticeGaussConst ι * (η ^ (-s) / s) := by
  set Λ := periodicLatticeGaussConst ι with hΛ
  have hΛ0 : 0 < Λ := periodicLatticeGaussConst_pos
  let F : PeriodicFrequency ι → ℝ → ℝ := fun m t =>
    t ^ (-s - 1) * Real.exp (-‖z + periodicFrequencyVector m‖ ^ 2 / (a * t ^ 2))
  let g : ℝ → ℝ := fun t => Λ * t ^ (-s - 1)
  have hSsub : Ioc η (1 / 2 : ℝ) ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le hη ht.1.le
  have hgint : IntegrableOn g (Ioi η) := (integrableOn_Ioi_rpow_of_lt (by linarith : -s - 1 < -1) hη).const_mul Λ
  have hF : ∀ m, Integrable (F m) (volume.restrict (Ioc η (1 / 2 : ℝ))) := by
    intro m
    have hy : z + periodicFrequencyVector m ≠ 0 := hz m
    have hh := (DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale s (‖z + periodicFrequencyVector m‖ ^ 2 / a) hs
      (by have := norm_pos_iff.mpr hy; positivity)).mono_set hSsub
    refine hh.congr_fun (fun t ht => ?_) measurableSet_Ioc
    simp only [F]
    congr 2
    field_simp
  have hnn : ∀ m, 0 ≤ᵐ[volume.restrict (Ioc η (1 / 2 : ℝ))] F m := by
    intro m
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (Real.rpow_nonneg (hSsub ht).le _) (Real.exp_pos _).le
  have hlat : ∀ t ∈ Ioc η (1 / 2 : ℝ), Summable (fun m => F m t) ∧ ∑' m, F m t ≤ g t := by
    intro t ht
    have ht0 : 0 < t := hSsub ht
    have hB : 1 / 2 ≤ 1 / (a * t ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : t ^ 2 ≤ 1 / 4 := by nlinarith [ht.2]
      nlinarith [this]
    obtain ⟨hs1, hle⟩ := periodic_lattice_gauss_le (1 / (a * t ^ 2)) hB z hzc
    have he : ∀ m : PeriodicFrequency ι, F m t =
        t ^ (-s - 1) * Real.exp (-(1 / (a * t ^ 2)) * ‖z + periodicFrequencyVector m‖ ^ 2) := by
      intro m; simp only [F]; congr 2; field_simp
    simp_rw [he]
    refine ⟨hs1.mul_left _, ?_⟩
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg ht0.le _) |>.trans (le_of_eq (by simp only [g]; ring))
  have hpt : ∀ᵐ t ∂(volume.restrict (Ioc η (1 / 2 : ℝ))), Summable fun m => F m t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using (hlat t ht).1
  have hle : ∀ᵐ t ∂(volume.restrict (Ioc η (1 / 2 : ℝ))), ∑' m, F m t ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using (hlat t ht).2
  have hgI : Integrable g (volume.restrict (Ioc η (1 / 2 : ℝ))) := hgint.mono_set (fun t ht => ht.1)
  obtain ⟨hsum, hbound⟩ := summable_integral_tsum_le hF hnn hpt hgI hle
  refine ⟨hsum, hbound.trans ?_⟩
  calc ∫ t in Ioc η (1 / 2 : ℝ), g t ≤ ∫ t in Ioi η, g t := by
        apply setIntegral_mono_set hgint
        · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact mul_nonneg hΛ0.le (Real.rpow_nonneg (lt_trans hη ht).le _)
        · exact Filter.Eventually.of_forall (fun t ht => ht.1)
    _ = Λ * (η ^ (-s) / s) := by
        simp only [g]
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s - 1 < -1) hη]
        congr 1
        rw [show -s - 1 + 1 = -s by ring]
        field_simp

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_band_lattice_integral_le
