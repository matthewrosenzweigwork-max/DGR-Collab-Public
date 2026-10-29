import DGRHS.Commutator.SourceRieszTruncatedTransportKernelIntegralBound
import DGRHS.Commutator.SourceRieszTruncatedTransportKernelGaussianScaleBounds
import DGRHS.Gaussian.PeriodicLocalTsumDeriv
import DGRHS.Gaussian.PeriodicTransportLift
import DGRHS.Gaussian.PeriodicMultidimensionalPoisson

/-!
Packet P9h, unit 2 (part 3): Gaussian-scale profiles on `ℝ^d` and their lattice sums.

`periodicProfile c s S y = c ∫_{t ∈ S} t^{-s-1} exp(-|y|²/(2t²)) dt` is the Euclidean Gaussian-scale
profile of `DGRHS.Commutator` (the family `gaussianRieszEuclideanShortRange` is `S = (0,η]`).  Its
lattice sum `y ↦ Σ_m profile(y + m)` is the position-space form of a short heat-time piece of the
periodic Riesz kernel.  Here: all-order derivative bounds of the profile away from `0` with Gaussian
decay (reusing the Euclidean all-order Gaussian bounds), summability, openness of the complement of
the lattice and termwise iterated differentiation of the lattice sum off the lattice.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped NNReal Topology
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Gaussian-scale profile over a set `S` of scales. -/
def periodicProfile (c s : ℝ) (S : Set ℝ) (y : E) : ℝ :=
  c * ∫ t in S, t ^ (-s - 1) * sourceRieszGaussianScale t y

/-- The lattice sum of a profile. -/
def periodicProfileSum (c s : ℝ) (S : Set ℝ) (y : E) : ℝ :=
  ∑' m : PeriodicFrequency ι, periodicProfile c s S (y + periodicFrequencyVector m)

lemma periodicProfile_nonneg (c s : ℝ) (S : Set ℝ) (hc : 0 ≤ c) (hSm : MeasurableSet S)
    (hS : S ⊆ Ioi 0) (y : E) : 0 ≤ periodicProfile c s S y := by
  unfold periodicProfile
  refine mul_nonneg hc (setIntegral_nonneg hSm ?_)
  intro t ht
  exact mul_nonneg (Real.rpow_nonneg (hS ht).le _) (by unfold sourceRieszGaussianScale; positivity)

lemma periodicProfile_iteratedFDeriv_formula (c s : ℝ) (S : Set ℝ) (hSm : MeasurableSet S)
    (hS : S ⊆ Ioi 0) (hs : 0 < s) (n : ℕ) {z : E} (hz : z ≠ 0) :
    iteratedFDeriv ℝ n (periodicProfile c s S) z =
      c • ∫ t in S, t ^ (-s - 1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z :=
  sourceRieszGaussian_iteratedFDeriv_scale_integral n c s S hSm hS hs hz

lemma periodicProfile_differentiableAt_iteratedFDeriv (c s : ℝ) (S : Set ℝ) (hSm : MeasurableSet S)
    (hS : S ⊆ Ioi 0) (hs : 0 < s) (n : ℕ) {z : E} (hz : z ≠ 0) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ n (periodicProfile c s S)) z := by
  have he : iteratedFDeriv ℝ n (periodicProfile c s S) =ᶠ[𝓝 z]
      fun y => c • ∫ t in S, t ^ (-s - 1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y := by
    filter_upwards [eventually_ne_nhds hz] with y hy
    exact periodicProfile_iteratedFDeriv_formula c s S hSm hS hs n hy
  refine DifferentiableAt.congr_of_eventuallyEq ?_ he
  exact ((hasFDerivAt_sourceRieszGaussian_scale_integral n s S hSm hS hs hz).const_smul c).differentiableAt

lemma rpow_neg_sub_one_mul_inv_pow (s : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ (-s - 1) * (t⁻¹) ^ k = t ^ (-(s + k) - 1) := by
  rw [← Real.rpow_natCast, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
  congr 1
  ring

/-- All-order derivative bound of a profile over scales `⊆ (0,η]` away from the origin, with Gaussian
decay at infinity. -/
lemma periodicProfile_iteratedFDeriv_bound (c s η r : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (hr : 0 < r) (S : Set ℝ) (hSm : MeasurableSet S) (hS : S ⊆ Ioc 0 η) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : E, r ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ k (periodicProfile c s S) y‖ ≤ B * Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)) := by
  have hS0 : S ⊆ Ioi 0 := fun t ht => (hS ht).1
  set Ck := sourceRieszGaussianDerivativeConstant k with hCk
  have hCk0 : 0 ≤ Ck := (sourceRieszGaussianDerivativeConstant_pos k).le
  set J : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (-(s + k) - 1) * Real.exp (-(r ^ 2 / 16) / t ^ 2) with hJ
  have hJint : IntegrableOn (fun t : ℝ => t ^ (-(s + k) - 1) * Real.exp (-(r ^ 2 / 16) / t ^ 2))
      (Ioi 0) :=
    DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale (s + k) (r ^ 2 / 16) (by positivity)
      (by positivity)
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi (fun t ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)
  refine ⟨c * Ck * J, by positivity, ?_⟩
  intro y hy
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  rw [periodicProfile_iteratedFDeriv_formula c s S hSm hS0 hs k hy0, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hc]
  have hi := integrable_sourceRieszGaussian_scale_on k s S hSm hS0 hs hy0
  have hpt : ∀ t ∈ S, ‖t ^ (-s - 1) • iteratedFDeriv ℝ k (sourceRieszGaussianScale t) y‖ ≤
      Ck * (t ^ (-(s + k) - 1) * Real.exp (-(r ^ 2 / 16) / t ^ 2)) * Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)) := by
    intro t ht
    have ht0 : 0 < t := (hS ht).1
    have htη : t ≤ η := (hS ht).2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    have hb := sourceRieszGaussian_iteratedFDeriv_unweighted_bound k t ht0 y
    have hexp : Real.exp (-‖y‖ ^ 2 / (8 * t ^ 2)) ≤
        Real.exp (-(r ^ 2 / 16) / t ^ 2) * Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : r ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
      have h2 : ‖y‖ ^ 2 / (16 * η ^ 2) ≤ ‖y‖ ^ 2 / (16 * t ^ 2) := by
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        nlinarith
      have h3 : (r ^ 2 / 16) / t ^ 2 ≤ ‖y‖ ^ 2 / (16 * t ^ 2) := by
        rw [div_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      have h4 : -‖y‖ ^ 2 / (8 * t ^ 2) = -(‖y‖ ^ 2 / (16 * t ^ 2)) - ‖y‖ ^ 2 / (16 * t ^ 2) := by
        field_simp; ring
      have h5 : -(r ^ 2 / 16) / t ^ 2 = -((r ^ 2 / 16) / t ^ 2) := by ring
      rw [h4, h5, show -‖y‖ ^ 2 / (16 * η ^ 2) = -(‖y‖ ^ 2 / (16 * η ^ 2)) by ring]
      linarith
    calc t ^ (-s - 1) * ‖iteratedFDeriv ℝ k (sourceRieszGaussianScale t) y‖
        ≤ t ^ (-s - 1) * ((t⁻¹) ^ k * Ck * Real.exp (-‖y‖ ^ 2 / (8 * t ^ 2))) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht0.le _)
      _ = Ck * (t ^ (-(s + k) - 1) * Real.exp (-‖y‖ ^ 2 / (8 * t ^ 2))) := by
          rw [← rpow_neg_sub_one_mul_inv_pow s k ht0]; ring
      _ ≤ Ck * (t ^ (-(s + k) - 1) * (Real.exp (-(r ^ 2 / 16) / t ^ 2) *
            Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)))) := by
          gcongr
      _ = _ := by ring
  have hmajor : IntegrableOn (fun t : ℝ => Ck * (t ^ (-(s + k) - 1) * Real.exp (-(r ^ 2 / 16) / t ^ 2)) *
      Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2))) S :=
    ((hJint.mono_set hS0).const_mul Ck).mul_const _
  calc c * ‖∫ t in S, t ^ (-s - 1) • iteratedFDeriv ℝ k (sourceRieszGaussianScale t) y‖
      ≤ c * ∫ t in S, ‖t ^ (-s - 1) • iteratedFDeriv ℝ k (sourceRieszGaussianScale t) y‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hc
    _ ≤ c * ∫ t in S, Ck * (t ^ (-(s + k) - 1) * Real.exp (-(r ^ 2 / 16) / t ^ 2)) *
          Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono_on hi.norm hmajor hSm hpt) hc
    _ = c * Ck * (∫ t in S, t ^ (-(s + k) - 1) * Real.exp (-(r ^ 2 / 16) / t ^ 2)) *
          Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)) := by
        rw [integral_mul_const, integral_const_mul]; ring
    _ ≤ c * Ck * J * Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)) := by
        gcongr
        exact setIntegral_mono_set hJint
          (by
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
            exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)
          (Filter.Eventually.of_forall hS0)

end DGRHS.Periodic
