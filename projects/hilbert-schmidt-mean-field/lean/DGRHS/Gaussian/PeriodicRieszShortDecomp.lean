import DGRHS.Gaussian.PeriodicHeatRealSeries
import DGRHS.Gaussian.PeriodicProfileLatticeSum
import DGRHS.Gaussian.PeriodicRieszMellinIdentification
import DGRHS.Gaussian.RieszGaussianTruncationComparison

/-!
Packet P9h, unit 2 (part 6): the short heat-time piece of the periodic Riesz kernel as a lattice
sum of Gaussian-scale profiles.

With `p = (d-s)/2 - 1` and the heat time `u = 2π²t²` (Euclidean scale `t`), for `z` off the lattice
`∫_{0<u≤2π²τ²} u^p Re H(u, z) du = Σ_m K₀ ∫_{0<t≤τ} t^{-s-1} e^{-|z+m|²/(2t²)} dt`,
`K₀ = π^{d/2} · 4π² · (2π²)^{-s/2-1}`.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Constant relating the heat-time short integral to the Gaussian-scale profile. -/
def periodicRieszProfileConst (ι : Type u) [Fintype ι] (s : ℝ) : ℝ :=
  Real.pi ^ ((Fintype.card ι : ℝ) / 2) * (4 * Real.pi ^ 2) * (2 * Real.pi ^ 2) ^ (-s / 2 - 1)

lemma periodicRieszProfileConst_pos (s : ℝ) : 0 < periodicRieszProfileConst ι s := by
  unfold periodicRieszProfileConst
  positivity

/-- Heat-time integrand of a single lattice image. -/
def periodicHeatImageIntegrand (s : ℝ) (y : E) (u : ℝ) : ℝ :=
  Real.pi ^ ((Fintype.card ι : ℝ) / 2) * u ^ (-s / 2 - 1) * Real.exp (-Real.pi ^ 2 * ‖y‖ ^ 2 / u)

lemma periodic_heat_weight_eq (s : ℝ) {u : ℝ} (hu : 0 < u) :
    u ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) * (Real.pi / u) ^ ((Fintype.card ι : ℝ) / 2) =
      Real.pi ^ ((Fintype.card ι : ℝ) / 2) * u ^ (-s / 2 - 1) := by
  rw [Real.div_rpow Real.pi_pos.le hu.le, ← mul_div_assoc, mul_comm, mul_div_assoc,
    ← Real.rpow_sub hu]
  congr 2
  ring

lemma periodic_heat_weighted_eq_tsum (s : ℝ) (z : E) {u : ℝ} (hu : 0 < u) :
    u ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) * (periodicGaussianHeat u (periodicLift z)).re =
      ∑' m : PeriodicFrequency ι, periodicHeatImageIntegrand s (z + periodicFrequencyVector m) u := by
  rw [periodicGaussianHeat_lift_re_eq_image_sum u hu z, ← mul_assoc, periodic_heat_weight_eq s hu]
  unfold periodicHeatImageIntegrand
  rw [← tsum_mul_left]

/-- Value of the substituted integrand. -/
lemma periodicHeatImageIntegrand_sub (s τ : ℝ) (y : E) {t : ℝ} (ht : 0 < t) :
    |4 * Real.pi ^ 2 * t| • periodicHeatImageIntegrand s y (2 * Real.pi ^ 2 * t ^ 2) =
      periodicRieszProfileConst ι s * (t ^ (-s - 1) * sourceRieszGaussianScale t y) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h2 : (0 : ℝ) ≤ 2 * Real.pi ^ 2 := by positivity
  have hpow : (2 * Real.pi ^ 2 * t ^ 2) ^ (-s / 2 - 1) =
      (2 * Real.pi ^ 2) ^ (-s / 2 - 1) * t ^ (-s - 2) := by
    have h3 : (t ^ 2) ^ (-s / 2 - 1) = t ^ (-s - 2) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
      congr 1
      push_cast
      ring
    rw [Real.mul_rpow h2 (sq_nonneg t), h3]
  have hexp : -Real.pi ^ 2 * ‖y‖ ^ 2 / (2 * Real.pi ^ 2 * t ^ 2) = -‖y‖ ^ 2 / (2 * t ^ 2) := by
    field_simp
  have ht1 : t * t ^ (-s - 2) = t ^ (-s - 1) := by
    rw [show (-s - 1) = (-s - 2) + 1 by ring, Real.rpow_add_one ht.ne']; ring
  rw [smul_eq_mul, abs_of_pos (by positivity), periodicHeatImageIntegrand, hpow, hexp]
  unfold sourceRieszGaussianScale periodicRieszProfileConst
  rw [← ht1]
  ring

/-- The change of variables `u = 2π²t²` between the heat-time integral of an image and the
Gaussian-scale profile. -/
lemma periodicHeatImage_substitution (s τ : ℝ) (hs : 0 < s) (hτ : 0 < τ) (y : E) :
    ∫ u in Ioc 0 (2 * Real.pi ^ 2 * τ ^ 2), periodicHeatImageIntegrand s y u =
      periodicProfile (periodicRieszProfileConst ι s) s (Ioc 0 τ) y ∧
    (y ≠ 0 → IntegrableOn (periodicHeatImageIntegrand s y) (Ioc 0 (2 * Real.pi ^ 2 * τ ^ 2))) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  let f : ℝ → ℝ := fun t => 2 * Real.pi ^ 2 * t ^ 2
  let f' : ℝ → ℝ := fun t => 4 * Real.pi ^ 2 * t
  have hS : MeasurableSet (Ioc (0 : ℝ) τ) := measurableSet_Ioc
  have hf' : ∀ t ∈ Ioc (0 : ℝ) τ, HasDerivWithinAt f (f' t) (Ioc 0 τ) t := by
    intro t _
    have h := (hasDerivAt_pow 2 t).const_mul (2 * Real.pi ^ 2)
    refine (h.hasDerivWithinAt).congr_deriv ?_
    simp only [f']
    push_cast
    ring
  have hinj : InjOn f (Ioc 0 τ) := by
    intro a ha b hb hab
    have h : a ^ 2 = b ^ 2 := by
      have hc : (2 * Real.pi ^ 2) ≠ 0 := by positivity
      exact mul_left_cancel₀ hc hab
    exact (pow_left_inj₀ ha.1.le hb.1.le (by norm_num)).1 h
  have himage : f '' Ioc 0 τ = Ioc 0 (2 * Real.pi ^ 2 * τ ^ 2) := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨by have := ht.1; positivity, ?_⟩
      have := ht.2
      have h0 := ht.1
      show 2 * Real.pi ^ 2 * t ^ 2 ≤ 2 * Real.pi ^ 2 * τ ^ 2
      have : t ^ 2 ≤ τ ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    · intro hu
      refine ⟨Real.sqrt (u / (2 * Real.pi ^ 2)), ⟨Real.sqrt_pos.2 (div_pos hu.1 (by positivity)), ?_⟩, ?_⟩
      · rw [Real.sqrt_le_left hτ.le]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hu.2]
      · show 2 * Real.pi ^ 2 * Real.sqrt (u / (2 * Real.pi ^ 2)) ^ 2 = u
        rw [Real.sq_sqrt (div_pos hu.1 (by positivity)).le]
        field_simp
  have hint : IntegrableOn (fun t => |f' t| • periodicHeatImageIntegrand s y (f t)) (Ioc 0 τ) ∨ y = 0 := by
    by_cases hy : y = 0
    · exact Or.inr hy
    · left
      have h := (DGRHS.Gaussian.integrableOn_gaussianRieszEuclidean_full_scale s hs y hy).mono_set
        (fun t (ht : t ∈ Ioc (0 : ℝ) τ) => (ht.1 : t ∈ Ioi (0 : ℝ)))
      exact IntegrableOn.congr_fun (h.const_mul (periodicRieszProfileConst ι s))
        (fun t ht => (periodicHeatImageIntegrand_sub s τ y ht.1).symm) hS
  constructor
  · rw [← himage, integral_image_eq_integral_abs_deriv_smul hS hf' hinj]
    rw [setIntegral_congr_fun hS (fun t ht => periodicHeatImageIntegrand_sub s τ y ht.1)]
    unfold periodicProfile
    rw [integral_const_mul]
  · intro hy
    rw [← himage]
    refine (integrableOn_image_iff_integrableOn_abs_deriv_smul hS hf' hinj _).2 ?_
    rcases hint with h | h
    · exact h
    · exact absurd h hy

end DGRHS.Periodic
