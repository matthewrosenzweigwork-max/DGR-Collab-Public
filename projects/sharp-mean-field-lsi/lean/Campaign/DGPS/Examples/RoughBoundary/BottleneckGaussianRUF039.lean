import DGPS.Examples.RoughBoundary.Bottleneck

set_option maxHeartbeats 2000000

open MeasureTheory

namespace DGPS.Examples.RoughBoundary.Bottleneck

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.FreeEnergy
open DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Particle
open DGPS.Examples.RoughBoundary.Semicontinuity
open DGPS.Examples.RoughBoundary.Landscape

/-- The real Gaussian integral over the Euclidean plane. -/
lemma gauss_integral_E2_RUF039 {c : ℝ} (hc : 0 < c) :
    ∫ v : E2, Real.exp (-c * ‖v‖ ^ 2) = Real.pi / c := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hc, finrank_euclideanSpace_fin]
  norm_num

/-- Integrability of a centred Gaussian on the Euclidean plane. -/
lemma integrable_gauss_E2_RUF039 {c : ℝ} (hc : 0 < c) :
    Integrable (fun v : E2 => Real.exp (-c * ‖v‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E2) (b := (c : ℂ))
    (by simpa using hc) 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  simp [Complex.norm_exp, ← Complex.ofReal_pow, ← Complex.ofReal_mul]

/-- Completing the square: `∫ exp(-c|t|² + ⟪t,w⟫) dt = (π/c) exp(|w|²/(4c))`. -/
lemma gauss_shift_RUF039 {c : ℝ} (hc : 0 < c) (w : E2) :
    ∫ t : E2, Real.exp (-c * ‖t‖ ^ 2 + inner ℝ t w) =
      (Real.pi / c) * Real.exp (‖w‖ ^ 2 / (4 * c)) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hpt : ∀ t : E2, Real.exp (-c * ‖t‖ ^ 2 + inner ℝ t w) =
      Real.exp (‖w‖ ^ 2 / (4 * c)) * Real.exp (-c * ‖t - (1 / (2 * c)) • w‖ ^ 2) := by
    intro t
    rw [← Real.exp_add]
    congr 1
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  have hshift := integral_sub_right_eq_self (μ := volume)
    (fun t : E2 => Real.exp (-c * ‖t‖ ^ 2)) ((1 / (2 * c)) • w)
  simp only [hpt]
  rw [integral_const_mul]
  rw [hshift, gauss_integral_E2_RUF039 hc, mul_comm]

/-- Complete the square in the exponent `n κ |n⁻¹ w|² / 2`. -/
lemma gaussian_completion_RUF039 {κ n : ℝ} (hκ : 0 < κ) (hn : 0 < n) (w : E2) :
    Real.exp (n * κ * ‖n⁻¹ • w‖ ^ 2 / 2) =
      (n / (2 * Real.pi * κ)) *
        ∫ t : E2, Real.exp (-(n / (2 * κ)) * ‖t‖ ^ 2 + inner ℝ t w) := by
  have hc : 0 < n / (2 * κ) := by positivity
  have hn0 : n ≠ 0 := hn.ne'
  have hκ0 : κ ≠ 0 := hκ.ne'
  rw [gauss_shift_RUF039 hc w]
  have hexp : n * κ * ‖n⁻¹ • w‖ ^ 2 / 2 = ‖w‖ ^ 2 / (4 * (n / (2 * κ))) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  have hpref : n / (2 * Real.pi * κ) * (Real.pi / (n / (2 * κ))) = 1 := by
    field_simp
  rw [hexp]
  calc Real.exp (‖w‖ ^ 2 / (4 * (n / (2 * κ))))
      = (n / (2 * Real.pi * κ) * (Real.pi / (n / (2 * κ)))) *
          Real.exp (‖w‖ ^ 2 / (4 * (n / (2 * κ)))) := by rw [hpref, one_mul]
    _ = _ := by ring

/-- Product integration over the particle measure. -/
lemma product_exp_RUF039 {L ε : ℝ} (N : ℕ+) (t : E2) :
    ∫ x : ParticleSpace 1 N, Real.exp (inner ℝ t (∑ i, Ufeat L ε (x i)))
        ∂particleHaar 1 N =
      (∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1) ^ (N : ℕ) := by
  change ∫ x : Fin N → Torus 1, Real.exp (inner ℝ t (∑ i, Ufeat L ε (x i)))
      ∂(Measure.pi fun _ : Fin N => haar 1) = _
  calc
    _ = ∫ x : Fin N → Torus 1, ∏ i, Real.exp (inner ℝ t (Ufeat L ε (x i)))
        ∂(Measure.pi fun _ : Fin N => haar 1) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by simp only [inner_sum, Real.exp_sum]
    _ = ∏ i, ∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1 :=
          integral_fintype_prod_eq_prod (fun _ y => Real.exp (inner ℝ t (Ufeat L ε y)))
    _ = _ := by simp

/-- The one-site log moment generating function is positive. -/
lemma integral_exp_inner_pos_RUF039 {L ε : ℝ} (hL : 0 < L) (t : E2) :
    0 < ∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1 := by
  apply integral_exp_pos
  refine Integrable.mono' (integrable_const (Real.exp ‖t‖)) ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.inner (continuous_Ufeat hL ε))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have h := real_inner_le_norm t (Ufeat L ε y)
    rw [norm_Ufeat] at h
    linarith

/-- Pointwise bound used for Fubini: `exp(-c r² + n r) ≤ exp(-(c/2) r²) exp(n²/(2c))`. -/
lemma exp_quad_bound_RUF039 {c n r : ℝ} (hc : 0 < c) :
    Real.exp (-c * r ^ 2 + n * r) ≤ Real.exp (-(c / 2) * r ^ 2) * Real.exp (n ^ 2 / (2 * c)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h2c : 0 < 2 * c := by positivity
  have hid : (-(c / 2) * r ^ 2 + n ^ 2 / (2 * c)) - (-c * r ^ 2 + n * r) =
      (c * r - n) ^ 2 / (2 * c) := by
    field_simp
    ring
  have hnn := div_nonneg (sq_nonneg (c * r - n)) h2c.le
  linarith

/-- Joint integrability of the Gibbs-weighted Gaussian integrand over particles and plane. -/
lemma integrable_joint_RUF039 {L ε κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (N : ℕ+) :
    Integrable (fun z : ParticleSpace 1 N × E2 =>
        Real.exp (-((N : ℝ) / (2 * κ)) * ‖z.2‖ ^ 2 +
          inner ℝ z.2 (∑ i, Ufeat L ε (z.1 i))))
      ((particleHaar 1 N).prod (volume : Measure E2)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hc : 0 < (N : ℝ) / (2 * κ) := by positivity
  have hU : Continuous (Ufeat L ε) := continuous_Ufeat hL ε
  have hS : Continuous (fun z : ParticleSpace 1 N × E2 => ∑ i, Ufeat L ε (z.1 i)) :=
    continuous_finsetSum _ fun i _ => hU.comp ((continuous_apply i).comp continuous_fst)
  have hcont : Continuous (fun z : ParticleSpace 1 N × E2 =>
      Real.exp (-((N : ℝ) / (2 * κ)) * ‖z.2‖ ^ 2 +
        inner ℝ z.2 (∑ i, Ufeat L ε (z.1 i)))) :=
    Real.continuous_exp.comp
      ((continuous_const.mul (continuous_snd.norm.pow 2)).add (continuous_snd.inner hS))
  refine Integrable.mono'
    (g := fun z : ParticleSpace 1 N × E2 =>
      Real.exp (-(((N : ℝ) / (2 * κ)) / 2) * ‖z.2‖ ^ 2) * Real.exp (((N : ℝ) ^ 2) / (2 * ((N : ℝ) / (2 * κ)))))
    ?_ hcont.aestronglyMeasurable ?_
  · exact ((integrable_gauss_E2_RUF039 (half_pos hc)).mul_const
      (Real.exp (((N : ℝ) ^ 2) / (2 * ((N : ℝ) / (2 * κ)))))).comp_snd (particleHaar 1 N)
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine le_trans (Real.exp_le_exp.mpr ?_) (exp_quad_bound_RUF039 (r := ‖z.2‖) hc)
    have hSn : ‖∑ i, Ufeat L ε (z.1 i)‖ ≤ (N : ℝ) := by
      calc ‖∑ i, Ufeat L ε (z.1 i)‖ ≤ ∑ i, ‖Ufeat L ε (z.1 i)‖ := norm_sum_le _ _
        _ = (N : ℝ) := by simp [norm_Ufeat]
    have hip := real_inner_le_norm z.2 (∑ i, Ufeat L ε (z.1 i))
    have hmul := mul_le_mul_of_nonneg_left hSn (norm_nonneg z.2)
    linarith

/-- Inner integral over the particles of the Gibbs-weighted Gaussian integrand. -/
lemma inner_integral_RUF039 {L ε c : ℝ} (N : ℕ+) (t : E2) :
    ∫ x : ParticleSpace 1 N, Real.exp (-c * ‖t‖ ^ 2 + inner ℝ t (∑ i, Ufeat L ε (x i)))
        ∂particleHaar 1 N =
      Real.exp (-c * ‖t‖ ^ 2) * (∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1) ^ (N : ℕ) := by
  simp only [Real.exp_add]
  rw [integral_const_mul, product_exp_RUF039 N t]

/-- The exact Gaussian representation of the shifted partition function, for general
parameters: `Z_N = (N/(2πκ)) ∫ exp(-N Ψ(t)) dt`. -/
theorem exact_gaussian_representation_general_RUF039 {L ε κ : ℝ} (hL : 0 < L) (hκ : 0 < κ)
    (N : ℕ+) :
    ∫ x : ParticleSpace 1 N,
        Real.exp ((N : ℝ) * κ * ‖(N : ℝ)⁻¹ • ∑ i, Ufeat L ε (x i)‖ ^ 2 / 2)
          ∂particleHaar 1 N =
      ((N : ℝ) / (2 * Real.pi * κ)) *
        ∫ t : E2, Real.exp (-(N : ℝ) * featurePotential κ (Ufeat L ε) t) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hpt : ∀ x : ParticleSpace 1 N,
      Real.exp ((N : ℝ) * κ * ‖(N : ℝ)⁻¹ • ∑ i, Ufeat L ε (x i)‖ ^ 2 / 2) =
        ((N : ℝ) / (2 * Real.pi * κ)) *
          ∫ t : E2, Real.exp (-((N : ℝ) / (2 * κ)) * ‖t‖ ^ 2 +
            inner ℝ t (∑ i, Ufeat L ε (x i))) :=
    fun x => gaussian_completion_RUF039 hκ hn _
  calc
    _ = ∫ x : ParticleSpace 1 N, ((N : ℝ) / (2 * Real.pi * κ)) *
          ∫ t : E2, Real.exp (-((N : ℝ) / (2 * κ)) * ‖t‖ ^ 2 +
            inner ℝ t (∑ i, Ufeat L ε (x i))) ∂volume ∂particleHaar 1 N :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((N : ℝ) / (2 * Real.pi * κ)) * ∫ x : ParticleSpace 1 N,
          ∫ t : E2, Real.exp (-((N : ℝ) / (2 * κ)) * ‖t‖ ^ 2 +
            inner ℝ t (∑ i, Ufeat L ε (x i))) ∂volume ∂particleHaar 1 N :=
          integral_const_mul _ _
    _ = ((N : ℝ) / (2 * Real.pi * κ)) * ∫ t : E2, ∫ x : ParticleSpace 1 N,
          Real.exp (-((N : ℝ) / (2 * κ)) * ‖t‖ ^ 2 +
            inner ℝ t (∑ i, Ufeat L ε (x i))) ∂particleHaar 1 N ∂volume := by
          rw [integral_integral_swap
            (f := fun (x : ParticleSpace 1 N) (t : E2) => Real.exp (-((N : ℝ) / (2 * κ)) * ‖t‖ ^ 2 +
              inner ℝ t (∑ i, Ufeat L ε (x i))))
            (integrable_joint_RUF039 hL hκ N)]
    _ = ((N : ℝ) / (2 * Real.pi * κ)) * ∫ t : E2,
          Real.exp (-((N : ℝ) / (2 * κ)) * ‖t‖ ^ 2) *
            (∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1) ^ (N : ℕ) := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun t => inner_integral_RUF039 N t)
    _ = _ := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          have hA := integral_exp_inner_pos_RUF039 (ε := ε) hL t
          dsimp only
          unfold featurePotential featureLogPartition
          rw [show -(N : ℝ) * (‖t‖ ^ 2 / (2 * κ) - Real.log (∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1))
              = -((N : ℝ) / (2 * κ)) * ‖t‖ ^ 2 +
                (N : ℝ) * Real.log (∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1) by ring]
          rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hA]

/-- Kappa positivity for the feature constant used in the Bottleneck module. -/
lemma kappa0_pos_RUF039 : 0 < kappa0 := by
  unfold kappa0
  norm_num

/-- The exact Gaussian representation of the shifted partition function
`Z_N = ∫ exp(N κ |M_N|² / 2) dm^N = (N/(2πκ)) ∫_{ℝ²} exp(-N Ψ(t)) dt` for the selected
parameter, with the RUF027 free-energy decomposition as the consumed interface. -/
theorem exact_gaussian_representation_of_shifted_partition :
    ∃ L : ℝ, 0 < L ∧ FreeEnergyDecomposition L (1 / L) ∧
      ∀ N : ℕ+,
        ∫ x : ParticleSpace 1 N,
            Real.exp ((N : ℝ) * kappa0 * ‖(N : ℝ)⁻¹ • ∑ i, Ufeat L (1 / L) (x i)‖ ^ 2 / 2)
              ∂particleHaar 1 N =
          ((N : ℝ) / (2 * Real.pi * kappa0)) *
            ∫ t : E2, Real.exp (-(N : ℝ) * featurePotential kappa0 (Ufeat L (1 / L)) t) := by
  obtain ⟨_, L₀, _, h1, _, _, L, hL₀L, _, hFree⟩ :=
    exact_free_energy_decomposition_and_unique_haar_minimizer
  have hL : 0 < L := by linarith
  exact ⟨L, hL, hFree, fun N =>
    exact_gaussian_representation_general_RUF039 hL kappa0_pos_RUF039 N⟩

end DGPS.Examples.RoughBoundary.Bottleneck
