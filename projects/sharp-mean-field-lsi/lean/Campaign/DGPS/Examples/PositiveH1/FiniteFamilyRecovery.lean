import Mathlib
import DGPS.Examples.PositiveH1.Recovery
import DGPS.Examples.PositiveH1.Dissipation

/-!
# Finite family exact entropy recovery (H1017)

For the rough model `kernelData κ` on `𝕋¹` (`κ ≥ 0`), a species family `F` and a labeling
`σ : Fin N → Fin F.count` with fiber counts `n_s(N)`, the labeled product `ν_N = ⊗ᵢ ρ_{σ(i)} m`
of H1016 satisfies, with `p_s = n_s / N`, `H_s = H(ρ_s | m)` and
`R_st = ∬ R(x - y) ρ_s(x) ρ_t(y) dm dm`,

`N⁻¹ H(ν_N | P_N) = ∑ p_s H_s + (κ/2) ∑ p_s p_t R_st + (κ/(2N)) (A - ∑ p_s R_ss) + (log K_N)/N`,

and if `p_s(N) → θ_s` the right side tends to `∑ θ_s H_s + (κ/2) ∑ θ_s θ_t R_st`, which for
`κ = kappa` is the species gap `G_θ`.

Reading choices: `κ ≥ 0` is a hypothesis (for the bounds on `K_N`); `H(ν_N | P_N)` is read as an
`ℝ≥0∞`-valued `relativeEntropy`, proved `≠ ⊤`, and then taken `toReal`; the convergence is along
`atTop` in `ℕ+` for an arbitrary family of labelings `σ N`; the identification with the gap is
stated for the concrete coupling `κ = kappa` of `positiveH1`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.PositiveH1.Recovery

open DGPS DGPS.Particle DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier

/-! ### Pair marginals of a product measure -/

theorem pair_map_pi {n : ℕ} (μ : Fin n → Measure (Torus 1)) [∀ k, IsProbabilityMeasure (μ k)]
    {i j : Fin n} (hij : i ≠ j) :
    (Measure.pi μ).map (fun x : Fin n → Torus 1 => (x i, x j)) = (μ i).prod (μ j) := by
  symm
  apply Measure.prod_eq
  intro s t hs ht
  have hm : Measurable fun x : Fin n → Torus 1 => (x i, x j) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  rw [Measure.map_apply hm (hs.prod ht)]
  have hpre : (fun x : Fin n → Torus 1 => (x i, x j)) ⁻¹' (s ×ˢ t) =
      Set.pi Set.univ (fun k => if k = i then s else if k = j then t else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = i
      · subst hk; simpa using h1
      · by_cases hk' : k = j
        · subst hk'; simpa [hk] using h2
        · simp [hk, hk']
    · intro h
      refine ⟨?_, ?_⟩
      · simpa using h i
      · simpa [hij.symm] using h j
  rw [hpre, Measure.pi_pi]
  rw [Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ i)]
  rw [Finset.prod_eq_prod_sdiff_singleton_mul (s := Finset.univ \ {i})
    (by simp [hij.symm] : j ∈ Finset.univ \ {i})]
  have h1 : ∏ k ∈ (Finset.univ \ {i}) \ {j}, μ k
      (if k = i then s else if k = j then t else Set.univ) = 1 := by
    refine Finset.prod_eq_one fun k hk => ?_
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hk
    simp [hk.1, hk.2]
  rw [h1]
  simp [hij.symm, mul_comm]

theorem integral_pair_pi {n : ℕ} (μ : Fin n → Measure (Torus 1)) [∀ k, IsProbabilityMeasure (μ k)]
    {i j : Fin n} (hij : i ≠ j) {f : Torus 1 × Torus 1 → ℝ} (hf : Continuous f) :
    ∫ x, f (x i, x j) ∂Measure.pi μ = ∫ q, f q ∂((μ i).prod (μ j)) := by
  have hm : Measurable fun x : Fin n → Torus 1 => (x i, x j) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  rw [← pair_map_pi μ hij, integral_map hm.aemeasurable hf.aestronglyMeasurable]

/-! ### The potential as a double sum, and bounds on `R` -/

theorem U_eq_sum (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    U κ N x = κ / (2 * N) * ∑ i, ∑ j, R (x i - x j) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have h := hamiltonian_eq κ N x
  simp only [particleHamiltonian, kernelData, Finset.sum_const_zero, zero_add, R_zero] at h
  have e : ∑ i : Fin N, ∑ j : Fin N, κ * (R (x i - x j) - A)
      = κ * ∑ i, ∑ j, R (x i - x j) - κ * (N * N * A) := by
    simp [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
  rw [e] at h
  field_simp at h ⊢
  linarith

theorem abs_R_le (x : Torus 1) : |R x| ≤ A := by
  have := tsum_of_norm_bounded a_summable.hasSum (f := fun n => a n * cosMode n x)
    (fun n => term_abs_le n x)
  simpa [R, A, Real.norm_eq_abs] using this


/-! ### Densities, species entropies and pair integrals -/

/-- The species entropy `H_s = H(ρ_s | m)` as a real number. -/
noncomputable def entropyOf (ρ : AbsoluteDensity 1) : ℝ :=
  (relativeEntropy (densityMeasure ρ) (haar 1)).toReal

/-- `R_{ρτ} = ∬ R(x - y) ρ(x) τ(y) dm dm`. -/
noncomputable def pairInt (ρ τ : AbsoluteDensity 1) : ℝ :=
  ∫ x, ∫ y, R (x - y) * (ρ.density x * τ.density y) ∂haar 1 ∂haar 1

theorem aemeasurable_density (ρ : AbsoluteDensity 1) : AEMeasurable ρ.density (haar 1) :=
  ρ.integrable_density.aemeasurable

theorem integral_densityMeasure (ρ : AbsoluteDensity 1) (g : Torus 1 → ℝ) :
    ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)) = ∫ x, ρ.density x * g x ∂haar 1 := by
  rw [densityMeasure_coe]
  exact integral_withDensity_ofReal (aemeasurable_density ρ) ρ.density_nonneg g

theorem densityMeasure_prod (ρ τ : AbsoluteDensity 1) :
    (densityMeasure ρ : Measure (Torus 1)).prod (densityMeasure τ) =
      ((haar 1).prod (haar 1)).withDensity
        fun q => ENNReal.ofReal (ρ.density q.1 * τ.density q.2) := by
  have h := prod_withDensity₀ (μ := haar 1) (ν := haar 1)
    (aemeasurable_density ρ).ennreal_ofReal (aemeasurable_density τ).ennreal_ofReal
  rw [densityMeasure_coe, densityMeasure_coe]
  refine h.trans ?_
  congr 1
  funext q
  rw [← ENNReal.ofReal_mul (ρ.density_nonneg q.1)]

theorem aemeasurable_density_prod (ρ τ : AbsoluteDensity 1) :
    AEMeasurable (fun q : Torus 1 × Torus 1 => ρ.density q.1 * τ.density q.2)
      ((haar 1).prod (haar 1)) :=
  ((aemeasurable_density ρ).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
    ((aemeasurable_density τ).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)

theorem integral_densityMeasure_prod (ρ τ : AbsoluteDensity 1) (g : Torus 1 × Torus 1 → ℝ) :
    ∫ q, g q ∂((densityMeasure ρ : Measure (Torus 1)).prod (densityMeasure τ)) =
      ∫ q, ρ.density q.1 * τ.density q.2 * g q ∂((haar 1).prod (haar 1)) := by
  rw [densityMeasure_prod]
  exact integral_withDensity_ofReal (aemeasurable_density_prod ρ τ)
    (fun q => mul_nonneg (ρ.density_nonneg q.1) (τ.density_nonneg q.2)) g

theorem integrable_dm_prod (ρ τ : AbsoluteDensity 1) {g : Torus 1 × Torus 1 → ℝ}
    (hg : Continuous g) :
    Integrable (fun q => ρ.density q.1 * τ.density q.2 * g q) ((haar 1).prod (haar 1)) := by
  have hi : Integrable g ((densityMeasure ρ : Measure (Torus 1)).prod (densityMeasure τ)) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [densityMeasure_prod,
    integrable_withDensity_iff_integrable_smul₀' (aemeasurable_density_prod ρ τ).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hi
  refine hi.congr (Filter.Eventually.of_forall fun q => ?_)
  simp [ENNReal.toReal_ofReal (mul_nonneg (ρ.density_nonneg q.1) (τ.density_nonneg q.2))]

/-- The pair integral in measure form. -/
noncomputable def pairMeas (ρ τ : AbsoluteDensity 1) : ℝ :=
  ∫ q : Torus 1 × Torus 1, R (q.1 - q.2)
    ∂((densityMeasure ρ : Measure (Torus 1)).prod (densityMeasure τ))

theorem continuous_R_sub : Continuous fun q : Torus 1 × Torus 1 => R (q.1 - q.2) :=
  continuous_R.comp (continuous_fst.sub continuous_snd)

theorem pairMeas_eq (ρ τ : AbsoluteDensity 1) : pairMeas ρ τ = pairInt ρ τ := by
  unfold pairMeas pairInt
  rw [integral_densityMeasure_prod,
    integral_prod _ (by simpa [mul_comm, mul_assoc] using integrable_dm_prod ρ τ continuous_R_sub)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem abs_pairMeas_le (ρ τ : AbsoluteDensity 1) : |pairMeas ρ τ| ≤ A := by
  have := norm_integral_le_of_norm_le_const (μ :=
    (densityMeasure ρ : Measure (Torus 1)).prod (densityMeasure τ))
    (f := fun q : Torus 1 × Torus 1 => R (q.1 - q.2)) (C := A)
    (Filter.Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using abs_R_le (q.1 - q.2))
  simpa [pairMeas, Real.norm_eq_abs] using this

theorem abs_pairInt_le (ρ τ : AbsoluteDensity 1) : |pairInt ρ τ| ≤ A := by
  rw [← pairMeas_eq]; exact abs_pairMeas_le ρ τ


variable {N : ℕ+}

/-! ### The labeled product: amplitudes, integrals, and the potential energy -/

theorem amp_sq_eq (r : Fin N → AbsoluteDensity 1) (x : ParticleSpace 1 N) :
    amp r x ^ 2 = ∏ k, (r k).density (x k) := by
  unfold amp
  rw [← Finset.prod_pow]
  rfl

theorem integrable_amp_sq (r : Fin N → AbsoluteDensity 1) :
    Integrable (fun x => amp r x ^ 2) (particleHaar 1 N) :=
  (memLp_prod_eval (N := N) (b := fun k => (r k).sqrt) fun k => (r k).memLp_sqrt).integrable_sq

theorem aemeasurable_amp_sq (r : Fin N → AbsoluteDensity 1) :
    AEMeasurable (fun x => amp r x ^ 2) (particleHaar 1 N) :=
  (integrable_amp_sq r).aemeasurable

instance labeledProduct_isProbabilityMeasure (r : Fin N → AbsoluteDensity 1) :
    IsProbabilityMeasure (labeledProduct r) := by
  unfold labeledProduct
  infer_instance

theorem integral_labeled (r : Fin N → AbsoluteDensity 1) (g : ParticleSpace 1 N → ℝ) :
    ∫ x, g x ∂labeledProduct r = ∫ x, amp r x ^ 2 * g x ∂particleHaar 1 N := by
  rw [labeledProduct_eq]
  exact integral_withDensity_ofReal (aemeasurable_amp_sq r) (fun x => sq_nonneg _) g

theorem integrable_labeled_iff (r : Fin N → AbsoluteDensity 1) (g : ParticleSpace 1 N → ℝ) :
    Integrable g (labeledProduct r) ↔
      Integrable (fun x => amp r x ^ 2 * g x) (particleHaar 1 N) := by
  rw [labeledProduct_eq, integrable_withDensity_iff_integrable_smul₀'
    (aemeasurable_amp_sq r).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (sq_nonneg (amp r x))]

theorem integral_amp_sq (r : Fin N → AbsoluteDensity 1) :
    ∫ x, amp r x ^ 2 ∂particleHaar 1 N = 1 := by
  have h := integral_labeled r (fun _ => 1)
  simpa using h.symm

theorem integrable_U_labeled (κ : ℝ) (r : Fin N → AbsoluteDensity 1) :
    Integrable (fun x => amp r x ^ 2 * U κ N x) (particleHaar 1 N) :=
  (integrable_labeled_iff r (U κ N)).1
    ((continuous_U κ N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem amp_sq_mul_log (r : Fin N → AbsoluteDensity 1) (x : ParticleSpace 1 N) :
    amp r x ^ 2 * Real.log (amp r x ^ 2) =
      ∑ k, ∏ j, (r j).density (x j) *
        (if j = k then Real.log ((r j).density (x j)) else 1) := by
  have hprod : ∀ k, ∏ j, (r j).density (x j) *
      (if j = k then Real.log ((r j).density (x j)) else 1) =
      (∏ j, (r j).density (x j)) * Real.log ((r k).density (x k)) := by
    intro k
    rw [Finset.prod_mul_distrib]
    congr 1
    simp [Finset.prod_ite_eq']
  simp_rw [hprod, amp_sq_eq]
  by_cases h : ∏ j, (r j).density (x j) = 0
  · simp [h]
  · rw [Real.log_prod (fun j _ hj => h (Finset.prod_eq_zero (Finset.mem_univ j) hj)),
      Finset.mul_sum]

theorem integral_amp_sq_mul_log (r : Fin N → AbsoluteDensity 1) :
    Integrable (fun x => amp r x ^ 2 * Real.log (amp r x ^ 2)) (particleHaar 1 N) ∧
    ∫ x, amp r x ^ 2 * Real.log (amp r x ^ 2) ∂particleHaar 1 N = ∑ k, entropyOf (r k) := by
  have hint : ∀ k : Fin N, ∀ j : Fin N, Integrable
      (fun y => (r j).density y * (if j = k then Real.log ((r j).density y) else 1)) (haar 1) := by
    intro k j
    by_cases hj : j = k
    · simpa [hj] using (r j).integrable_density_mul_log
    · simpa [hj] using (r j).integrable_density
  have hk : ∀ k : Fin N, Integrable (fun x : ParticleSpace 1 N => ∏ j, (r j).density (x j) *
      (if j = k then Real.log ((r j).density (x j)) else 1)) (particleHaar 1 N) := fun k =>
    Integrable.fintype_prod (μ := fun _ => haar 1)
      (f := fun j y => (r j).density y * (if j = k then Real.log ((r j).density y) else 1))
      (hint k)
  have hfun : (fun x : ParticleSpace 1 N => amp r x ^ 2 * Real.log (amp r x ^ 2)) =
      fun x => ∑ k, ∏ j, (r j).density (x j) *
        (if j = k then Real.log ((r j).density (x j)) else 1) := funext (amp_sq_mul_log r)
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun k _ => hk k, ?_⟩
  rw [integral_finsetSum _ fun k _ => hk k]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold particleHaar
  rw [integral_fintype_prod_eq_prod (μ := fun _ => haar 1)
    (f := fun j y => (r j).density y * (if j = k then Real.log ((r j).density y) else 1))]
  have : ∀ j : Fin N, ∫ y, (r j).density y *
      (if j = k then Real.log ((r j).density y) else 1) ∂haar 1 =
      if j = k then entropyOf (r k) else 1 := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp only [ite_true]
      exact (absoluteDensity_entropy_finite (r j)).2.2.2.symm
    · simp [hj, (r j).integral_density]
  simp_rw [this]
  simp [Finset.prod_ite_eq']

/-! ### Exact per-particle entropy of the labeled product -/

theorem log_wfun_sq (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    Real.log (wfun κ N x ^ 2) = Real.log (K κ N) + U κ N x := by
  have hK := K_pos κ N
  have h1 : Real.exp (U κ N x / 2) ^ 2 = Real.exp (U κ N x) := by
    rw [sq, ← Real.exp_add]; ring_nf
  unfold wfun
  rw [mul_pow, Real.sq_sqrt hK.le, h1, Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp]

theorem pointwise_vlogv (κ : ℝ) (r : Fin N → AbsoluteDensity 1) (x : ParticleSpace 1 N) :
    p κ N x * (root κ r x ^ 2 * Real.log (root κ r x ^ 2)) =
      amp r x ^ 2 * Real.log (amp r x ^ 2) + amp r x ^ 2 * (Real.log (K κ N) + U κ N x) := by
  by_cases h : amp r x = 0
  · simp [root, h]
  · have hr : root κ r x ^ 2 = amp r x ^ 2 * wfun κ N x ^ 2 := by unfold root; ring
    have hw : 0 < wfun κ N x ^ 2 := by
      have := K_pos κ N
      unfold wfun
      positivity
    rw [← mul_assoc, p_mul_rootsq, hr, Real.log_mul (pow_ne_zero 2 h) hw.ne', log_wfun_sq]
    ring

theorem integrable_P_iff (κ : ℝ) (g : ParticleSpace 1 N → ℝ) :
    Integrable g (particleLaw (kernelData κ) N) ↔
      Integrable (fun x => p κ N x * g x) (particleHaar 1 N) := by
  rw [particleLaw_eq, integrable_withDensity_iff_integrable_smul₀'
    (continuous_p κ N).aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (p_nonneg κ N x)]

theorem labeled_entropy_exact (κ : ℝ) (r : Fin N → AbsoluteDensity 1) :
    relativeEntropy (labeledProduct r) (particleLaw (kernelData κ) N) ≠ ⊤ ∧
    (relativeEntropy (labeledProduct r) (particleLaw (kernelData κ) N)).toReal =
      ∑ k, entropyOf (r k) + Real.log (K κ N) + ∫ x, U κ N x ∂labeledProduct r := by
  have hac : particleLaw (kernelData κ) N ≪ particleHaar 1 N := by
    rw [particleLaw_eq]; exact withDensity_absolutelyContinuous _ _
  have hmeas : AEMeasurable (fun x => root κ r x ^ 2) (particleLaw (kernelData κ) N) :=
    ((root_aemeasurable κ r).pow_const 2).mono_ac hac
  have h1 : relativeEntropy (labeledProduct r) (particleLaw (kernelData κ) N) =
      homogeneousEntropy (particleLaw (kernelData κ) N) (fun x => root κ r x ^ 2) := by
    rw [labeledProduct_eq_withDensity κ r]
    exact relativeEntropy_withDensity (Filter.Eventually.of_forall fun x => sq_nonneg _) hmeas
  have hI1 : Integrable (fun x => root κ r x ^ 2 * Real.log (root κ r x ^ 2))
      (particleLaw (kernelData κ) N) := by
    rw [integrable_P_iff]
    simp_rw [pointwise_vlogv]
    refine (integral_amp_sq_mul_log r).1.add ?_
    simp_rw [mul_add]
    exact ((integrable_amp_sq r).mul_const _).add (integrable_U_labeled κ r)
  have hI2 : Integrable (fun x => root κ r x ^ 2) (particleLaw (kernelData κ) N) := by
    rw [integrable_P_iff]
    simp_rw [p_mul_rootsq]
    exact integrable_amp_sq r
  have hF : Integrable (fun x => root κ r x ^ 2 * Real.log (root κ r x ^ 2) - root κ r x ^ 2 + 1)
      (particleLaw (kernelData κ) N) := (hI1.sub hI2).add (integrable_const 1)
  have hnn : ∀ x, 0 ≤ root κ r x ^ 2 * Real.log (root κ r x ^ 2) - root κ r x ^ 2 + 1 := by
    intro x
    have := entropyIntegrand_nonneg one_pos (sq_nonneg (root κ r x))
    rwa [entropyIntegrand_one] at this
  have hent : homogeneousEntropy (particleLaw (kernelData κ) N) (fun x => root κ r x ^ 2) =
      ENNReal.ofReal (∫ x, (root κ r x ^ 2 * Real.log (root κ r x ^ 2) - root κ r x ^ 2 + 1)
        ∂particleLaw (kernelData κ) N) := by
    rw [entropy_mass_one (integral_rootsq κ r)]
    exact (ofReal_integral_eq_lintegral_ofReal hF (Filter.Eventually.of_forall hnn)).symm
  have hval : ∫ x, (root κ r x ^ 2 * Real.log (root κ r x ^ 2) - root κ r x ^ 2 + 1)
        ∂particleLaw (kernelData κ) N =
      ∑ k, entropyOf (r k) + Real.log (K κ N) + ∫ x, U κ N x ∂labeledProduct r := by
    rw [integral_add (f := fun x => root κ r x ^ 2 * Real.log (root κ r x ^ 2) - root κ r x ^ 2)
      (g := fun _ => (1 : ℝ)) (hI1.sub hI2) (integrable_const 1),
      integral_sub (f := fun x => root κ r x ^ 2 * Real.log (root κ r x ^ 2))
      (g := fun x => root κ r x ^ 2) hI1 hI2, integral_rootsq κ r]
    have hlog : ∫ x, root κ r x ^ 2 * Real.log (root κ r x ^ 2) ∂particleLaw (kernelData κ) N =
        ∑ k, entropyOf (r k) + Real.log (K κ N) + ∫ x, U κ N x ∂labeledProduct r := by
      rw [particleLaw_eq, integral_withDensity_ofReal (continuous_p κ N).aemeasurable
        (p_nonneg κ N)]
      simp_rw [pointwise_vlogv]
      have hsplit : ∀ x : ParticleSpace 1 N, amp r x ^ 2 * (Real.log (K κ N) + U κ N x) =
          Real.log (K κ N) * amp r x ^ 2 + amp r x ^ 2 * U κ N x := fun x => by ring
      simp_rw [hsplit]
      have hc : Integrable (fun x => Real.log (K κ N) * amp r x ^ 2) (particleHaar 1 N) :=
        (integrable_amp_sq r).const_mul _
      have hcU : Integrable (fun x => Real.log (K κ N) * amp r x ^ 2 + amp r x ^ 2 * U κ N x)
          (particleHaar 1 N) := hc.add (integrable_U_labeled κ r)
      rw [integral_add (integral_amp_sq_mul_log r).1 hcU,
        integral_add hc (integrable_U_labeled κ r),
        integral_const_mul, integral_amp_sq, (integral_amp_sq_mul_log r).2,
        ← integral_labeled r (U κ N)]
      ring
    rw [hlog]
    simp
  refine ⟨?_, ?_⟩
  · rw [h1, hent]; exact ENNReal.ofReal_ne_top
  · rw [h1, hent, ENNReal.toReal_ofReal (integral_nonneg hnn), hval]

/-! ### The mean interaction energy of the labeled product -/

theorem integral_U_labeled (κ : ℝ) (r : Fin N → AbsoluteDensity 1) :
    ∫ x, U κ N x ∂labeledProduct r =
      κ / (2 * N) * ∑ i, ∑ j, (if i = j then A else pairMeas (r i) (r j)) := by
  simp_rw [U_eq_sum]
  rw [integral_const_mul]
  congr 1
  have hint : ∀ i j : Fin N, Integrable (fun x : ParticleSpace 1 N => R (x i - x j))
      (labeledProduct r) := fun i j =>
    (continuous_R.comp ((continuous_apply i).sub (continuous_apply j))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst hij
    simp [R_zero]
  · simp only [hij, ↓reduceIte]
    have h := integral_pair_pi (fun k => (densityMeasure (r k) : Measure (Torus 1))) hij
      (f := fun q : Torus 1 × Torus 1 => R (q.1 - q.2)) continuous_R_sub
    exact h

/-! ### Fiber sums over a labeling -/

/-- The number `n_s` of indices carrying label `s`. -/
noncomputable def cnt {n : ℕ} (σ : Fin N → Fin n) (s : Fin n) : ℝ :=
  ((Finset.univ.filter fun i => σ i = s).card : ℝ)

/-- The fraction `p_s = n_s / N` of indices carrying label `s`. -/
noncomputable def frac {n : ℕ} (σ : Fin N → Fin n) (s : Fin n) : ℝ := cnt σ s / N

theorem sum_fiber {n : ℕ} (σ : Fin N → Fin n) (g : Fin n → ℝ) :
    ∑ i, g (σ i) = ∑ s, cnt σ s * g s := by
  rw [← Finset.sum_fiberwise Finset.univ σ (fun i => g (σ i))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2] :
    ∀ i ∈ Finset.univ.filter (fun i => σ i = s), g (σ i) = g s)]
  simp [cnt]

theorem sum_fiber2 {n : ℕ} (σ : Fin N → Fin n) (g : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, g (σ i) (σ j) = ∑ s, ∑ t, cnt σ s * cnt σ t * g s t := by
  calc ∑ i, ∑ j, g (σ i) (σ j) = ∑ i, ∑ t, cnt σ t * g (σ i) t :=
        Finset.sum_congr rfl fun i _ => sum_fiber σ (g (σ i))
    _ = ∑ t, ∑ i, cnt σ t * g (σ i) t := Finset.sum_comm
    _ = ∑ t, cnt σ t * ∑ s, cnt σ s * g s t := Finset.sum_congr rfl fun t _ => by
        rw [← Finset.mul_sum, sum_fiber σ (fun s => g s t)]
    _ = ∑ s, ∑ t, cnt σ s * cnt σ t * g s t := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring

/-! ### The exact finite-`N` identity -/

theorem finite_exact_identity (κ : ℝ) (F : SpeciesFamily 1) (σ : Fin N → Fin F.count) :
    relativeEntropy (labeledProduct fun i => F.density (σ i)) (particleLaw (kernelData κ) N) ≠ ⊤ ∧
    (relativeEntropy (labeledProduct fun i => F.density (σ i))
        (particleLaw (kernelData κ) N)).toReal / N =
      ∑ s, frac σ s * entropyOf (F.density s)
      + κ / 2 * ∑ s, ∑ t, frac σ s * frac σ t * pairInt (F.density s) (F.density t)
      + κ / (2 * N) * (A - ∑ s, frac σ s * pairInt (F.density s) (F.density s))
      + Real.log (K κ N) / N := by
  obtain ⟨hne, hval⟩ := labeled_entropy_exact κ (fun i => F.density (σ i))
  refine ⟨hne, ?_⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  rw [hval, integral_U_labeled]
  have hsplit : ∀ i j : Fin N, (if i = j then A else pairMeas (F.density (σ i)) (F.density (σ j))) =
      pairMeas (F.density (σ i)) (F.density (σ j)) +
        (if i = j then A - pairMeas (F.density (σ i)) (F.density (σ i)) else 0) := by
    intro i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [sum_fiber2 σ (fun s t => pairMeas (F.density s) (F.density t)),
    Finset.sum_sub_distrib, sum_fiber σ (fun s => pairMeas (F.density s) (F.density s)),
    sum_fiber σ (fun s => entropyOf (F.density s))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pairMeas_eq]
  have e1 : ∑ s, frac σ s * entropyOf (F.density s) =
      (∑ s, cnt σ s * entropyOf (F.density s)) / N := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by unfold frac; ring
  have e2 : ∑ s, ∑ t, frac σ s * frac σ t * pairInt (F.density s) (F.density t) =
      (∑ s, ∑ t, cnt σ s * cnt σ t * pairInt (F.density s) (F.density t)) / (N : ℝ) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by unfold frac; field_simp
  have e3 : ∑ s, frac σ s * pairInt (F.density s) (F.density s) =
      (∑ s, cnt σ s * pairInt (F.density s) (F.density s)) / N := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by unfold frac; ring
  rw [e1, e2, e3]
  field_simp
  ring

/-! ### Bounds on the normalizer and the barycenter pair integral -/

theorem abs_log_K_le {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ+) : |Real.log (K κ N)| ≤ κ * A / 2 := by
  have h1 : Real.log (K κ N) ≤ 0 := Real.log_nonpos (K_pos κ N).le (K_le_one hκ N)
  have h2 : -(κ * A / 2) ≤ Real.log (K κ N) :=
    (Real.le_log_iff_exp_le (K_pos κ N)).2 (exp_le_K κ N)
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem pairMeas_eq_prod (ρ τ : AbsoluteDensity 1) :
    pairMeas ρ τ =
      ∫ q, ρ.density q.1 * τ.density q.2 * R (q.1 - q.2) ∂((haar 1).prod (haar 1)) :=
  integral_densityMeasure_prod ρ τ _

theorem pairMeas_barycenter (F : SpeciesFamily 1) :
    pairMeas (barycenter F) (barycenter F) =
      ∑ s, ∑ t, F.weight s * F.weight t * pairMeas (F.density s) (F.density t) := by
  simp only [pairMeas_eq_prod]
  have hd : ∀ x, (barycenter F).density x = ∑ s, F.weight s * (F.density s).density x :=
    fun x => by rw [SpeciesFamily.barycenter_density_apply]; rfl
  have hq : ∀ q : Torus 1 × Torus 1, (barycenter F).density q.1 * (barycenter F).density q.2 *
      R (q.1 - q.2) = ∑ s, ∑ t, F.weight s * F.weight t *
        ((F.density s).density q.1 * (F.density t).density q.2 * R (q.1 - q.2)) := by
    intro q
    rw [hd, hd, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  simp_rw [hq]
  have hint : ∀ s t, Integrable (fun q : Torus 1 × Torus 1 => F.weight s * F.weight t *
      ((F.density s).density q.1 * (F.density t).density q.2 * R (q.1 - q.2)))
      ((haar 1).prod (haar 1)) := fun s t =>
    (integrable_dm_prod (F.density s) (F.density t) continuous_R_sub).const_mul _
  rw [integral_finsetSum _ fun s _ => integrable_finsetSum _ fun t _ => hint s t]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finsetSum _ fun t _ => hint s t]
  exact Finset.sum_congr rfl fun t _ => integral_const_mul _ _

theorem gap_eq_limit (F : SpeciesFamily 1) :
    (speciesGap DGPS.Examples.PositiveH1.Model.positiveH1 F : ℝ) =
      ∑ s, F.weight s * entropyOf (F.density s)
      + DGPS.Examples.PositiveH1.Model.kappa / 2 *
        ∑ s, ∑ t, F.weight s * F.weight t * pairInt (F.density s) (F.density t) := by
  rw [DGPS.Examples.PositiveH1.Nonlinear.h1011_gap_species]
  congr 2
  have h1 : DGPS.Examples.PositiveH1.CrossTerm.P (barycenter F) =
      pairMeas (barycenter F) (barycenter F) := by
    rw [← DGPS.Examples.PositiveH1.Nonlinear.h1011_fourierEnergy,
      DGPS.Examples.PositiveH1.Nonlinear.fourierEnergy,
      ← DGPS.Examples.PositiveH1.Nonlinear.integral_R_sub]
    rfl
  rw [h1, pairMeas_barycenter]
  simp only [pairMeas_eq]

/-! ### Convergence -/

theorem tendsto_exact_limit {κ : ℝ} (hκ : 0 ≤ κ) (F : SpeciesFamily 1)
    (σ : ∀ N : ℕ+, Fin N → Fin F.count)
    (hσ : ∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop (𝓝 (F.weight s))) :
    Tendsto (fun N : ℕ+ =>
        (relativeEntropy (labeledProduct fun i => F.density (σ N i))
          (particleLaw (kernelData κ) N)).toReal / N) atTop
      (𝓝 (∑ s, F.weight s * entropyOf (F.density s)
        + κ / 2 * ∑ s, ∑ t, F.weight s * F.weight t * pairInt (F.density s) (F.density t))) := by
  have hN : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop
  have hinv : Tendsto (fun N : ℕ+ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have hT1 : Tendsto (fun N : ℕ+ => ∑ s, frac (σ N) s * entropyOf (F.density s)) atTop
      (𝓝 (∑ s, F.weight s * entropyOf (F.density s))) :=
    tendsto_finsetSum _ fun s _ => (hσ s).mul_const _
  have hT2 : Tendsto (fun N : ℕ+ => κ / 2 * ∑ s, ∑ t,
      frac (σ N) s * frac (σ N) t * pairInt (F.density s) (F.density t)) atTop
      (𝓝 (κ / 2 * ∑ s, ∑ t, F.weight s * F.weight t * pairInt (F.density s) (F.density t))) :=
    (tendsto_finsetSum _ fun s _ => tendsto_finsetSum _ fun t _ =>
      ((hσ s).mul (hσ t)).mul_const _).const_mul _
  have hc : Tendsto (fun N : ℕ+ => κ / (2 * (N : ℝ))) atTop (𝓝 0) := by
    have := hinv.const_mul (κ / 2)
    rw [mul_zero] at this
    refine this.congr fun N => ?_
    have : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
    field_simp
  have hT3 : Tendsto (fun N : ℕ+ => κ / (2 * (N : ℝ)) *
      (A - ∑ s, frac (σ N) s * pairInt (F.density s) (F.density s))) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ+ => A - ∑ s, frac (σ N) s * pairInt (F.density s) (F.density s))
        atTop (𝓝 (A - ∑ s, F.weight s * pairInt (F.density s) (F.density s))) :=
      tendsto_const_nhds.sub (tendsto_finsetSum _ fun s _ => (hσ s).mul_const _)
    simpa using hc.mul hb
  have hT4 : Tendsto (fun N : ℕ+ => Real.log (K κ N) / N) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (by simpa using hinv.const_mul (κ * A / 2))
    have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hN0]
    calc |Real.log (K κ N)| / N ≤ (κ * A / 2) / N :=
          div_le_div_of_nonneg_right (abs_log_K_le hκ N) hN0.le
      _ = κ * A / 2 * ((N : ℕ) : ℝ)⁻¹ := by ring
  have hsum := ((hT1.add hT2).add hT3).add hT4
  rw [add_zero, add_zero] at hsum
  refine hsum.congr fun N => ?_
  exact ((finite_exact_identity κ F (σ N)).2).symm

/-! ### The theorem -/

/-- **Finite family exact entropy recovery.** -/
theorem finite_family_exact_entropy_recovery {κ : ℝ} (hκ : 0 ≤ κ) (F : SpeciesFamily 1) :
    (∀ (N : ℕ+) (σ : Fin N → Fin F.count),
      relativeEntropy (labeledProduct fun i => F.density (σ i))
        (particleLaw (kernelData κ) N) ≠ ⊤ ∧
      (relativeEntropy (labeledProduct fun i => F.density (σ i))
          (particleLaw (kernelData κ) N)).toReal / N =
        ∑ s, frac σ s * entropyOf (F.density s)
        + κ / 2 * ∑ s, ∑ t, frac σ s * frac σ t * pairInt (F.density s) (F.density t)
        + κ / (2 * N) * (A - ∑ s, frac σ s * pairInt (F.density s) (F.density s))
        + Real.log (K κ N) / N) ∧
    (∀ σ : ∀ N : ℕ+, Fin N → Fin F.count,
      (∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop (𝓝 (F.weight s))) →
      Tendsto (fun N : ℕ+ =>
          (relativeEntropy (labeledProduct fun i => F.density (σ N i))
            (particleLaw (kernelData κ) N)).toReal / N) atTop
        (𝓝 (∑ s, F.weight s * entropyOf (F.density s)
          + κ / 2 * ∑ s, ∑ t, F.weight s * F.weight t *
            pairInt (F.density s) (F.density t)))) ∧
    (κ = DGPS.Examples.PositiveH1.Model.kappa →
      ∑ s, F.weight s * entropyOf (F.density s)
          + κ / 2 * ∑ s, ∑ t, F.weight s * F.weight t * pairInt (F.density s) (F.density t) =
        (speciesGap DGPS.Examples.PositiveH1.Model.positiveH1 F : ℝ)) :=
  ⟨fun N σ => finite_exact_identity κ F σ, fun σ hσ => tendsto_exact_limit hκ F σ hσ,
    fun h => by rw [h]; exact (gap_eq_limit F).symm⟩

end DGPS.Examples.PositiveH1.Recovery
