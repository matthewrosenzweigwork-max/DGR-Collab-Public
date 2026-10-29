import Mathlib
import DGPS.Examples.PositiveH1.TransferCommonTail
import DGPS.Examples.PositiveH1.TransferRough
import DGPS.Examples.PositiveH1.TransferInverse
import DGPS.Examples.PositiveH1.Model
import DGPS.Foundations.SobolevEmbedding
import DGPS.Foundations.Entropy
import DGPS.Particle.Rates

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS
open DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier
open DGPS.Examples.PositiveH1.Model

/-!
# H1035: full-domain entropy change of density

For `h_{N,M} = √(p_N / p_{N,M})`, `g = f h_{N,M}` and `f ∈ H¹(P_N)` (at `κ = 1/100`), we show
`g ∈ H¹(P_{N,M})`, `∫ g² dP_{N,M} = ∫ f² dP_N`, and
`Ent_{P_N}(f²) = Ent_{P_{N,M}}(g²) + ∫ f² T_{N,M} dP_N + log(K_N/K_{N,M}) ∫ f² dP_N`,
with `log(K_N/K_{N,M}) ≤ 0`.  Main result: `full_domain_entropy_change_of_density`.
-/

namespace DGPS.Examples.PositiveH1.Transfer

/-- `A_M = R_M(0) = Σ_{2 ≤ n ≤ M} a_n`. -/
noncomputable def AM (M : ℕ) : ℝ := ∑ n ∈ Finset.Icc 2 M, a n

theorem RM_zero (M : ℕ) : RM M 0 = AM M := by
  unfold RM AM
  exact Finset.sum_congr rfl fun n _ => by rw [cosMode_zero, mul_one]

/-- The cutoff normalizer `K_{N,M} = ∫ e^{-U_{N,M}} dm^N`. -/
noncomputable def KM (N : ℕ+) (M : ℕ) : ℝ :=
  ∫ x, Real.exp (-UM (1 / 100) N M x) ∂particleHaar 1 N

theorem cutoff_hamiltonian (M : ℕ) (N : ℕ+) (x : ParticleSpace 1 N) :
    particleHamiltonian (positiveH1Cutoff M) N x = UM (1 / 100) N M x - (1 / 100) * N * AM M / 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have h1 : ∑ i, ∑ j, RM M (x i - x j) = N * ∑ n ∈ Finset.Icc 2 M, a n * ‖Z N n x‖ ^ 2 := by
    unfold RM
    have e1 : ∀ i, ∑ j, ∑ n ∈ Finset.Icc 2 M, a n * cosMode n (x i - x j) =
        ∑ n ∈ Finset.Icc 2 M, ∑ j, a n * cosMode n (x i - x j) := fun i => Finset.sum_comm
    simp_rw [e1]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp_rw [← Finset.mul_sum]
    rw [← normSq_S_cos, norm_Z_sq]
    field_simp
  simp only [particleHamiltonian, positiveH1Cutoff, Finset.sum_const_zero, zero_add]
  rw [show kappa = 1 / 100 from rfl]
  simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, h1, RM_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold UM
  field_simp

theorem continuous_UM (N : ℕ+) (M : ℕ) : Continuous (UM (1 / 100) N M) := by
  have h : UM (1 / 100) N M = fun x => particleHamiltonian (positiveH1Cutoff M) N x +
      (1 / 100) * N * AM M / 2 := by
    funext x; rw [cutoff_hamiltonian]; ring
  rw [h]
  exact (DGPS.Particle.particleHamiltonian_continuous (positiveH1Cutoff M) N).add continuous_const

theorem cutoff_partition (N : ℕ+) (M : ℕ) :
    particlePartition (positiveH1Cutoff M) N = Real.exp ((1 / 100) * N * AM M / 2) * KM N M := by
  unfold particlePartition KM
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [cutoff_hamiltonian]
  rw [← Real.exp_add]; congr 1; ring

theorem KM_pos (N : ℕ+) (M : ℕ) : 0 < KM N M := by
  have h := cutoff_partition N M
  have h2 := DGPS.Particle.particlePartition_pos (positiveH1Cutoff M) N
  rw [h] at h2
  exact pos_of_mul_pos_right h2 (Real.exp_pos _).le

theorem cutoff_density (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    particleDensity (positiveH1Cutoff M) N x = (KM N M)⁻¹ * Real.exp (-UM (1 / 100) N M x) := by
  unfold particleDensity
  have := (Real.exp_pos ((1 / 100) * N * AM M / 2)).ne'
  have h2 : Real.exp (-(UM (1 / 100) N M x - (1 / 100) * N * AM M / 2)) =
      Real.exp (-UM (1 / 100) N M x) * Real.exp ((1 / 100) * N * AM M / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [cutoff_partition, cutoff_hamiltonian, mul_inv, h2]
  have := (KM_pos N M).ne'
  field_simp

theorem K_le_KM (N : ℕ+) (M : ℕ) : K (1 / 100) N ≤ KM N M := by
  unfold K KM
  have hc : Continuous fun x => Real.exp (-UM (1 / 100) N M x) :=
    Real.continuous_exp.comp (continuous_UM N M).neg
  refine integral_mono (integrable_exp_neg_U _ N)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) fun x => ?_
  refine Real.exp_le_exp.2 ?_
  have := U_sub_UM (1 / 100) N M x
  have := tailT_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100) N M x
  linarith

/-- The potential `U_{N,M}` as a function on `𝕋^N`. -/
noncomputable def PhiM (N : ℕ+) (M : ℕ) (y : Torus (N : ℕ)) : ℝ :=
  (1 / 100) / 2 * ∑ n ∈ Finset.Icc 2 M, a n * ((Rr n y ^ 2 + Ii n y ^ 2) / N)

theorem UM_eq_PhiM (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    UM (1 / 100) N M x = PhiM N M (EE N x) := by
  unfold UM PhiM
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [norm_Z_sq, normSq_S_eq]

theorem isSmooth_PhiM (N : ℕ+) (M : ℕ) : IsSmoothPeriodic (PhiM N M) := by
  unfold PhiM
  refine isSmooth_const_mul (isSmoothPeriodic_sum _ fun n _ => isSmooth_const_mul ?_ _) _
  have h1 := (isSmooth_Rr (M := (N : ℕ)) n).mul (isSmooth_Rr (M := (N : ℕ)) n)
  have h2 := (isSmooth_Ii (M := (N : ℕ)) n).mul (isSmooth_Ii (M := (N : ℕ)) n)
  have h3 := isSmooth_const_mul (isSmooth_add h1 h2) ((N : ℝ)⁻¹)
  have e : (fun y : Torus (N : ℕ) => (Rr n y ^ 2 + Ii n y ^ 2) / N) =
      fun y => (N : ℝ)⁻¹ * (Rr n y * Rr n y + Ii n y * Ii n y) := by
    funext y; ring
  rw [e]
  exact h3

/-- The reciprocal square root `p_{N,M}^{-1/2} = √K_{N,M} e^{U_{N,M}/2}` on `𝕋^N`. -/
noncomputable def wtM (N : ℕ+) (M : ℕ) (y : Torus (N : ℕ)) : ℝ :=
  Real.sqrt (KM N M) * Real.exp (PhiM N M y / 2)

theorem isSmooth_wtM (N : ℕ+) (M : ℕ) : IsSmoothPeriodic (wtM N M) := by
  unfold wtM
  refine isSmooth_const_mul ?_ _
  have h := (isSmooth_PhiM N M).div_const 2
  show ContDiff ℝ ∞ (fun s => Real.exp (PhiM N M (torusLift s) / 2))
  exact Real.contDiff_exp.comp h

theorem sqrt_pM_inv (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    (Real.sqrt (particleDensity (positiveH1Cutoff M) N x))⁻¹ = wtM N M (EE N x) := by
  have hK : 0 ≤ (KM N M)⁻¹ := (inv_pos.2 (KM_pos N M)).le
  have h2 : Real.exp (-UM (1 / 100) N M x) = Real.exp (-UM (1 / 100) N M x / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Real.sqrt (particleDensity (positiveH1Cutoff M) N x) =
      (Real.sqrt (KM N M))⁻¹ * Real.exp (-UM (1 / 100) N M x / 2) := by
    rw [cutoff_density, Real.sqrt_mul hK, Real.sqrt_inv, h2, Real.sqrt_sq (Real.exp_pos _).le]
  rw [h3, mul_inv, inv_inv, ← Real.exp_neg]
  unfold wtM
  rw [← UM_eq_PhiM]
  congr 2
  ring

theorem haarH1_mul_wtM {N : ℕ+} (M : ℕ) {ψ : ParticleSpace 1 N → ℝ}
    {g : ParticleSpace 1 N → Fin N → Tangent 1} (hψ : IsParticleHaarWeakGradient N ψ g) :
    MemParticleHaarH1 N (fun x => ψ x * (Real.sqrt (particleDensity (positiveH1Cutoff M) N x))⁻¹) := by
  have h := mul_smooth_H1 (isSmooth_wtM N M) (transport_weak N hψ)
  have hP := transport_weak_symm N h
  have key : (fun x => ψ x * (Real.sqrt (particleDensity (positiveH1Cutoff M) N x))⁻¹) =
      fun x => wtM N M (EE N x) * ψ ((EE N).symm (EE N x)) := by
    funext x
    rw [sqrt_pM_inv, MeasurableEquiv.symm_apply_apply, mul_comm]
  rw [key]
  exact ⟨_, hP⟩

theorem integrable_sq_mul_log_sq_haar {N : ℕ+} {u : ParticleSpace 1 N → ℝ}
    (hu : MemParticleHaarH1 N u) :
    Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) (particleHaar 1 N) := by
  obtain ⟨g, hg⟩ := hu
  have h := integrable_sq_mul_log_sq_of_memH1 (N : ℕ) (⟨_, transport_weak N hg⟩ : MemH1 _)
  have h2 := ((mp_EE N).integrable_comp_emb (EE N).measurableEmbedding).2 h
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp

theorem integrable_law_iff {d : ℕ} (A : InteractionData d) (N : ℕ+) {h : ParticleSpace d N → ℝ} :
    Integrable h (particleLaw A N) ↔ Integrable h (particleHaar d N) := by
  rw [← memLp_one_iff_integrable, ← memLp_one_iff_integrable]
  exact DGPS.Particle.memLp_particleLaw_iff A N

/-- Entropy of a nonnegative integrable `v` with integrable `v log v` w.r.t. a probability
measure: finite, with real value `∫ v log v - a log a`. -/
theorem homogeneousEntropy_toReal {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {v : α → ℝ} (hv : ∀ x, 0 ≤ v x) (hint : Integrable v P)
    (hlog : Integrable (fun x => v x * Real.log (v x)) P) :
    homogeneousEntropy P v ≠ ⊤ ∧ (homogeneousEntropy P v).toReal =
      ∫ x, v x * Real.log (v x) ∂P - (∫ x, v x ∂P) * Real.log (∫ x, v x ∂P) := by
  have hv' : 0 ≤ᵐ[P] v := Filter.Eventually.of_forall hv
  have hform := homogeneousEntropy_eq_formula hv' hint hlog
  set a := ∫ x, v x ∂P with ha
  have ha0 : 0 ≤ a := integral_nonneg hv
  have hX : 0 ≤ ∫ x, v x * Real.log (v x) ∂P - a * Real.log a := by
    rcases ha0.eq_or_lt with h0 | h0
    · have hz : v =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hv' hint).mp h0.symm
      have h1 : ∫ x, v x * Real.log (v x) ∂P = 0 := by
        rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
        · simp
        · filter_upwards [hz] with x hx; simp [hx]
      rw [← h0, h1]; simp
    · have hpt : ∀ x, 0 ≤ v x * Real.log (v x) - v x * Real.log a + a - v x := by
        intro x
        have := entropyIntegrand_nonneg h0 (hv x)
        unfold entropyIntegrand at this
        rcases eq_or_ne (v x) 0 with h | h
        · rw [h]; simp [h0.le]
        · rw [Real.log_div h h0.ne'] at this; linarith
      have i1 : Integrable (fun x => v x * Real.log a) P := hint.mul_const _
      have i2 : Integrable (fun x => v x * Real.log (v x) - v x * Real.log a) P := hlog.sub i1
      have i3 : Integrable (fun x => v x * Real.log (v x) - v x * Real.log a + a) P :=
        i2.add (integrable_const a)
      have hI : 0 ≤ ∫ x, (v x * Real.log (v x) - v x * Real.log a + a - v x) ∂P :=
        integral_nonneg fun x => hpt x
      rw [integral_sub i3 hint, integral_add i2 (integrable_const a), integral_sub hlog i1,
        integral_mul_const, integral_const, ← ha] at hI
      simp at hI
      linarith
  rw [hform]
  exact ⟨ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hX⟩

/-- The density ratio `h_{N,M} = √(p_N / p_{N,M})`. -/
noncomputable def hNM (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) : ℝ :=
  Real.sqrt (particleDensity (kernelData (1 / 100)) N x /
    particleDensity (positiveH1Cutoff M) N x)

theorem hNM_sq (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    hNM N M x ^ 2 = particleDensity (kernelData (1 / 100)) N x /
      particleDensity (positiveH1Cutoff M) N x := by
  unfold hNM
  exact Real.sq_sqrt (div_nonneg (DGPS.Particle.particleDensity_pos _ N x).le (DGPS.Particle.particleDensity_pos _ N x).le)

theorem hNM_eq (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    hNM N M x = Real.sqrt (p (1 / 100) N x) *
      (Real.sqrt (particleDensity (positiveH1Cutoff M) N x))⁻¹ := by
  unfold hNM
  rw [Real.sqrt_div (DGPS.Particle.particleDensity_pos _ N x).le, density_eq, div_eq_mul_inv]

theorem ratio_eq (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    particleDensity (kernelData (1 / 100)) N x / particleDensity (positiveH1Cutoff M) N x =
      KM N M / K (1 / 100) N * Real.exp (-tailT (1 / 100) N M x) := by
  have hK := K_pos (1 / 100 : ℝ) N
  have hKM := KM_pos N M
  have hU : U (1 / 100) N x = UM (1 / 100) N M x + tailT (1 / 100) N M x := by
    have := U_sub_UM (1 / 100) N M x; linarith
  rw [density_eq, cutoff_density]
  unfold p
  rw [hU, neg_add, Real.exp_add]
  field_simp

theorem haarH1_of_mul {N : ℕ+} {M : ℕ} (f : ParticleH1 (kernelData (1 / 100)) N) :
    MemParticleHaarH1 N (fun x => f x * hNM N M x) := by
  obtain ⟨gf, hgf⟩ := f.2
  have hψ := (ground_state_map_on_every_rough_particle_test N f.1 f.2 gf hgf).2.1
  have h := haarH1_mul_wtM M hψ
  have hfun : (fun x => f x * hNM N M x) = fun x => f x * Real.sqrt (p (1 / 100) N x) *
      (Real.sqrt (particleDensity (positiveH1Cutoff M) N x))⁻¹ := by
    funext x; rw [hNM_eq]; ring
  rw [hfun]; exact h

theorem mass_pointwise (N : ℕ+) (M : ℕ) (f : ParticleH1 (kernelData (1 / 100)) N)
    (x : ParticleSpace 1 N) :
    particleDensity (positiveH1Cutoff M) N x * (f x * hNM N M x) ^ 2 =
      particleDensity (kernelData (1 / 100)) N x * f x ^ 2 := by
  have h := DGPS.Particle.particleDensity_pos (positiveH1Cutoff M) N x
  rw [mul_pow, hNM_sq]
  field_simp

theorem log_pointwise (N : ℕ+) (M : ℕ) (f : ParticleH1 (kernelData (1 / 100)) N)
    (x : ParticleSpace 1 N) :
    particleDensity (positiveH1Cutoff M) N x *
        ((f x * hNM N M x) ^ 2 * Real.log ((f x * hNM N M x) ^ 2)) =
      particleDensity (kernelData (1 / 100)) N x *
        (f x ^ 2 * Real.log (f x ^ 2) +
          (Real.log (KM N M) - Real.log (K (1 / 100) N)) * f x ^ 2 -
          f x ^ 2 * tailT (1 / 100) N M x) := by
  have hK := K_pos (1 / 100 : ℝ) N
  have hKM := KM_pos N M
  have hd := DGPS.Particle.particleDensity_pos (positiveH1Cutoff M) N x
  rcases eq_or_ne (f x) 0 with h | h
  · simp [h]
  · have hr : hNM N M x ^ 2 = KM N M / K (1 / 100) N * Real.exp (-tailT (1 / 100) N M x) := by
      rw [hNM_sq, ratio_eq]
    have hrpos : 0 < hNM N M x ^ 2 := by rw [hr]; positivity
    have hlog : Real.log ((f x * hNM N M x) ^ 2) =
        Real.log (f x ^ 2) + (Real.log (KM N M) - Real.log (K (1 / 100) N) - tailT (1 / 100) N M x) := by
      rw [mul_pow, Real.log_mul (pow_ne_zero 2 h) hrpos.ne', hr,
        Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_div hKM.ne' hK.ne',
        Real.log_exp]
      ring
    rw [hlog, ← mul_assoc, mass_pointwise N M f x]
    ring

theorem full_domain_entropy_change_of_density (N : ℕ+) (M : ℕ)
    (f : ParticleH1 (kernelData (1 / 100)) N) :
    ∃ hg : MemParticleH1 (positiveH1Cutoff M) N (fun x => f x * hNM N M x),
      (∫ x, (f x * hNM N M x) ^ 2 ∂particleLaw (positiveH1Cutoff M) N =
        ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N) ∧
      particleEntropy (kernelData (1 / 100)) N f ≠ ⊤ ∧
      particleEntropy (positiveH1Cutoff M) N ⟨_, hg⟩ ≠ ⊤ ∧
      (particleEntropy (kernelData (1 / 100)) N f).toReal =
        (particleEntropy (positiveH1Cutoff M) N ⟨_, hg⟩).toReal +
          ∫ x, f x ^ 2 * tailT (1 / 100) N M x ∂particleLaw (kernelData (1 / 100)) N +
          Real.log (K (1 / 100) N / KM N M) *
            ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N ∧
      Real.log (K (1 / 100) N / KM N M) ≤ 0 := by
  have hK := K_pos (1 / 100 : ℝ) N
  have hKM := KM_pos N M
  have hgH := haarH1_of_mul (M := M) f
  have hg : MemParticleH1 (positiveH1Cutoff M) N (fun x => f x * hNM N M x) :=
    (memParticleH1_iff _ N _).2 hgH
  have hfH : MemParticleHaarH1 N f := (memParticleH1_iff _ N _).1 f.2
  refine ⟨hg, ?_⟩
  set P := particleLaw (kernelData (1 / 100)) N with hP
  set Q := particleLaw (positiveH1Cutoff M) N with hQ
  set g : ParticleSpace 1 N → ℝ := fun x => f x * hNM N M x with hgdef
  -- integrability
  have hf2 : Integrable (fun x => f x ^ 2) P := by
    obtain ⟨gf, hgf⟩ := f.2
    exact hgf.memLp.integrable_sq
  have hg2 : Integrable (fun x => g x ^ 2) Q := by
    obtain ⟨gg, hgg⟩ := hg
    exact hgg.memLp.integrable_sq
  have hfl : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) P :=
    (integrable_law_iff _ N).2 (integrable_sq_mul_log_sq_haar hfH)
  have hgl : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) Q :=
    (integrable_law_iff _ N).2 (integrable_sq_mul_log_sq_haar hgH)
  have hT : Continuous (tailT (1 / 100) N M) := by
    have : tailT (1 / 100) N M = fun x => U (1 / 100) N x - UM (1 / 100) N M x := by
      funext x; rw [U_sub_UM]
    rw [this]; exact (continuous_U _ N).sub (continuous_UM N M)
  have hfT : Integrable (fun x => f x ^ 2 * tailT (1 / 100) N M x) P := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hT.continuousOn
    exact hf2.mul_bdd hT.aestronglyMeasurable (c := C)
      (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ _))
  -- mass
  have hmass : ∫ x, g x ^ 2 ∂Q = ∫ x, f x ^ 2 ∂P := by
    rw [hQ, hP, DGPS.Particle.integral_particleLaw, DGPS.Particle.integral_particleLaw]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mass_pointwise N M f x)
  -- entropy integral
  have hent : ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂Q =
      ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂P +
        (Real.log (KM N M) - Real.log (K (1 / 100) N)) * ∫ x, f x ^ 2 ∂P -
        ∫ x, f x ^ 2 * tailT (1 / 100) N M x ∂P := by
    rw [hQ, DGPS.Particle.integral_particleLaw]
    have : ∀ x, DGPS.particleDensity (positiveH1Cutoff M) N x *
        (g x ^ 2 * Real.log (g x ^ 2)) = DGPS.particleDensity (kernelData (1 / 100)) N x *
        (f x ^ 2 * Real.log (f x ^ 2) +
          (Real.log (KM N M) - Real.log (K (1 / 100) N)) * f x ^ 2 -
          f x ^ 2 * tailT (1 / 100) N M x) := fun x => log_pointwise N M f x
    simp_rw [this]
    rw [← DGPS.Particle.integral_particleLaw (kernelData (1 / 100)) N
      (fun x => f x ^ 2 * Real.log (f x ^ 2) +
          (Real.log (KM N M) - Real.log (K (1 / 100) N)) * f x ^ 2 -
          f x ^ 2 * tailT (1 / 100) N M x)]
    have hc : Integrable (fun x => (Real.log (KM N M) - Real.log (K (1 / 100) N)) * f x ^ 2) P :=
      hf2.const_mul _
    have hs : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2) +
        (Real.log (KM N M) - Real.log (K (1 / 100) N)) * f x ^ 2) P := hfl.add hc
    rw [integral_sub hs hfT, integral_add hfl hc, integral_const_mul]
  -- entropies
  obtain ⟨hfin1, hval1⟩ := homogeneousEntropy_toReal (P := P) (v := fun x => f x ^ 2)
    (fun x => sq_nonneg _) hf2 hfl
  obtain ⟨hfin2, hval2⟩ := homogeneousEntropy_toReal (P := Q) (v := fun x => g x ^ 2)
    (fun x => sq_nonneg _) hg2 hgl
  refine ⟨hmass, hfin1, hfin2, ?_, ?_⟩
  · have e1 : (particleEntropy (kernelData (1 / 100)) N f).toReal =
        ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂P -
          (∫ x, f x ^ 2 ∂P) * Real.log (∫ x, f x ^ 2 ∂P) := hval1
    have e2 : (particleEntropy (positiveH1Cutoff M) N ⟨_, hg⟩).toReal =
        ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂Q -
          (∫ x, g x ^ 2 ∂Q) * Real.log (∫ x, g x ^ 2 ∂Q) := hval2
    rw [e1, e2, hent, hmass, Real.log_div hK.ne' hKM.ne']
    ring
  · rw [Real.log_nonpos_iff (div_pos hK hKM).le]
    exact (div_le_one hKM).2 (K_le_KM N M)

end DGPS.Examples.PositiveH1.Transfer
