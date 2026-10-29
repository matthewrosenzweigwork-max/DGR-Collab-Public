import DGPS.Examples.RoughBoundary.Model
import DGPS.Particle.Sobolev

/-!
# Rough particle Hamiltonian and oscillation (RUF037)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 6, (6.1)-(6.2). For the model data
`(0, W_{L,ε})`, `H_N = κN/2 - B_N`, `B_N = κ|S_N|²/(2N)`, `0 ≤ B_N ≤ 11N/12`, with oscillation
`11N/12` for `N ≥ 2` and `P_1 = m` for `N = 1`; `H¹(P_N) = H¹(m^N)`.
-/

open MeasureTheory Set
open scoped Real

namespace DGPS.Examples.RoughBoundary.Particle

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.Model

/-- `S_N(x) = ∑ᵢ U(xᵢ)`. -/
noncomputable def featureSum (L ε : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    EuclideanSpace ℝ (Fin 2) :=
  ∑ i, Ufeat L ε (x i)

/-- `B_N(x) = κ |S_N(x)|² / (2N)`. -/
noncomputable def roughB (L ε : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) : ℝ :=
  kappa * ‖featureSum L ε N x‖ ^ 2 / (2 * (N : ℝ))

lemma norm_featureSum_sq (L ε : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    ‖featureSum L ε N x‖ ^ 2 = ∑ i, ∑ j, inner ℝ (Ufeat L ε (x i)) (Ufeat L ε (x j)) := by
  rw [← real_inner_self_eq_norm_sq]
  unfold featureSum
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]

lemma hamiltonian_eq {L : ℝ} (hL : 0 < L) (ε : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    particleHamiltonian (modelData hL ε) N x = kappa * (N : ℝ) / 2 - roughB L ε N x := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  unfold particleHamiltonian roughB
  simp only [modelData, modelW, Finset.sum_const_zero, zero_add]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, norm_featureSum_sq]
  field_simp

lemma roughB_nonneg (L ε : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) : 0 ≤ roughB L ε N x := by
  have : 0 ≤ kappa := by unfold kappa; norm_num
  unfold roughB; positivity

lemma norm_featureSum_le (L ε : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    ‖featureSum L ε N x‖ ≤ N := by
  calc ‖featureSum L ε N x‖ ≤ ∑ i, ‖Ufeat L ε (x i)‖ := norm_sum_le _ _
    _ = N := by simp [norm_Ufeat]

lemma roughB_le (L ε : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    roughB L ε N x ≤ 11 * (N : ℝ) / 12 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have h1 := norm_featureSum_le L ε N x
  have h2 : ‖featureSum L ε N x‖ ^ 2 ≤ (N : ℝ) ^ 2 := by
    gcongr
  unfold roughB
  rw [div_le_iff₀ (by positivity)]
  have : kappa = 11 / 6 := rfl
  rw [this]
  nlinarith

lemma roughB_const (L ε : ℝ) (N : ℕ+) (y : Torus 1) :
    roughB L ε N (fun _ => y) = 11 * (N : ℝ) / 12 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have : featureSum L ε N (fun _ => y) = (N : ℝ) • Ufeat L ε y := by
    simp [featureSum, ← Nat.cast_smul_eq_nsmul ℝ]
  unfold roughB
  rw [this, norm_smul, mul_pow, norm_Ufeat, Real.norm_natCast]
  have : kappa = 11 / 6 := rfl
  rw [this]
  field_simp
  ring

lemma exists_Ufeat_eq {L : ℝ} (hL : 0 < L) (ε φ : ℝ) :
    ∃ y : Torus 1, Ufeat L ε y = !₂[Real.cos φ, Real.sin φ] := by
  have hc := continuous_theta L ε
  have h1 : theta L ε 1 = theta L ε 0 + 2 := by
    simpa using theta_add_one hL ε 0
  set t : ℝ := φ / (2 * π) with ht
  set k : ℤ := ⌈theta L ε 0 - t⌉ with hk
  have hk1 : theta L ε 0 - t ≤ k := Int.le_ceil _
  have hk2 : (k : ℝ) < theta L ε 0 - t + 1 := Int.ceil_lt_add_one _
  have hmem : t + k ∈ Icc (theta L ε 0) (theta L ε 1) := ⟨by linarith, by linarith⟩
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (zero_le_one' ℝ) hc.continuousOn hmem
  refine ⟨Spikes.pt x, ?_⟩
  rw [Ufeat_pt hL ε x]
  have e : 2 * π * theta L ε x = φ + (k : ℝ) * (2 * π) := by
    rw [hx, ht]; field_simp
  unfold Ureal
  rw [e, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

lemma sum_cos_sin_eq_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.range n, Real.cos (2 * π * i / n) = 0 ∧
    ∑ i ∈ Finset.range n, Real.sin (2 * π * i / n) = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hζ := Complex.isPrimitiveRoot_exp n hn0
  have hs := hζ.geom_sum_eq_zero (by omega)
  have key : ∀ i : ℕ, Complex.exp (2 * π * Complex.I / n) ^ i =
      Complex.exp (((2 * π * i / n : ℝ) : ℂ) * Complex.I) := by
    intro i
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [key] at hs
  constructor
  · have := congrArg Complex.re hs
    rw [Complex.re_sum] at this
    simpa only [Complex.exp_ofReal_mul_I_re, Complex.zero_re] using this
  · have := congrArg Complex.im hs
    rw [Complex.im_sum] at this
    simpa only [Complex.exp_ofReal_mul_I_im, Complex.zero_im] using this

lemma exists_featureSum_eq_zero {L : ℝ} (hL : 0 < L) (ε : ℝ) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∃ x : ParticleSpace 1 N, featureSum L ε N x = 0 := by
  choose y hy using fun i : Fin N => exists_Ufeat_eq hL ε (2 * π * (i : ℕ) / (N : ℕ))
  refine ⟨y, ?_⟩
  obtain ⟨hc, hs⟩ := sum_cos_sin_eq_zero N hN
  rw [← Fin.sum_univ_eq_sum_range (fun i => Real.cos (2 * π * i / (N : ℕ))) N] at hc
  rw [← Fin.sum_univ_eq_sum_range (fun i => Real.sin (2 * π * i / (N : ℕ))) N] at hs
  ext j
  fin_cases j
  · simp [featureSum, hy, hc]
  · simp [featureSum, hy, hs]

lemma density_eq {L : ℝ} (hL : 0 < L) (ε : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    particleDensity (modelData hL ε) N x =
      (∫ y, Real.exp (roughB L ε N y) ∂particleHaar 1 N)⁻¹ * Real.exp (roughB L ε N x) := by
  have hexp : ∀ y, Real.exp (-particleHamiltonian (modelData hL ε) N y) =
      Real.exp (-(kappa * (N : ℝ) / 2)) * Real.exp (roughB L ε N y) := by
    intro y
    rw [hamiltonian_eq, ← Real.exp_add]
    congr 1; ring
  have hZ : particlePartition (modelData hL ε) N =
      Real.exp (-(kappa * (N : ℝ) / 2)) * ∫ y, Real.exp (roughB L ε N y) ∂particleHaar 1 N := by
    unfold particlePartition
    simp_rw [hexp]
    rw [integral_const_mul]
  unfold particleDensity
  rw [hZ, hexp, mul_inv_rev]
  have := (Real.exp_pos (-(kappa * (N : ℝ) / 2))).ne'
  field_simp

lemma roughB_one (L ε : ℝ) (x : ParticleSpace 1 1) : roughB L ε 1 x = kappa / 2 := by
  have : featureSum L ε 1 x = Ufeat L ε (x 0) := by
    unfold featureSum
    exact Fin.sum_univ_one _
  unfold roughB
  rw [this, norm_Ufeat]
  simp

lemma particleLaw_one {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    particleLaw (modelData hL ε) 1 = particleHaar 1 1 := by
  have hd : ∀ x, particleDensity (modelData hL ε) 1 x = 1 := by
    intro x
    rw [density_eq]
    simp_rw [roughB_one]
    simp [(Real.exp_pos _).ne']
  unfold particleLaw
  simp_rw [hd]
  simp

/-- RUF037: Hamiltonian formula, exponent range, Gibbs density, exact oscillation (`N ≥ 2`),
the degenerate case `N = 1`, and the fixed-`N` Sobolev equivalence. -/
theorem rough_particle_hamiltonian_and_oscillation {L : ℝ} (hL : 0 < L) (ε : ℝ) (N : ℕ+) :
    (∀ x : ParticleSpace 1 N, particleHamiltonian (modelData hL ε) N x =
        kappa * (N : ℝ) / 2 - kappa * ‖∑ i, Ufeat L ε (x i)‖ ^ 2 / (2 * (N : ℝ))) ∧
    (∀ x : ParticleSpace 1 N, roughB L ε N x = kappa * ‖∑ i, Ufeat L ε (x i)‖ ^ 2 / (2 * (N : ℝ)) ∧
        0 ≤ roughB L ε N x ∧ roughB L ε N x ≤ 11 * (N : ℝ) / 12) ∧
    (∀ x : ParticleSpace 1 N, particleDensity (modelData hL ε) N x =
        (∫ y, Real.exp (roughB L ε N y) ∂particleHaar 1 N)⁻¹ * Real.exp (roughB L ε N x)) ∧
    particleLaw (modelData hL ε) N = (particleHaar 1 N).withDensity (fun x =>
        ENNReal.ofReal ((∫ y, Real.exp (roughB L ε N y) ∂particleHaar 1 N)⁻¹ *
          Real.exp (roughB L ε N x))) ∧
    ((2 : ℕ) ≤ (N : ℕ) →
      IsGreatest (Set.range (roughB L ε N)) (11 * (N : ℝ) / 12) ∧
      IsLeast (Set.range (roughB L ε N)) 0 ∧
      sSup (Set.range (roughB L ε N)) - sInf (Set.range (roughB L ε N)) = 11 * (N : ℝ) / 12) ∧
    ((N : ℕ) = 1 →
      (∀ x : ParticleSpace 1 N, roughB L ε N x = kappa / 2) ∧
      (∀ x : ParticleSpace 1 N, particleHamiltonian (modelData hL ε) N x = 0) ∧
      particleLaw (modelData hL ε) N = particleHaar 1 N) ∧
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ f : ParticleSpace 1 N → ℝ, MemParticleH1 (modelData hL ε) N f ↔ MemParticleHaarH1 N f) ∧
      (∀ f g, IsParticleWeakGradient (modelData hL ε) N f g ↔ IsParticleHaarWeakGradient N f g) ∧
      (∀ f g, IsParticleHaarWeakGradient N f g →
        c * particleH1NormSq (particleHaar 1 N) f g ≤
            particleH1NormSq (particleLaw (modelData hL ε) N) f g ∧
          particleH1NormSq (particleLaw (modelData hL ε) N) f g ≤
            C * particleH1NormSq (particleHaar 1 N) f g) := by
  refine ⟨hamiltonian_eq hL ε N, fun x => ⟨rfl, roughB_nonneg L ε N x, roughB_le L ε N x⟩,
    density_eq hL ε N, (by unfold particleLaw; simp_rw [density_eq]), fun hN => ?_, fun hN => ?_, ?_⟩
  · obtain ⟨x0, hx0⟩ := exists_featureSum_eq_zero hL ε N hN
    obtain ⟨y0⟩ : Nonempty (Torus 1) := inferInstance
    have hmax : roughB L ε N (fun _ => y0) = 11 * (N : ℝ) / 12 := roughB_const L ε N y0
    have hmin : roughB L ε N x0 = 0 := by simp [roughB, hx0]
    have hG : IsGreatest (Set.range (roughB L ε N)) (11 * (N : ℝ) / 12) :=
      ⟨⟨_, hmax⟩, by rintro _ ⟨x, rfl⟩; exact roughB_le L ε N x⟩
    have hLe : IsLeast (Set.range (roughB L ε N)) 0 :=
      ⟨⟨x0, hmin⟩, by rintro _ ⟨x, rfl⟩; exact roughB_nonneg L ε N x⟩
    refine ⟨hG, hLe, ?_⟩
    rw [hG.csSup_eq, hLe.csInf_eq]; ring
  · obtain rfl : N = 1 := PNat.coe_eq_one_iff.mp hN
    have hB := roughB_one L ε
    refine ⟨hB, fun x => ?_, particleLaw_one hL ε⟩
    rw [hamiltonian_eq, hB]
    have : kappa * ((1 : ℕ+) : ℝ) / 2 = kappa / 2 := by simp
    rw [this]; ring
  · obtain ⟨c, C, hc, hcC, h1, h2, h3, -⟩ := particleSobolev_equiv (modelData hL ε) N
    exact ⟨c, C, hc, hcC, h1, h2, h3⟩

end DGPS.Examples.RoughBoundary.Particle
