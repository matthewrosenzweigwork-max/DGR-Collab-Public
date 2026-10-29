import DGPS.FiniteN.Tools.PositiveRate
import DGPS.FiniteN.Tools.GroundState
import DGPS.FiniteN.Tools.UnitTorusNormalization
import DGPS.FiniteN.TiltedXY

/-!
# FIN017: explicit particle entropy defects

Generic part: smooth tests on the particle torus, the Gibbs-to-Haar entropy identity
`Ent_P(φ²) = Ent_m(G²) + ∫ H φ² dP + M log Z` with `G² = ρ φ²`, and the ground-state/Haar-LSI
estimate `Ent_P(φ²) ≤ (2/a₀) E(φ) + (B + Λ) ∫ φ² dP`.
-/

open MeasureTheory Real
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.EntropyDefects

open DGPS DGPS.Particle DGPS.FiniteN.Tools.WeightedSobolev

variable {d : ℕ} {N : ℕ+}

/-! ### Smooth particle tests via the flat torus -/

/-- Unflattening `ℝ^{N d} → (ℝ^d)^N`. -/
noncomputable def unflatL (d : ℕ) (N : ℕ+) :
    (Fin ((N : ℕ) * d) → ℝ) →L[ℝ] (Fin N → Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin ((N : ℕ) * d) => ℝ) (idx N d (i, j))

theorem ofT_torusLift (a : Fin ((N : ℕ) * d) → ℝ) :
    ofT d N (torusLift a) = particleLift (unflatL d N a) := rfl

theorem isSmoothPeriodic_comp_ofT {φ : ParticleSpace d N → ℝ} (hφ : IsSmoothPeriodicParticle φ) :
    IsSmoothPeriodic (fun y => φ (ofT d N y)) := by
  unfold IsSmoothPeriodic
  have : ((fun y => φ (ofT d N y)) ∘ torusLift : (Fin ((N : ℕ) * d) → ℝ) → ℝ) =
      (φ ∘ particleLift) ∘ unflatL d N := by
    funext a; exact congrArg φ (ofT_torusLift a)
  rw [this]
  exact hφ.comp (unflatL d N).contDiff

theorem continuous_toT : Continuous (toT d N) :=
  continuous_pi fun _ => (continuous_apply _).comp (continuous_apply _)

theorem continuous_of_smooth {φ : ParticleSpace d N → ℝ} (hφ : IsSmoothPeriodicParticle φ) :
    Continuous φ := by
  have : φ = (fun y => φ (ofT d N y)) ∘ toT d N := by funext x; simp [ofT_toT]
  rw [this]
  exact (isSmoothPeriodic_comp_ofT hφ).continuous_torus.comp continuous_toT

theorem comp_ofT_toT (φ : ParticleSpace d N → ℝ) (x : ParticleSpace d N) :
    (fun y => φ (ofT d N y)) (toT d N x) = φ x := by simp [ofT_toT]

theorem particlePartial_eq_coordPartial {φ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) (i : Fin N) (j : Fin d) (x : ParticleSpace d N) :
    particlePartial i j φ x =
      coordPartial (idx N d (i, j)) (fun y => φ (ofT d N y)) (toT d N x) := by
  have h := particlePartial_comp_toT (isSmoothPeriodic_comp_ofT hφ) i j x
  have e : (fun x => (fun y => φ (ofT d N y)) (toT d N x)) = φ := by
    funext x; simp [ofT_toT]
  rw [e] at h
  exact h

theorem continuous_particlePartial {φ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) (i : Fin N) (j : Fin d) :
    Continuous (particlePartial i j φ) := by
  have : particlePartial i j φ = fun x =>
      coordPartial (idx N d (i, j)) (fun y => φ (ofT d N y)) (toT d N x) :=
    funext (particlePartial_eq_coordPartial hφ i j)
  rw [this]
  exact ((isSmoothPeriodic_comp_ofT hφ).continuous_coordPartial _).comp continuous_toT

theorem particlePartial_const_mul (c : ℝ) {φ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) (i : Fin N) (j : Fin d) (x : ParticleSpace d N) :
    particlePartial i j (fun y => c * φ y) x = c * particlePartial i j φ x := by
  unfold particlePartial
  have h : ((fun y => c * φ y) ∘ particleLift) = c • (φ ∘ particleLift) := by
    funext y; simp
  rw [h, fderiv_const_smul ((hφ.differentiable (by simp)) _)]
  simp

theorem integrable_of_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)


/-! ### Gibbs entropy through Haar entropy -/

section Identity

variable (A : InteractionData d) (N : ℕ+)

theorem log_particleDensity (x : ParticleSpace d N) :
    Real.log (particleDensity A N x) =
      -Real.log (particlePartition A N) - particleHamiltonian A N x := by
  unfold particleDensity
  rw [Real.log_mul (inv_pos.2 (particlePartition_pos A N)).ne' (Real.exp_pos _).ne',
    Real.log_inv, Real.log_exp]
  ring

theorem integral_density_mul_sq {φ : ParticleSpace d N → ℝ} :
    ∫ x, particleDensity A N x * φ x ^ 2 ∂particleHaar d N = ∫ x, φ x ^ 2 ∂particleLaw A N :=
  (integral_particleLaw A N _).symm

/-- The real Gibbs entropy of `φ²` splits into the Haar entropy of `ρ φ²` and the defect terms. -/
theorem entropy_gibbs_eq {φ : ParticleSpace d N → ℝ} (hφ : Continuous φ) :
    homogeneousEntropy (particleLaw A N) (fun x => φ x ^ 2) =
      ENNReal.ofReal
        ((∫ x, particleDensity A N x * φ x ^ 2 *
            Real.log (particleDensity A N x * φ x ^ 2) ∂particleHaar d N
          - (∫ x, φ x ^ 2 ∂particleLaw A N) * Real.log (∫ x, φ x ^ 2 ∂particleLaw A N))
        + ((∫ x, φ x ^ 2 ∂particleLaw A N) * Real.log (particlePartition A N)
          + ∫ x, particleHamiltonian A N x * φ x ^ 2 ∂particleLaw A N)) := by
  have hv : Continuous fun x => φ x ^ 2 := hφ.pow 2
  have hvl : Continuous fun x => φ x ^ 2 * Real.log (φ x ^ 2) :=
    Real.continuous_mul_log.comp hv
  have hρ := particleDensity_continuous A N
  have hH := particleHamiltonian_continuous A N
  rw [homogeneousEntropy_eq_formula (Filter.Eventually.of_forall fun x => sq_nonneg (φ x))
    (integrable_of_continuous hv) (integrable_of_continuous hvl)]
  congr 1
  set M := ∫ x, φ x ^ 2 ∂particleLaw A N with hM
  set L := Real.log (particlePartition A N) with hL
  have hpt : ∀ x, particleDensity A N x * φ x ^ 2 * Real.log (particleDensity A N x * φ x ^ 2) =
      particleDensity A N x * (φ x ^ 2 * Real.log (φ x ^ 2))
        + particleDensity A N x * (φ x ^ 2 * (-L) - particleHamiltonian A N x * φ x ^ 2) := by
    intro x
    by_cases h0 : φ x ^ 2 = 0
    · simp [h0]
    · rw [Real.log_mul (particleDensity_pos A N x).ne' h0, log_particleDensity]
      ring
  simp_rw [hpt]
  have i1 : Integrable (fun x => particleDensity A N x * (φ x ^ 2 * Real.log (φ x ^ 2)))
      (particleHaar d N) := integrable_of_continuous (hρ.mul hvl)
  have i2 : Integrable (fun x => particleDensity A N x *
      (φ x ^ 2 * (-L) - particleHamiltonian A N x * φ x ^ 2)) (particleHaar d N) :=
    integrable_of_continuous (hρ.mul ((hv.mul continuous_const).sub (hH.mul hv)))
  rw [integral_add i1 i2, ← integral_particleLaw A N (fun x => φ x ^ 2 * Real.log (φ x ^ 2)),
    ← integral_particleLaw A N (fun x => φ x ^ 2 * (-L) - particleHamiltonian A N x * φ x ^ 2),
    integral_sub (f := fun x => φ x ^ 2 * (-L))
      (g := fun x => particleHamiltonian A N x * φ x ^ 2)
      (integrable_of_continuous (hv.mul continuous_const))
      (integrable_of_continuous (hH.mul hv)), integral_mul_const]
  ring

/-- The Haar entropy of `ρ φ²` as a real number. -/
theorem entropy_haar_eq {φ : ParticleSpace d N → ℝ} (hφ : Continuous φ) :
    homogeneousEntropy (particleHaar d N) (fun x => particleDensity A N x * φ x ^ 2) =
      ENNReal.ofReal
        (∫ x, particleDensity A N x * φ x ^ 2 *
            Real.log (particleDensity A N x * φ x ^ 2) ∂particleHaar d N
          - (∫ x, φ x ^ 2 ∂particleLaw A N) * Real.log (∫ x, φ x ^ 2 ∂particleLaw A N)) := by
  have hρ := particleDensity_continuous A N
  have hw : Continuous fun x => particleDensity A N x * φ x ^ 2 := hρ.mul (hφ.pow 2)
  have hwl : Continuous fun x => (particleDensity A N x * φ x ^ 2) *
      Real.log (particleDensity A N x * φ x ^ 2) := Real.continuous_mul_log.comp hw
  rw [homogeneousEntropy_eq_formula
    (Filter.Eventually.of_forall fun x => mul_nonneg (particleDensity_pos A N x).le (sq_nonneg _))
    (integrable_of_continuous hw) (integrable_of_continuous hwl), integral_density_mul_sq]

end Identity


/-! ### The ground-state transform on the flat torus -/

theorem sum_flat (f : Fin ((N : ℕ) * d) → ℝ) :
    ∑ k, f k = ∑ i, ∑ j, f (idx N d (i, j)) := by
  rw [← Fintype.sum_prod_type' (f := fun i j => f (idx N d (i, j)))]
  exact ((idx N d).sum_comp f).symm

/-- `y ↦ c φ(y) e^{-Ψ(y)/2}` on the flat torus. -/
noncomputable def groundT (Ψ : Torus ((N : ℕ) * d) → ℝ) (c : ℝ) (φ : ParticleSpace d N → ℝ)
    (y : Torus ((N : ℕ) * d)) : ℝ :=
  (c * φ (ofT d N y)) * Real.exp (-Ψ y / 2)

theorem isSmoothPeriodic_scaled {φ : ParticleSpace d N → ℝ} (hφ : IsSmoothPeriodicParticle φ)
    (c : ℝ) : IsSmoothPeriodic (fun y => c * φ (ofT d N y)) := by
  exact contDiff_const.mul (isSmoothPeriodic_comp_ofT hφ)

theorem isSmoothPeriodic_groundT {Ψ : Torus ((N : ℕ) * d) → ℝ} (hΨ : IsSmoothPeriodic Ψ)
    {φ : ParticleSpace d N → ℝ} (hφ : IsSmoothPeriodicParticle φ) (c : ℝ) :
    IsSmoothPeriodic (groundT Ψ c φ) :=
  (isSmoothPeriodic_scaled hφ c).mul (groundState_isSmoothPeriodic_exp_neg_half hΨ)

theorem groundT_toT_sq (Ψ : Torus ((N : ℕ) * d) → ℝ) (c : ℝ) (φ : ParticleSpace d N → ℝ)
    (x : ParticleSpace d N) :
    groundT Ψ c φ (toT d N x) ^ 2 = c ^ 2 * φ x ^ 2 * Real.exp (-Ψ (toT d N x)) := by
  unfold groundT
  rw [ofT_toT, mul_pow, mul_pow, ← Real.exp_nat_mul]
  congr 2; push_cast; ring


theorem coordPartial_const_mul {n : ℕ} {Φ : Torus n → ℝ} (hΦ : IsSmoothPeriodic Φ) (c : ℝ)
    (k : Fin n) (y : Torus n) :
    coordPartial k (fun z => c * Φ z) y = c * coordPartial k Φ y := by
  unfold coordPartial
  have h : ((fun z => c * Φ z) ∘ torusLift) = fun a => c * (Φ ∘ torusLift) a := rfl
  rw [h, fderiv_const_mul ((hΦ.differentiable (by simp)) _)]
  simp

/-- The potential term `ΔΨ/2 - |∇Ψ|²/4` of the ground-state identity. -/
noncomputable def qT {n : ℕ} (Ψ : Torus n → ℝ) (y : Torus n) : ℝ :=
  ∑ k, coordPartial k (coordPartial k Ψ) y / 2 - ∑ k, (coordPartial k Ψ y) ^ 2 / 4

theorem continuous_qT {n : ℕ} {Ψ : Torus n → ℝ} (hΨ : IsSmoothPeriodic Ψ) :
    Continuous (qT Ψ) := by
  unfold qT
  refine (continuous_finsetSum _ fun k _ => ?_).sub (continuous_finsetSum _ fun k _ => ?_)
  · exact (((hΨ.isSmoothPeriodic_coordPartial k).isSmoothPeriodic_coordPartial k).continuous_torus).div_const _
  · exact ((hΨ.isSmoothPeriodic_coordPartial k).continuous_torus.pow 2).div_const _

section Transfer

variable (A : InteractionData d) (N : ℕ+)

theorem rhs_transfer {Ψ : Torus ((N : ℕ) * d) → ℝ} (hΨ : IsSmoothPeriodic Ψ)
    (hHam : ∀ x, particleHamiltonian A N x = Ψ (toT d N x))
    {φ : ParticleSpace d N → ℝ} (hφ : IsSmoothPeriodicParticle φ) {c : ℝ}
    (hc : c ^ 2 = (particlePartition A N)⁻¹) :
    ∫ y, (∑ k, (coordPartial k (fun z => c * φ (ofT d N z)) y) ^ 2
        + qT Ψ y * (c * φ (ofT d N y)) ^ 2) * Real.exp (-Ψ y) ∂haar ((N : ℕ) * d)
      = particleSmoothEnergy A φ + ∫ x, qT Ψ (toT d N x) * φ x ^ 2 ∂particleLaw A N := by
  rw [integral_comp_toT]
  have hΦ := isSmoothPeriodic_comp_ofT hφ
  have hpt : ∀ x : ParticleSpace d N,
      (∑ k, (coordPartial k (fun z => c * φ (ofT d N z)) (toT d N x)) ^ 2
        + qT Ψ (toT d N x) * (c * φ (ofT d N (toT d N x))) ^ 2) * Real.exp (-Ψ (toT d N x))
      = particleDensity A N x * (∑ i, ∑ j, particlePartial i j φ x ^ 2
          + qT Ψ (toT d N x) * φ x ^ 2) := by
    intro x
    have h1 : ∑ k, (coordPartial k (fun z => c * φ (ofT d N z)) (toT d N x)) ^ 2
        = c ^ 2 * ∑ i, ∑ j, particlePartial i j φ x ^ 2 := by
      rw [sum_flat, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coordPartial_const_mul hΦ, particlePartial_eq_coordPartial hφ]
      ring
    rw [h1, ofT_toT, particleDensity, ← hHam x, mul_pow, hc]
    ring
  simp_rw [hpt]
  have i1 : Continuous fun x : ParticleSpace d N => ∑ i, ∑ j, particlePartial i j φ x ^ 2 :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_particlePartial hφ i j).pow 2
  have i2 : Continuous fun x : ParticleSpace d N => qT Ψ (toT d N x) * φ x ^ 2 :=
    ((continuous_qT hΨ).comp continuous_toT).mul ((continuous_of_smooth hφ).pow 2)
  rw [← integral_particleLaw A N (fun x => ∑ i, ∑ j, particlePartial i j φ x ^ 2
      + qT Ψ (toT d N x) * φ x ^ 2),
    integral_add (integrable_of_continuous i1) (integrable_of_continuous i2)]
  rfl

end Transfer


/-! ### The generic estimate for smooth tests -/

section Core

variable (A : InteractionData d) (N : ℕ+)

theorem log_partition_le {Λ : ℝ} (hΛ : ∀ x, -particleHamiltonian A N x ≤ Λ) :
    Real.log (particlePartition A N) ≤ Λ := by
  rw [Real.log_le_iff_le_exp (particlePartition_pos A N)]
  unfold particlePartition
  calc ∫ x, Real.exp (-particleHamiltonian A N x) ∂particleHaar d N
      ≤ ∫ _x, Real.exp Λ ∂particleHaar d N :=
        integral_mono (exp_neg_hamiltonian_integrable A N) (integrable_const _)
          fun x => Real.exp_le_exp.2 (hΛ x)
    _ = Real.exp Λ := by simp

theorem qT_le {n : ℕ} (Ψ : Torus n → ℝ) (y : Torus n) :
    qT Ψ y ≤ (∑ k, coordPartial k (coordPartial k Ψ) y) / 2 := by
  unfold qT
  have : 0 ≤ ∑ k, (coordPartial k Ψ y) ^ 2 / 4 :=
    Finset.sum_nonneg fun k _ => by positivity
  rw [Finset.sum_div]
  linarith

theorem tangentNormSq_partial {d : ℕ} {N : ℕ+} (ψ : ParticleSpace d N → ℝ) (x : ParticleSpace d N) :
    particleTangentNormSq (fun i => (WithLp.toLp 2 fun j => particlePartial i j ψ x : Tangent d))
      = ∑ i, ∑ j, particlePartial i j ψ x ^ 2 := by
  rw [particleTangentNormSq_eq]

/-- The generic entropy bound on smooth tests. -/
theorem core_smooth {Ψ : Torus ((N : ℕ) * d) → ℝ} (hΨ : IsSmoothPeriodic Ψ)
    (hHam : ∀ x, particleHamiltonian A N x = Ψ (toT d N x)) {B Λ : ℝ}
    (hB : ∀ x, particleHamiltonian A N x +
      (1 / (4 * Real.pi ^ 2)) * ∑ k, coordPartial k (coordPartial k Ψ) (toT d N x) ≤ B)
    (hΛ : ∀ x, -particleHamiltonian A N x ≤ Λ)
    {φ : ParticleSpace d N → ℝ} (hφ : IsSmoothPeriodicParticle φ) :
    homogeneousEntropy (particleLaw A N) (fun y => φ y ^ 2) ≤
      ENNReal.ofReal (2 / (4 * Real.pi ^ 2) * particleSmoothEnergy A φ
        + (B + Λ) * ∫ y, φ y ^ 2 ∂particleLaw A N) := by
  have hφc := continuous_of_smooth hφ
  set c := Real.sqrt (particlePartition A N)⁻¹ with hcdef
  have hc : c ^ 2 = (particlePartition A N)⁻¹ :=
    Real.sq_sqrt (inv_pos.2 (particlePartition_pos A N)).le
  set g : ParticleSpace d N → ℝ := fun x => groundT Ψ c φ (toT d N x) with hgdef
  have hg : IsSmoothPeriodicParticle g :=
    isSmoothPeriodicParticle_comp_toT (isSmoothPeriodic_groundT hΨ hφ c)
  have hlsi := DGPS.FiniteN.PositiveRate.particleHaar_lsi (DGPS.FiniteN.PositiveRate.isParticleHaarWeakGradient_of_smooth hg)
  have hg2 : (fun x => g x ^ 2) = fun x => particleDensity A N x * φ x ^ 2 := by
    funext x
    simp only [hgdef]
    rw [groundT_toT_sq, hc, particleDensity, ← hHam x]
    ring
  rw [hg2, entropy_haar_eq A N hφc] at hlsi
  simp only [tangentNormSq_partial] at hlsi
  have hcont : Continuous fun x : ParticleSpace d N => ∑ i, ∑ j, particlePartial i j g x ^ 2 :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_particlePartial hg i j).pow 2
  have hnn : ∀ x : ParticleSpace d N, 0 ≤ ∑ i, ∑ j, particlePartial i j g x ^ 2 :=
    fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_continuous hcont)
    (Filter.Eventually.of_forall hnn)] at hlsi
  -- the Dirichlet integral of the ground-state transform
  have hdir : ∫ x, ∑ i, ∑ j, particlePartial i j g x ^ 2 ∂particleHaar d N =
      particleSmoothEnergy A φ + ∫ x, qT Ψ (toT d N x) * φ x ^ 2 ∂particleLaw A N := by
    have e1 : ∀ x : ParticleSpace d N, ∑ i, ∑ j, particlePartial i j g x ^ 2 =
        (fun y => ∑ k, (coordPartial k (groundT Ψ c φ) y) ^ 2) (toT d N x) := by
      intro x
      simp only [hgdef]
      rw [sum_flat]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [particlePartial_comp_toT (isSmoothPeriodic_groundT hΨ hφ c)]
    rw [show (∫ x, ∑ i, ∑ j, particlePartial i j g x ^ 2 ∂particleHaar d N) =
        ∫ y, ∑ k, (coordPartial k (groundT Ψ c φ) y) ^ 2 ∂haar ((N : ℕ) * d) from by
      rw [integral_comp_toT]
      exact integral_congr_ae (Filter.Eventually.of_forall e1)]
    have := ground_state_weighted_energy_identity_torus Ψ (fun z => c * φ (ofT d N z)) hΨ
      (isSmoothPeriodic_scaled hφ c)
    change ∫ y, ∑ j, (coordPartial j (fun z => (c * φ (ofT d N z)) * Real.exp (-Ψ z / 2)) y) ^ 2
      ∂haar ((N : ℕ) * d) = _ at this
    unfold groundT
    rw [this]
    exact rhs_transfer A N hΨ hHam hφ hc
  rw [hdir] at hlsi
  set D := particleSmoothEnergy A φ + ∫ x, qT Ψ (toT d N x) * φ x ^ 2 ∂particleLaw A N with hD
  have hDnn : 0 ≤ D := by
    rw [← hdir]; exact integral_nonneg hnn
  have hα : (0 : ℝ) ≤ 2 / (4 * Real.pi ^ 2) := by positivity
  rw [← ENNReal.ofReal_mul hα, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hα hDnn)] at hlsi
  rw [entropy_gibbs_eq A N hφc]
  apply ENNReal.ofReal_le_ofReal
  set M := ∫ x, φ x ^ 2 ∂particleLaw A N with hM
  have hM0 : 0 ≤ M := integral_nonneg fun x => sq_nonneg _
  have hlogZ := log_partition_le A N hΛ
  -- pointwise bound on the potential terms
  have hq : ∀ x, 2 / (4 * Real.pi ^ 2) * qT Ψ (toT d N x) + particleHamiltonian A N x ≤ B := by
    intro x
    have h1 := qT_le Ψ (toT d N x)
    have h2 := hB x
    have : 2 / (4 * Real.pi ^ 2) * qT Ψ (toT d N x) ≤
        (1 / (4 * Real.pi ^ 2)) * ∑ k, coordPartial k (coordPartial k Ψ) (toT d N x) := by
      calc 2 / (4 * Real.pi ^ 2) * qT Ψ (toT d N x)
          ≤ 2 / (4 * Real.pi ^ 2) * ((∑ k, coordPartial k (coordPartial k Ψ) (toT d N x)) / 2) :=
            mul_le_mul_of_nonneg_left h1 hα
        _ = _ := by ring
    linarith
  have hi1 : Continuous fun x : ParticleSpace d N =>
      (2 / (4 * Real.pi ^ 2) * qT Ψ (toT d N x) + particleHamiltonian A N x) * φ x ^ 2 :=
    ((continuous_const.mul ((continuous_qT hΨ).comp continuous_toT)).add
      (particleHamiltonian_continuous A N)).mul (hφc.pow 2)
  have hint : ∫ x, (2 / (4 * Real.pi ^ 2) * qT Ψ (toT d N x) + particleHamiltonian A N x) * φ x ^ 2
      ∂particleLaw A N ≤ B * M := by
    rw [hM, ← integral_const_mul]
    exact integral_mono (integrable_of_continuous hi1)
      (integrable_of_continuous (continuous_const.mul (hφc.pow 2)))
      fun x => mul_le_mul_of_nonneg_right (hq x) (sq_nonneg _)
  have hsplit : ∫ x, (2 / (4 * Real.pi ^ 2) * qT Ψ (toT d N x) + particleHamiltonian A N x) * φ x ^ 2
      ∂particleLaw A N =
      2 / (4 * Real.pi ^ 2) * ∫ x, qT Ψ (toT d N x) * φ x ^ 2 ∂particleLaw A N
        + ∫ x, particleHamiltonian A N x * φ x ^ 2 ∂particleLaw A N := by
    rw [← integral_const_mul, ← integral_add]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    · exact integrable_of_continuous
        (continuous_const.mul (((continuous_qT hΨ).comp continuous_toT).mul (hφc.pow 2)))
    · exact integrable_of_continuous ((particleHamiltonian_continuous A N).mul (hφc.pow 2))
  have hZ' : M * Real.log (particlePartition A N) ≤ M * Λ := mul_le_mul_of_nonneg_left hlogZ hM0
  have hhlsi : ∫ x, particleDensity A N x * φ x ^ 2 *
        Real.log (particleDensity A N x * φ x ^ 2) ∂particleHaar d N - M * Real.log M ≤
      2 / (4 * Real.pi ^ 2) * D := hlsi
  rw [hD] at hhlsi
  nlinarith [hhlsi, hint, hsplit, hZ']

end Core

/-! ### The trigonometric model family -/

theorem fderiv_eq_deriv_line {n : ℕ} {F : (Fin n → ℝ) → ℝ} {b : Fin n → ℝ}
    (hF : DifferentiableAt ℝ F b) (v : Fin n → ℝ) :
    fderiv ℝ F b v = deriv (fun u : ℝ => F (b + u • v)) 0 := by
  have h1 : HasDerivAt (fun u : ℝ => b + u • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add b
  have h2 : HasFDerivAt F (fderiv ℝ F (b + (0:ℝ) • v)) (b + (0:ℝ) • v) := by
    simpa using hF.hasFDerivAt
  have := h2.comp_hasDerivAt (0:ℝ) h1
  have h4 := this.deriv
  simp only [zero_smul, add_zero] at h4
  exact h4.symm

theorem hasDerivAt_cosL (x : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cos (2 * π * (x + u))) (-(Real.sin (2 * π * x)) * (2 * π)) 0 := by
  have h := (((hasDerivAt_id (0:ℝ)).const_add x).const_mul (2 * π)).cos
  simpa using h

theorem hasDerivAt_sinL (x : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin (2 * π * (x + u))) (Real.cos (2 * π * x) * (2 * π)) 0 := by
  have h := (((hasDerivAt_id (0:ℝ)).const_add x).const_mul (2 * π)).sin
  simpa using h

section Trig
variable {n : ℕ}

noncomputable def cosSum (a : Fin n → ℝ) : ℝ := ∑ k, Real.cos (2 * π * a k)
noncomputable def sinSum (a : Fin n → ℝ) : ℝ := ∑ k, Real.sin (2 * π * a k)

noncomputable def trigF (h p q r : ℝ) (a : Fin n → ℝ) : ℝ :=
  -h * cosSum a - p * cosSum a ^ 2 - q * sinSum a ^ 2 + r

theorem cosSum_line (b : Fin n → ℝ) (k : Fin n) (u : ℝ) :
    cosSum (b + u • (Pi.single k (1:ℝ) : Fin n → ℝ)) =
      cosSum b + (Real.cos (2 * π * (b k + u)) - Real.cos (2 * π * b k)) := by
  unfold cosSum
  have : ∀ j, Real.cos (2 * π * (b + u • (Pi.single k (1:ℝ) : Fin n → ℝ)) j) =
      Real.cos (2 * π * b j) + (if j = k then Real.cos (2 * π * (b k + u)) - Real.cos (2 * π * b k) else 0) := by
    intro j
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sinSum_line (b : Fin n → ℝ) (k : Fin n) (u : ℝ) :
    sinSum (b + u • (Pi.single k (1:ℝ) : Fin n → ℝ)) =
      sinSum b + (Real.sin (2 * π * (b k + u)) - Real.sin (2 * π * b k)) := by
  unfold sinSum
  have : ∀ j, Real.sin (2 * π * (b + u • (Pi.single k (1:ℝ) : Fin n → ℝ)) j) =
      Real.sin (2 * π * b j) + (if j = k then Real.sin (2 * π * (b k + u)) - Real.sin (2 * π * b k) else 0) := by
    intro j
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem contDiff_trigF (h p q r : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (trigF (n := n) h p q r) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cosSum (n := n)) :=
    ContDiff.sum fun k _ => (contDiff_const.mul (contDiff_apply ℝ ℝ k)).cos
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sinSum (n := n)) :=
    ContDiff.sum fun k _ => (contDiff_const.mul (contDiff_apply ℝ ℝ k)).sin
  unfold trigF
  exact (((contDiff_const.mul hc).sub (contDiff_const.mul (hc.pow 2))).sub
    (contDiff_const.mul (hs.pow 2))).add contDiff_const

/-- First directional derivative. -/
noncomputable def trigG (h p q : ℝ) (k : Fin n) (b : Fin n → ℝ) : ℝ :=
  2 * π * h * Real.sin (2 * π * b k) + 4 * π * p * cosSum b * Real.sin (2 * π * b k)
    - 4 * π * q * sinSum b * Real.cos (2 * π * b k)

theorem fderiv_trigF (h p q r : ℝ) (k : Fin n) (b : Fin n → ℝ) :
    fderiv ℝ (trigF h p q r) b (Pi.single k 1) = trigG h p q k b := by
  rw [fderiv_eq_deriv_line ((contDiff_trigF h p q r).differentiable (by simp) b)]
  have e : (fun u : ℝ => trigF h p q r (b + u • (Pi.single k (1:ℝ) : Fin n → ℝ))) = fun u =>
      -h * (cosSum b + (Real.cos (2 * π * (b k + u)) - Real.cos (2 * π * b k)))
      - p * (cosSum b + (Real.cos (2 * π * (b k + u)) - Real.cos (2 * π * b k))) ^ 2
      - q * (sinSum b + (Real.sin (2 * π * (b k + u)) - Real.sin (2 * π * b k))) ^ 2 + r := by
    funext u
    unfold trigF
    rw [cosSum_line, sinSum_line]
  rw [e]
  have hc := hasDerivAt_cosL (b k)
  have hs := hasDerivAt_sinL (b k)
  have h0 := ((((hc.sub_const (Real.cos (2 * π * b k))).const_add (cosSum b)).const_mul (-h)).sub
      ((((hc.sub_const (Real.cos (2 * π * b k))).const_add (cosSum b)).pow 2).const_mul p)).sub
      ((((hs.sub_const (Real.sin (2 * π * b k))).const_add (sinSum b)).pow 2).const_mul q)
  have h1 := h0.add_const r
  refine HasDerivAt.deriv ?_
  convert h1 using 1
  simp [trigG]
  ring

theorem contDiff_trigG (h p q r : ℝ) (k : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (trigG (n := n) h p q k) := by
  have : trigG (n := n) h p q k = fun b => fderiv ℝ (trigF h p q r) b (Pi.single k 1) := by
    funext b; exact (fderiv_trigF h p q r k b).symm
  rw [this]
  exact ((contDiff_trigF h p q r).fderiv_right (by simp)).clm_apply contDiff_const

noncomputable def trigD2 (h p q : ℝ) (k : Fin n) (b : Fin n → ℝ) : ℝ :=
  4 * π ^ 2 * h * Real.cos (2 * π * b k) - 8 * π ^ 2 * p * Real.sin (2 * π * b k) ^ 2
    + 8 * π ^ 2 * p * cosSum b * Real.cos (2 * π * b k)
    - 8 * π ^ 2 * q * Real.cos (2 * π * b k) ^ 2 + 8 * π ^ 2 * q * sinSum b * Real.sin (2 * π * b k)

theorem fderiv_trigG (h p q : ℝ) (k : Fin n) (b : Fin n → ℝ) :
    fderiv ℝ (trigG h p q k) b (Pi.single k 1) = trigD2 h p q k b := by
  rw [fderiv_eq_deriv_line ((contDiff_trigG h p q 0 k).differentiable (by simp) b)]
  have e : (fun u : ℝ => trigG h p q k (b + u • (Pi.single k (1:ℝ) : Fin n → ℝ))) = fun u =>
      2 * π * h * Real.sin (2 * π * (b k + u))
      + 4 * π * p * (cosSum b + (Real.cos (2 * π * (b k + u)) - Real.cos (2 * π * b k)))
          * Real.sin (2 * π * (b k + u))
      - 4 * π * q * (sinSum b + (Real.sin (2 * π * (b k + u)) - Real.sin (2 * π * b k)))
          * Real.cos (2 * π * (b k + u)) := by
    funext u
    unfold trigG
    rw [cosSum_line, sinSum_line]
    simp
  rw [e]
  have hc := hasDerivAt_cosL (b k)
  have hs := hasDerivAt_sinL (b k)
  have hC := (hc.sub_const (Real.cos (2 * π * b k))).const_add (cosSum b)
  have hS := (hs.sub_const (Real.sin (2 * π * b k))).const_add (sinSum b)
  have h0 := (((hs.const_mul (2 * π * h)).add
      ((hC.const_mul (4 * π * p)).mul hs)).sub ((hS.const_mul (4 * π * q)).mul hc))
  refine HasDerivAt.deriv ?_
  convert h0 using 1
  simp [trigD2]
  ring

theorem sum_fderiv_trigG (h p q : ℝ) (b : Fin n → ℝ) :
    ∑ k, fderiv ℝ (trigG h p q k) b (Pi.single k 1) =
      4 * π ^ 2 * h * cosSum b - 8 * π ^ 2 * p * ∑ k, Real.sin (2 * π * b k) ^ 2
        + 8 * π ^ 2 * p * cosSum b ^ 2 - 8 * π ^ 2 * q * ∑ k, Real.cos (2 * π * b k) ^ 2
        + 8 * π ^ 2 * q * sinSum b ^ 2 := by
  simp only [fderiv_trigG, trigD2, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [show ∑ k, Real.cos (2 * π * b k) = cosSum b from rfl,
    show ∑ k, Real.sin (2 * π * b k) = sinSum b from rfl]
  ring

theorem abs_cosSum_le (b : Fin n → ℝ) : |cosSum b| ≤ n := by
  unfold cosSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |Real.cos (2 * π * b k)| ≤ ∑ _k : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => Real.abs_cos_le_one _
    _ = n := by simp

theorem abs_sinSum_le (b : Fin n → ℝ) : |sinSum b| ≤ n := by
  unfold sinSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |Real.sin (2 * π * b k)| ≤ ∑ _k : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => Real.abs_sin_le_one _
    _ = n := by simp

theorem trig_B (h p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (b : Fin n → ℝ) :
    trigF h p q r b + (1 / (4 * π ^ 2)) * ∑ k, fderiv ℝ (trigG h p q k) b (Pi.single k 1)
      ≤ r + (p + q) * (n : ℝ) ^ 2 := by
  rw [sum_fderiv_trigG]
  have hC : cosSum b ^ 2 ≤ (n : ℝ) ^ 2 := sq_le_sq' (abs_le.1 (abs_cosSum_le b)).1 (abs_le.1 (abs_cosSum_le b)).2
  have hS : sinSum b ^ 2 ≤ (n : ℝ) ^ 2 := sq_le_sq' (abs_le.1 (abs_sinSum_le b)).1 (abs_le.1 (abs_sinSum_le b)).2
  have h1 : 0 ≤ ∑ k, Real.sin (2 * π * b k) ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h2 : 0 ≤ ∑ k, Real.cos (2 * π * b k) ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have e : trigF h p q r b + (1 / (4 * π ^ 2)) *
      (4 * π ^ 2 * h * cosSum b - 8 * π ^ 2 * p * ∑ k, Real.sin (2 * π * b k) ^ 2
        + 8 * π ^ 2 * p * cosSum b ^ 2 - 8 * π ^ 2 * q * ∑ k, Real.cos (2 * π * b k) ^ 2
        + 8 * π ^ 2 * q * sinSum b ^ 2) =
      r + p * cosSum b ^ 2 + q * sinSum b ^ 2 - 2 * p * ∑ k, Real.sin (2 * π * b k) ^ 2
        - 2 * q * ∑ k, Real.cos (2 * π * b k) ^ 2 := by
    unfold trigF
    field_simp
    ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hC hp, mul_le_mul_of_nonneg_left hS hq,
    mul_nonneg hp h1, mul_nonneg hq h2]

theorem trig_Lambda (h p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (b : Fin n → ℝ) :
    -trigF h p q r b ≤ |h| * n + (p + q) * (n : ℝ) ^ 2 := by
  have hC : cosSum b ^ 2 ≤ (n : ℝ) ^ 2 := sq_le_sq' (abs_le.1 (abs_cosSum_le b)).1 (abs_le.1 (abs_cosSum_le b)).2
  have hS : sinSum b ^ 2 ≤ (n : ℝ) ^ 2 := sq_le_sq' (abs_le.1 (abs_sinSum_le b)).1 (abs_le.1 (abs_sinSum_le b)).2
  have hh : h * cosSum b ≤ |h| * n :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_cosSum_le b) (abs_nonneg _))
  unfold trigF
  nlinarith [mul_le_mul_of_nonneg_left hC hp, mul_le_mul_of_nonneg_left hS hq]

end Trig


/-! ### Entropy defect for Hamiltonians of trigonometric type -/

section TrigModels

/-- The Hamiltonian as a function on the flat torus. -/
noncomputable def hamT (A : InteractionData 1) (N : ℕ+) : Torus ((N : ℕ) * 1) → ℝ :=
  fun y => particleHamiltonian A N (ofT 1 N y)

theorem coordPartial2_trig {n : ℕ} {Ψ : Torus n → ℝ} (h p q r : ℝ)
    (hF : Ψ ∘ torusLift = trigF h p q r) (k : Fin n) (b : Fin n → ℝ) :
    coordPartial k (coordPartial k Ψ) (torusLift b) =
      fderiv ℝ (trigG h p q k) b (Pi.single k 1) := by
  have h1 := congrFun (coordPartial_comp_torusLift k Ψ)
  have h2 : coordPartial k Ψ ∘ torusLift = trigG h p q k := by
    funext a
    rw [h1 a, hF]
    exact fderiv_trigF h p q r k a
  have h3 := congrFun (coordPartial_comp_torusLift k (coordPartial k Ψ)) b
  rw [h2] at h3
  exact h3

variable (A : InteractionData 1) (N : ℕ+)

/-- The entropy estimate for a Hamiltonian that is a trigonometric polynomial of the type
`-h C - p C² - q S² + r`. -/
theorem trig_entropy_defect {h p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hH : ∀ a : Fin ((N : ℕ) * 1) → ℝ,
      particleHamiltonian A N (ofT 1 N (torusLift a)) = trigF h p q r a) :
    ∀ f : ParticleH1 A N, homogeneousEntropy (particleLaw A N) (fun y => f.1 y ^ 2) ≤
      ENNReal.ofReal (2 / (4 * Real.pi ^ 2) * particleEnergy A N f
        + (r + 2 * (p + q) * (((N : ℕ) * 1 : ℕ) : ℝ) ^ 2 + |h| * (((N : ℕ) * 1 : ℕ) : ℝ)) *
          ∫ y, f.1 y ^ 2 ∂particleLaw A N) := by
  have hF : hamT A N ∘ torusLift = trigF h p q r := funext hH
  have hΨ : IsSmoothPeriodic (hamT A N) := by
    unfold IsSmoothPeriodic
    rw [hF]
    exact contDiff_trigF h p q r
  have hHam : ∀ x, particleHamiltonian A N x = hamT A N (toT 1 N x) := fun x => by
    simp [hamT, ofT_toT]
  have hlift : ∀ x : ParticleSpace 1 N,
      torusLift (SharpLSI.secT (toT 1 N x)) = toT 1 N x := fun x => SharpLSI.liftT_secT _
  have hB : ∀ x : ParticleSpace 1 N, particleHamiltonian A N x +
      (1 / (4 * Real.pi ^ 2)) * ∑ k, coordPartial k (coordPartial k (hamT A N)) (toT 1 N x)
      ≤ r + (p + q) * (((N : ℕ) * 1 : ℕ) : ℝ) ^ 2 := by
    intro x
    have := trig_B h p q r hp hq (SharpLSI.secT (toT 1 N x))
    rw [hHam x, ← hlift x]
    simp only [coordPartial2_trig h p q r hF, ← hF, Function.comp_apply] at this ⊢
    exact this
  have hΛ : ∀ x : ParticleSpace 1 N, -particleHamiltonian A N x ≤
      |h| * (((N : ℕ) * 1 : ℕ) : ℝ) + (p + q) * (((N : ℕ) * 1 : ℕ) : ℝ) ^ 2 := by
    intro x
    have := trig_Lambda h p q r hp hq hr (SharpLSI.secT (toT 1 N x))
    rw [hHam x, ← hlift x]
    simpa [← hF] using this
  have key := (fixed_n_weighted_sobolev_extension A N).2.2.2 (2 / (4 * Real.pi ^ 2))
    ((r + (p + q) * (((N : ℕ) * 1 : ℕ) : ℝ) ^ 2) +
      (|h| * (((N : ℕ) * 1 : ℕ) : ℝ) + (p + q) * (((N : ℕ) * 1 : ℕ) : ℝ) ^ 2))
    (fun φ hφ => core_smooth A N hΨ hHam hB hΛ hφ)
  intro f
  have := key f
  convert this using 3
  ring

end TrigModels


/-! ### The scalar cosine model and the tilted XY model -/

section Models

open DGPS.FiniteN.TiltedXY.Fin051

/-- The scalar cosine model in interaction form:
`H = -h S - κ S² / (2N)` with `S = ∑ cos(2π xᵢ)`, as `V = -h c - (κ/2) c²`,
`W = (κ/2) (c(x) - c(y))²`. -/
noncomputable def cosData (h κ : ℝ) : InteractionData 1 where
  V := fun x => -h * (phase x).re - κ / 2 * (phase x).re ^ 2
  W := fun x y => κ / 2 * ((phase x).re - (phase y).re) ^ 2
  V_continuous := by
    have hc := Complex.continuous_re.comp continuous_phase
    exact (continuous_const.mul hc).sub (continuous_const.mul (hc.pow 2))
  W_continuous := by
    have hc := Complex.continuous_re.comp continuous_phase
    exact continuous_const.mul (((hc.comp continuous_fst).sub (hc.comp continuous_snd)).pow 2)
  W_symm := fun x y => by ring
  W_diag := fun x => by simp

theorem cosData_V_lift (h κ : ℝ) (a : Fin 1 → ℝ) :
    (cosData h κ).V (torusLift a) =
      -h * Real.cos (2 * π * a 0) - κ / 2 * Real.cos (2 * π * a 0) ^ 2 := by
  show -h * (phase _).re - κ / 2 * (phase _).re ^ 2 = _
  rw [phase_re_lift]

theorem cosData_W_lift (h κ : ℝ) (a b : Fin 1 → ℝ) :
    (cosData h κ).W (torusLift a) (torusLift b) =
      κ / 2 * (Real.cos (2 * π * a 0) - Real.cos (2 * π * b 0)) ^ 2 := by
  show κ / 2 * ((phase _).re - (phase _).re) ^ 2 = _
  rw [phase_re_lift, phase_re_lift]

variable (N : ℕ+)

theorem sum_idx_one (g : ℝ → ℝ) (a : Fin ((N : ℕ) * 1) → ℝ) :
    ∑ k, g (a k) = ∑ i : Fin N, g (a (idx N 1 (i, 0))) := by
  rw [sum_flat (f := fun k => g (a k))]
  simp

theorem ofT_torusLift_apply (a : Fin ((N : ℕ) * 1) → ℝ) (i : Fin N) :
    ofT 1 N (torusLift a) i = torusLift (fun j : Fin 1 => a (idx N 1 (i, j))) := rfl

theorem cos_hamiltonian_lift (h κ : ℝ) (a : Fin ((N : ℕ) * 1) → ℝ) :
    particleHamiltonian (cosData h κ) N (ofT 1 N (torusLift a)) =
      trigF h (κ / (2 * (N : ℝ))) 0 0 a := by
  have hN : (N : ℝ) ≠ 0 := by positivity
  unfold particleHamiltonian trigF
  simp only [ofT_torusLift_apply, cosData_V_lift, cosData_W_lift]
  set y : Fin N → ℝ := fun i => Real.cos (2 * π * a (idx N 1 (i, 0))) with hy
  have hC : cosSum a = ∑ i, y i := by
    unfold cosSum
    exact sum_idx_one N (fun t => Real.cos (2 * π * t)) a
  have hrow : ∀ i, ∑ j, κ / 2 * (y i - y j) ^ 2 =
      κ / 2 * ((N : ℝ) * y i ^ 2 - 2 * y i * ∑ j, y j + ∑ j, y j ^ 2) := by
    intro i
    rw [← Finset.mul_sum]
    congr 1
    have : ∀ j, (y i - y j) ^ 2 = y i ^ 2 - 2 * y i * y j + y j ^ 2 := fun j => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : ∑ i, (-h * y i - κ / 2 * y i ^ 2) = -h * ∑ i, y i - κ / 2 * ∑ i, y i ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  have h2 : ∑ i, ∑ j, κ / 2 * (y i - y j) ^ 2 =
      κ / 2 * (2 * (N : ℝ) * ∑ i, y i ^ 2 - 2 * (∑ i, y i) ^ 2) := by
    simp only [hrow]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  show ∑ i, (-h * y i - κ / 2 * y i ^ 2) +
      1 / (2 * ((N : ℕ) : ℝ)) * ∑ x, ∑ j, κ / 2 * (y x - y j) ^ 2 =
    -h * cosSum a - κ / (2 * ((N : ℕ) : ℝ)) * cosSum a ^ 2 - 0 * sinSum a ^ 2 + 0
  rw [h1, h2, hC]
  field_simp
  ring

theorem xy_hamiltonian_lift (h κ : ℝ) (a : Fin ((N : ℕ) * 1) → ℝ) :
    particleHamiltonian (tiltedXYData h κ) N (ofT 1 N (torusLift a)) =
      trigF h (κ / (2 * (N : ℝ))) (κ / (2 * (N : ℝ))) (κ * (N : ℝ) / 2) a := by
  have hN : (N : ℝ) ≠ 0 := by positivity
  unfold particleHamiltonian trigF
  simp only [ofT_torusLift_apply, tiltedXYData_V_lift, tiltedXYData_W_lift]
  set c : Fin N → ℝ := fun i => Real.cos (2 * π * a (idx N 1 (i, 0))) with hc
  set t : Fin N → ℝ := fun i => Real.sin (2 * π * a (idx N 1 (i, 0))) with ht
  have hC : cosSum a = ∑ i, c i := by
    unfold cosSum
    exact sum_idx_one N (fun t => Real.cos (2 * π * t)) a
  have hS : sinSum a = ∑ i, t i := by
    unfold sinSum
    exact sum_idx_one N (fun t => Real.sin (2 * π * t)) a
  have hcos : ∀ i j, Real.cos (2 * π * (a (idx N 1 (i, 0)) - a (idx N 1 (j, 0)))) =
      c i * c j + t i * t j := by
    intro i j
    rw [mul_sub, Real.cos_sub]
  have h2 : ∑ i, ∑ j, κ * (1 - Real.cos (2 * π * (a (idx N 1 (i, 0)) - a (idx N 1 (j, 0))))) =
      κ * ((N : ℝ) ^ 2 - (∑ i, c i) ^ 2 - (∑ i, t i) ^ 2) := by
    simp only [hcos, ← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul, sq]
    ring
  show ∑ i, -h * c i + 1 / (2 * ((N : ℕ) : ℝ)) * ∑ x, ∑ j, κ * (1 - Real.cos (2 * π *
      (a (idx N 1 (x, 0)) - a (idx N 1 (j, 0))))) =
    -h * cosSum a - κ / (2 * ((N : ℕ) : ℝ)) * cosSum a ^ 2 -
      κ / (2 * ((N : ℕ) : ℝ)) * sinSum a ^ 2 + κ * ((N : ℕ) : ℝ) / 2
  rw [h2, hC, hS, ← Finset.mul_sum]
  field_simp
  ring


/-- Scalar cosine model: `Ent(f²) ≤ (2/a₀) E(f) + (|h| + κ) N ‖f‖²`. -/
theorem cos_entropy_defect (h : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ f : ParticleH1 (cosData h κ) N,
      homogeneousEntropy (particleLaw (cosData h κ) N) (fun y => f.1 y ^ 2) ≤
        ENNReal.ofReal (2 / (4 * π ^ 2) * particleEnergy (cosData h κ) N f +
          (|h| + κ) * (N : ℝ) * ∫ y, f.1 y ^ 2 ∂particleLaw (cosData h κ) N) := by
  have hN : (0 : ℝ) < (N : ℝ) := by positivity
  intro f
  have key := trig_entropy_defect (cosData h κ) N (h := h) (p := κ / (2 * (N : ℝ))) (q := 0)
    (r := 0) (by positivity) le_rfl le_rfl (fun a => cos_hamiltonian_lift N h κ a) f
  convert key using 3
  have : ((((N : ℕ) * 1 : ℕ) : ℝ)) = (N : ℝ) := by simp
  rw [this]
  field_simp
  ring

/-- Tilted XY model: `Ent(f²) ≤ (2/a₀) E(f) + (|h| + 5κ/2) N ‖f‖²`. -/
theorem xy_entropy_defect (h : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ f : ParticleH1 (tiltedXYData h κ) N,
      homogeneousEntropy (particleLaw (tiltedXYData h κ) N) (fun y => f.1 y ^ 2) ≤
        ENNReal.ofReal (2 / (4 * π ^ 2) * particleEnergy (tiltedXYData h κ) N f +
          (|h| + 5 * κ / 2) * (N : ℝ) * ∫ y, f.1 y ^ 2 ∂particleLaw (tiltedXYData h κ) N) := by
  have hN : (0 : ℝ) < (N : ℝ) := by positivity
  intro f
  have key := trig_entropy_defect (tiltedXYData h κ) N (h := h) (p := κ / (2 * (N : ℝ)))
    (q := κ / (2 * (N : ℝ))) (r := κ * (N : ℝ) / 2) (by positivity) (by positivity)
    (by positivity) (fun a => xy_hamiltonian_lift N h κ a) f
  convert key using 3
  have : ((((N : ℕ) * 1 : ℕ) : ℝ)) = (N : ℝ) := by simp
  rw [this]
  field_simp
  ring

end Models

end DGPS.FiniteN.EntropyDefects




namespace DGPS.FiniteN

open DGPS DGPS.Particle DGPS.FiniteN.Tools.WeightedSobolev EntropyDefects in
/-- FIN017: explicit `O(N)` entropy defects, with no `N²` term, for the scalar cosine model, the
tilted XY model, and (generically) any trigonometric Hamiltonian
`-h C - p C² - q S² + r` with `p, q, r ≥ 0` (in particular anisotropic ones `p ≠ q`).  The
coefficient `2/(4π²) = 2/a₀ ≤ 4/a₀` of the energy is the Haar LSI constant. -/
theorem explicit_particle_entropy_defects :
    (∀ (h κ : ℝ), 0 ≤ κ → ∀ (N : ℕ+) (f : ParticleH1 (cosData h κ) N),
      homogeneousEntropy (particleLaw (cosData h κ) N) (fun y => f.1 y ^ 2) ≤
        ENNReal.ofReal (2 / (4 * π ^ 2) * particleEnergy (cosData h κ) N f +
          (|h| + κ) * (N : ℝ) * ∫ y, f.1 y ^ 2 ∂particleLaw (cosData h κ) N)) ∧
    (∀ (h κ : ℝ), 0 ≤ κ → ∀ (N : ℕ+) (f : ParticleH1 (TiltedXY.Fin051.tiltedXYData h κ) N),
      homogeneousEntropy (particleLaw (TiltedXY.Fin051.tiltedXYData h κ) N) (fun y => f.1 y ^ 2) ≤
        ENNReal.ofReal (2 / (4 * π ^ 2) * particleEnergy (TiltedXY.Fin051.tiltedXYData h κ) N f +
          (|h| + 5 * κ / 2) * (N : ℝ) *
            ∫ y, f.1 y ^ 2 ∂particleLaw (TiltedXY.Fin051.tiltedXYData h κ) N)) ∧
    (∀ (A : InteractionData 1) (N : ℕ+) (h p q r : ℝ), 0 ≤ p → 0 ≤ q → 0 ≤ r →
      (∀ a : Fin ((N : ℕ) * 1) → ℝ,
        particleHamiltonian A N (ofT 1 N (torusLift a)) = trigF h p q r a) →
      ∀ f : ParticleH1 A N,
        homogeneousEntropy (particleLaw A N) (fun y => f.1 y ^ 2) ≤
          ENNReal.ofReal (2 / (4 * π ^ 2) * particleEnergy A N f +
            (r + 2 * (p + q) * (((N : ℕ) * 1 : ℕ) : ℝ) ^ 2 + |h| * (((N : ℕ) * 1 : ℕ) : ℝ)) *
              ∫ y, f.1 y ^ 2 ∂particleLaw A N)) :=
  ⟨fun h _ hκ N f => cos_entropy_defect N h hκ f,
   fun h _ hκ N f => xy_entropy_defect N h hκ f,
   fun A N _ _ _ _ hp hq hr hH f => trig_entropy_defect A N hp hq hr hH f⟩

end DGPS.FiniteN
