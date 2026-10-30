import DGPS.Lipschitz.T01ActualRankReplacement
import DGPS.Lipschitz.T01CenteredDualGenerator
import DGPS.Lipschitz.T01ParticleReferenceBridge
import FullLabeledLSI.Paper.Prop23ReplaceB
import SharpSymmetricLSI.Paper.FormLiminfS7
import SharpSymmetricLSI.Paper.FormLiminfS16b

/-! The actual centered force in the cylinder generator and its finite-rank approximation. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace DGPS.Lipschitz
open DGPS.Particle SharpLSI SharpLSI.FL KernelApproximation
variable {d : ℕ}

/-- The residual's chosen flat gradient is the actual centered gradient minus the finite-rank one. -/
theorem t01_centered_residual_gradient_ae (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    {e : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (e j ∘ liftT))
    (F : FiniteRankApprox A.W (μ : Measure (Torus d)) e) (R : ℕ) (N : ℕ+)
    {gU : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) gU) :
    ∀ᵐ X ∂particleLaw A N, ∀ l k,
      weakGradC (fun Y => centeredParticlePotential A μ N Y - URN F R N Y) X l k =
        gU X l k - gradURN F e R N X l k := by
  have hup : (μ : Measure (Torus d)) ≤ ENNReal.ofReal (frozenGibbs A μ).upper • haar d := by
    rw [← hfix]
    exact (frozenGibbs A μ).measure_le_smul_haar
  have hR := isWeakGrad_URN F hφ (fun _ => EventuallyEq.rfl) R N.pos
  have hD := isWeakGrad_sub_loc (legacy_isWeakGrad_of_particle hU) hR
  have hh := (Spectral.ac_map_flat (N := (N : ℕ)) hup).ae_le (weakGrad_ae_eq hD)
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d))
      (QN (μ : Measure (Torus d)) N) ((QN (μ : Measure (Torus d)) N).map flat) :=
    ⟨measurable_flat, rfl⟩
  have hQ := hmp.quasiMeasurePreserving.ae hh
  have hac : particleLaw A N ≪ QN (μ : Measure (Torus d)) N := by
    change particleLaw A N ≪ Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))
    rw [particleLaw_eq_centered_reference A μ hfix N]
    exact withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le hQ] with X hX
  intro l k
  exact congrFun hX (l, k)

/-- The finite-rank force polynomial is the pairing with its exact finite-rank weak gradient. -/
theorem t01_finite_rank_force_algebra {W : Torus d → Torus d → ℝ}
    {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
    (F : FiniteRankApprox W μ e) (R : ℕ) (N : ℕ) (X : Config N d) (i : ℕ) :
    (∑ p ∈ F.s R, ∑ q ∈ F.s R, F.a R p q * fluct e N q X * mobA e N X p i) =
      (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, ∑ k,
        gradURN F e R N X l k * cgrad (e (i + 1)) (X l) k := by
  let r : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ))
  let Sq : ℕ → ℝ := fun q => ∑ l, e (q + 1) (X l)
  let G : ℕ → Fin N → Fin d → ℝ := fun p l k => cgrad (e (p + 1)) (X l) k
  let c : Fin N → Fin d → ℝ := fun l k => cgrad (e (i + 1)) (X l) k
  have hr : r * r = (N : ℝ)⁻¹ := prop23_rpow_half_mul_self N
  have hgrad : ∀ l k, gradURN F e R N X l k =
      (N : ℝ)⁻¹ * ∑ p ∈ F.s R, ∑ q ∈ F.s R, F.a R p q * G p l k * Sq q := by
    intro l k
    change r * (∑ p ∈ F.s R, (∑ q ∈ F.s R, F.a R p q * (r * Sq q)) * G p l k) = _
    rw [← hr]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have h := finRank_force_alg (F.s R) (F.a R) G Sq c r (N : ℝ)⁻¹
  change (∑ p ∈ F.s R, ∑ q ∈ F.s R,
    F.a R p q * (r * Sq q) * ((N : ℝ)⁻¹ * ∑ l, ∑ k, G p l k * c l k)) = _
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro k hk
  rw [hgrad]

/-- The actual centered cylinder-force error is controlled by the genuine residual force energy. -/
theorem t01_centered_dualD_approx_sq (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    {e : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (e j ∘ liftT))
    (F : FiniteRankApprox A.W (μ : Measure (Torus d)) e) (R : ℕ) (N : ℕ+)
    {gU : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) gU)
    (i : ℕ) {Ci : ℝ} (hCi : ∀ y k, |cgrad (e (i + 1)) y k| ≤ Ci) :
    ∀ᵐ X ∂particleLaw A N,
      ((Real.sqrt (N : ℝ))⁻¹ * ∑ l, inner ℝ (gU X l) (smoothGrad (e (i + 1)) (X l)) -
        ∑ p ∈ F.s R, ∑ q ∈ F.s R, F.a R p q * fluct e N q X * mobA e N X p i) ^ 2 ≤
      d * Ci ^ 2 * gradSqC
        (fun Y => centeredParticlePotential A μ N Y - URN F R N Y) X := by
  have hscale : (Real.sqrt (N : ℝ))⁻¹ = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]
  have hcgrad : ∀ (u : Torus d → ℝ) x k, smoothGrad u x k = cgrad u x k :=
    fun _ _ _ => rfl
  filter_upwards [t01_centered_residual_gradient_ae A μ hfix hφ F R N hU] with X hX
  let u : Fin N → Fin d → ℝ := fun l k =>
    weakGradC (fun Y => centeredParticlePotential A μ N Y - URN F R N Y) X l k
  let c : Fin N → Fin d → ℝ := fun l k => cgrad (e (i + 1)) (X l) k
  have hkey : (Real.sqrt (N : ℝ))⁻¹ *
      ∑ l, inner ℝ (gU X l) (smoothGrad (e (i + 1)) (X l)) -
      ∑ p ∈ F.s R, ∑ q ∈ F.s R, F.a R p q * fluct e N q X * mobA e N X p i =
      (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, ∑ k, u l k * c l k := by
    rw [hscale, t01_finite_rank_force_algebra]
    simp only [dg_inner, hcgrad]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    change gU X l k * c l k - gradURN F e R N X l k * c l k = u l k * c l k
    rw [show u l k = gU X l k - gradURN F e R N X l k from hX l k]
    ring
  rw [hkey]
  exact sq_scaled_sum_le N.pos u c (fun l k => hCi (X l) k)

/-- The actual force energy controls pairings with an L2 observable and bounded cylinder derivative. -/
theorem t01_force_pairing_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f ψ Δ G : Ω → ℝ)
    (hf : MemLp f 2 P) {B K c δ : ℝ} (hf2 : ∫ x, f x ^ 2 ∂P ≤ B)
    (hK0 : 0 ≤ K) (hψ : ∀ x, |ψ x| ≤ K) (hc : 0 ≤ c) (hδ : 0 < δ)
    (hG0 : ∀ x, 0 ≤ G x) (hΔ : ∀ᵐ x ∂P, Δ x ^ 2 ≤ c * G x)
    (hG : ∫⁻ x, ENNReal.ofReal (G x) ∂P ≤ ENNReal.ofReal δ)
    (hint : Integrable (fun x => |f x * ψ x * Δ x|) P) :
    ∫ x, |f x * ψ x * Δ x| ∂P ≤ K / 2 * (B + c) * Real.sqrt δ := by
  let t := Real.sqrt δ
  have ht : 0 < t := Real.sqrt_pos.2 hδ
  have hB0 : 0 ≤ B := (integral_nonneg fun x => sq_nonneg _).trans hf2
  have hbound0 : 0 ≤ K / 2 * (B + c) * t := by positivity
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => abs_nonneg _)
    hint.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hbound0 ?_
  have hpt : ∀ᵐ x ∂P, ENNReal.ofReal |f x * ψ x * Δ x| ≤
      ENNReal.ofReal (K / 2 * t * f x ^ 2) + ENNReal.ofReal (K / 2 / t * c) *
        ENNReal.ofReal (G x) := by
    filter_upwards [hΔ] with x hx
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (mul_nonneg (by positivity) (hG0 x))]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : |f x * ψ x * Δ x| ≤ K * |f x * Δ x| := by
      rw [show f x * ψ x * Δ x = ψ x * (f x * Δ x) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_right (hψ x) (abs_nonneg _)
    have h2 := SharpLSI.abs_mul_le_amgm (x := f x) (y := Δ x) ht
    have h3 : Δ x ^ 2 / t ≤ c * G x / t := div_le_div_of_nonneg_right hx ht.le
    calc |f x * ψ x * Δ x| ≤ K * ((t * f x ^ 2 + Δ x ^ 2 / t) / 2) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 hK0)
      _ ≤ K * ((t * f x ^ 2 + c * G x / t) / 2) := by gcongr
      _ = K / 2 * t * f x ^ 2 + K / 2 / t * c * G x := by ring
  refine (lintegral_mono_ae hpt).trans ?_
  have hfm : AEMeasurable (fun x => ENNReal.ofReal (K / 2 * t * f x ^ 2)) P :=
    (hf.aestronglyMeasurable.aemeasurable.pow_const 2 |>.const_mul _).ennreal_ofReal
  rw [lintegral_add_left' hfm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hf2' : ∫⁻ x, ENNReal.ofReal (K / 2 * t * f x ^ 2) ∂P ≤
      ENNReal.ofReal (K / 2 * t * B) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrable_sq.const_mul _)
      (Eventually.of_forall fun x => by positivity), integral_const_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hf2 (by positivity))
  have hG' : ENNReal.ofReal (K / 2 / t * c) * ∫⁻ x, ENNReal.ofReal (G x) ∂P ≤
      ENNReal.ofReal (K / 2 / t * c * δ) := by
    calc _ ≤ ENNReal.ofReal (K / 2 / t * c) * ENNReal.ofReal δ := mul_le_mul_right hG _
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  refine (add_le_add hf2' hG').trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have htt : t * t = δ := Real.mul_self_sqrt hδ.le
  field_simp
  rw [← htt]
  have hroot : Real.sqrt (t * t) = t := by
    simpa only [pow_two] using Real.sqrt_sq ht.le
  rw [hroot]
  ring

/-- The actual residual-force threshold implies the centered cylinder-force pairing threshold. -/
theorem t01_centered_force_pairing_threshold (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    {e : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (e j ∘ liftT))
    (F : FiniteRankApprox A.W (μ : Measure (Torus d)) e)
    (gU : (N : ℕ+) → ParticleSpace d N → Fin N → Tangent d)
    (hU : ∀ N, IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) (gU N))
    (hForce : ∀ η : ℝ, 0 < η → ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ᶠ N : ℕ+ in atTop,
      (∫⁻ X, ENNReal.ofReal (gradSqC
        (fun Y => centeredParticlePotential A μ N Y - URN F R N Y) X)
          ∂particleLaw A N) ≤ ENNReal.ofReal η)
    {Ns : ℕ → ℕ+} (hNs : Tendsto (fun k => (Ns k : ℕ)) atTop atTop)
    (f ψ : (k : ℕ) → ParticleSpace d (Ns k) → ℝ)
    (hf : ∀ k, MemLp (f k) 2 (particleLaw A (Ns k))) {B K : ℝ}
    (hf2 : ∀ k, ∫ X, f k X ^ 2 ∂particleLaw A (Ns k) ≤ B)
    (hK0 : 0 ≤ K) (hψ : ∀ k X, |ψ k X| ≤ K) (i : ℕ)
    (hInt : ∀ R k, Integrable (fun X => |f k X * ψ k X *
      ((Real.sqrt (Ns k : ℝ))⁻¹ * ∑ l,
        inner ℝ (gU (Ns k) X l) (smoothGrad (e (i + 1)) (X l)) -
        ∑ p ∈ F.s R, ∑ q ∈ F.s R,
          F.a R p q * fluct e (Ns k) q X * mobA e (Ns k) X p i)|)
      (particleLaw A (Ns k))) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ᶠ k in atTop,
      (∫ X, |f k X * ψ k X *
        ((Real.sqrt (Ns k : ℝ))⁻¹ * ∑ l,
          inner ℝ (gU (Ns k) X l) (smoothGrad (e (i + 1)) (X l)) -
          ∑ p ∈ F.s R, ∑ q ∈ F.s R,
            F.a R p q * fluct e (Ns k) q X * mobA e (Ns k) X p i)|
        ∂particleLaw A (Ns k)) ≤ ε := by
  obtain ⟨Ci, hCi⟩ := exists_bound_cgrad (hφ (i + 1))
  have hNs' : Tendsto Ns atTop atTop := tendsto_atTop.2 fun n =>
    (hNs.eventually (eventually_ge_atTop (n : ℕ))).mono fun k hk => hk
  intro ε hε
  let κ : ℝ := K / 2 * (B + d * Ci ^ 2)
  let r : ℝ := ε / (|κ| + 1)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hδ : 0 < r ^ 2 := pow_pos hr 2
  obtain ⟨R₀, hR₀⟩ := hForce (r ^ 2) hδ
  refine ⟨R₀, fun R hR => ?_⟩
  filter_upwards [hNs'.eventually (hR₀ R hR)] with k hk
  let Δ : ParticleSpace d (Ns k) → ℝ := fun X =>
    (Real.sqrt (Ns k : ℝ))⁻¹ * ∑ l,
      inner ℝ (gU (Ns k) X l) (smoothGrad (e (i + 1)) (X l)) -
      ∑ p ∈ F.s R, ∑ q ∈ F.s R,
        F.a R p q * fluct e (Ns k) q X * mobA e (Ns k) X p i
  let G : ParticleSpace d (Ns k) → ℝ := fun X =>
    gradSqC (fun Y => centeredParticlePotential A μ (Ns k) Y - URN F R (Ns k) Y) X
  have hG0 : ∀ X, 0 ≤ G X := fun X =>
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hΔ : ∀ᵐ X ∂particleLaw A (Ns k), Δ X ^ 2 ≤ (d * Ci ^ 2) * G X :=
    t01_centered_dualD_approx_sq A μ hfix hφ F R (Ns k) (hU (Ns k)) i hCi
  have hpair := t01_force_pairing_bound (particleLaw A (Ns k)) (f k) (ψ k) Δ G
    (hf k) (hf2 k) hK0 (hψ k) (by positivity : 0 ≤ (d : ℝ) * Ci ^ 2) hδ hG0 hΔ hk (hInt R k)
  have hsqrt : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  change _ ≤ κ * Real.sqrt (r ^ 2) at hpair
  refine hpair.trans ?_
  rw [hsqrt]
  calc κ * r ≤ |κ| * r := mul_le_mul_of_nonneg_right (le_abs_self _) hr.le
    _ ≤ ε := by
      have ht : |κ| * r < (|κ| + 1) * r :=
        mul_lt_mul_of_pos_right (by linarith) hr
      have heq : (|κ| + 1) * r = ε := by dsimp only [r]; field_simp
      exact (ht.trans_eq heq).le

end DGPS.Lipschitz
