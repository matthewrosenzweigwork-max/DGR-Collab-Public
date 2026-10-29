import DGPS.Particle.Sobolev
import DGPS.Foundations.PeriodicSmoothing
import DGPS.Foundations.Entropy

/-!
# Fixed-`N` weighted Sobolev extension (FIN026)

Placement note (R5): the architecture lists FIN026 in `DGPS/FiniteN/Tools.lean`; to allow
parallel proofs of the FIN packets sharing that file it lives in this module. The public output
`DGPS.FiniteN.fixed_n_weighted_sobolev_extension` keeps its architecture name.

Transfer of the smoothing tools to the particle torus: `(𝕋^d)^N ≃ᵐ 𝕋^{N d}` via
`finProdFinEquiv`.
-/

open MeasureTheory Set Filter InformationTheory
open scoped ContDiff ENNReal Topology

namespace DGPS.FiniteN.Tools.WeightedSobolev

open DGPS

variable {d : ℕ} {N : ℕ+}

/-- Flattening index map. -/
abbrev idx (N : ℕ+) (d : ℕ) : Fin N × Fin d ≃ Fin ((N : ℕ) * d) := finProdFinEquiv

/-- `(𝕋^d)^N → 𝕋^{N d}`. -/
def toT (d : ℕ) (N : ℕ+) (x : ParticleSpace d N) : Torus ((N : ℕ) * d) :=
  fun k => x (idx N d |>.symm k).1 (idx N d |>.symm k).2

/-- `𝕋^{N d} → (𝕋^d)^N`. -/
def ofT (d : ℕ) (N : ℕ+) (y : Torus ((N : ℕ) * d)) : ParticleSpace d N :=
  fun i j => y (idx N d (i, j))

theorem ofT_toT (x : ParticleSpace d N) : ofT d N (toT d N x) = x := by
  funext i j; simp [ofT, toT]

theorem toT_ofT (y : Torus ((N : ℕ) * d)) : toT d N (ofT d N y) = y := by
  funext k; simp only [ofT, toT, Prod.mk.eta, Equiv.apply_symm_apply]

/-- The measurable equivalence. -/
def torusEquiv (d : ℕ) (N : ℕ+) : ParticleSpace d N ≃ᵐ Torus ((N : ℕ) * d) :=
  (particleUncurry d N).trans (MeasurableEquiv.piCongrLeft (fun _ => UnitAddCircle) (idx N d))

theorem torusEquiv_apply (x : ParticleSpace d N) : torusEquiv d N x = toT d N x := by
  funext k
  simp only [torusEquiv, MeasurableEquiv.trans_apply, toT]
  conv_lhs => rw [← (idx N d).apply_symm_apply k]
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp [particleUncurry_apply]

theorem measurePreserving_toT :
    MeasurePreserving (torusEquiv d N) (particleHaar d N) (haar ((N : ℕ) * d)) := by
  have h1 := measurePreserving_particleUncurry d N
  have h2 := measurePreserving_piCongrLeft (fun _ : Fin ((N : ℕ) * d) =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)) (idx N d)
  rw [haar_eq_pi_haarAddCircle]
  exact h2.comp h1

/-! ### Smooth tests and partial derivatives -/

/-- Flattening of a lifted configuration, as a continuous linear map. -/
noncomputable def flatL (d : ℕ) (N : ℕ+) :
    (Fin N → Fin d → ℝ) →L[ℝ] (Fin ((N : ℕ) * d) → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) (idx N d |>.symm k).2).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin d → ℝ)
        (idx N d |>.symm k).1)

theorem flatL_apply (y : Fin N → Fin d → ℝ) (k : Fin ((N : ℕ) * d)) :
    flatL d N y k = y (idx N d |>.symm k).1 (idx N d |>.symm k).2 := rfl

theorem toT_particleLift (y : Fin N → Fin d → ℝ) :
    toT d N (particleLift y) = torusLift (flatL d N y) := rfl

theorem isSmoothPeriodicParticle_comp_toT {ψ : Torus ((N : ℕ) * d) → ℝ} (hψ : IsSmoothPeriodic ψ) :
    IsSmoothPeriodicParticle (fun x => ψ (toT d N x)) := by
  have : ((fun x => ψ (toT d N x)) ∘ particleLift : (Fin N → Fin d → ℝ) → ℝ) =
      (ψ ∘ torusLift) ∘ flatL d N := by
    funext y; simp only [Function.comp_apply, toT_particleLift]
  unfold IsSmoothPeriodicParticle
  rw [this]
  exact hψ.comp (flatL d N).contDiff

theorem particlePartial_comp_toT {ψ : Torus ((N : ℕ) * d) → ℝ} (hψ : IsSmoothPeriodic ψ)
    (i : Fin N) (j : Fin d) (x : ParticleSpace d N) :
    particlePartial i j (fun x => ψ (toT d N x)) x = coordPartial (idx N d (i, j)) ψ (toT d N x) := by
  have hfun : ((fun x => ψ (toT d N x)) ∘ particleLift : (Fin N → Fin d → ℝ) → ℝ) =
      (ψ ∘ torusLift) ∘ flatL d N := by
    funext y; simp only [Function.comp_apply, toT_particleLift]
  unfold particlePartial coordPartial
  rw [hfun]
  have hd : DifferentiableAt ℝ (ψ ∘ torusLift) (flatL d N (fun k => SharpLSI.secT (x k))) :=
    (hψ.differentiable (by simp)).differentiableAt
  rw [fderiv_comp _ hd (flatL d N).differentiableAt, (flatL d N).fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  have h1 : flatL d N (fun k => SharpLSI.secT (x k)) = SharpLSI.secT (toT d N x) := rfl
  have h2 : flatL d N (Pi.single i (Pi.single j (1 : ℝ))) = Pi.single (idx N d (i, j)) 1 := by
    funext k
    obtain ⟨⟨a, b⟩, rfl⟩ := (idx N d).surjective k
    rw [flatL_apply, Equiv.symm_apply_apply]
    by_cases ha : a = i <;> by_cases hb : b = j <;>
      simp [(idx N d).injective.eq_iff, ha, hb]
  rw [h1, h2]

/-! ### Transfer of weak gradients and density of smooth tests -/

theorem torusEquiv_symm_apply (y : Torus ((N : ℕ) * d)) : (torusEquiv d N).symm y = ofT d N y := by
  have : torusEquiv d N (ofT d N y) = y := by rw [torusEquiv_apply, toT_ofT]
  exact (torusEquiv d N).symm_apply_eq.2 this.symm

theorem measurePreserving_ofT :
    MeasurePreserving (ofT d N) (haar ((N : ℕ) * d)) (particleHaar d N) := by
  have := (measurePreserving_toT (d := d) (N := N)).symm (torusEquiv d N)
  have h : (torusEquiv d N).symm = ofT d N := funext torusEquiv_symm_apply
  rwa [h] at this

theorem integral_comp_toT (H : Torus ((N : ℕ) * d) → ℝ) :
    ∫ y, H y ∂haar ((N : ℕ) * d) = ∫ x, H (toT d N x) ∂particleHaar d N := by
  have := (measurePreserving_toT (d := d) (N := N)).integral_comp' (g := H)
  simpa [torusEquiv_apply] using this.symm

/-- Flattening of tangent vectors. -/
noncomputable def tangentL (d : ℕ) (N : ℕ+) :
    (Fin N → Tangent d) →L[ℝ] Tangent ((N : ℕ) * d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun k => v (idx N d |>.symm k).1 (idx N d |>.symm k).2
      map_add' := fun v w => by ext k; rfl
      map_smul' := fun c v => by ext k; rfl }

theorem tangentL_apply (v : Fin N → Tangent d) (k : Fin ((N : ℕ) * d)) :
    tangentL d N v k = v (idx N d |>.symm k).1 (idx N d |>.symm k).2 := rfl

theorem isWeakGradient_comp_ofT {f : ParticleSpace d N → ℝ} {g : ParticleSpace d N → Fin N → Tangent d}
    (hg : IsParticleHaarWeakGradient N f g) :
    IsWeakGradient (fun y => f (ofT d N y)) (fun y => tangentL d N (g (ofT d N y))) where
  memLp := hg.memLp.comp_measurePreserving measurePreserving_ofT
  memLp_grad := (tangentL d N).comp_memLp'
    (hg.memLp_grad.comp_measurePreserving measurePreserving_ofT)
  ibp ψ hψ k := by
    obtain ⟨⟨i, j⟩, rfl⟩ := (idx N d).surjective k
    rw [integral_comp_toT, integral_comp_toT]
    have h := hg.ibp _ (isSmoothPeriodicParticle_comp_toT hψ) i j
    simp only [particlePartial_comp_toT hψ] at h
    simp only [ofT_toT, tangentL_apply, Equiv.symm_apply_apply]
    exact h

/-- Smooth periodic tests are dense in `H¹(m^N)`: a smooth sequence converging in `L²` together
with all partial derivatives. -/
theorem exists_smooth_particle_tendsto {f : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} (hg : IsParticleHaarWeakGradient N f g) :
    ∃ φ : ℕ → ParticleSpace d N → ℝ, (∀ n, IsSmoothPeriodicParticle (φ n)) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 (particleHaar d N)) atTop (𝓝 0) ∧
      ∀ (i : Fin N) (j : Fin d), Tendsto (fun n => eLpNorm
        (fun x => particlePartial i j (φ n) x - g x i j) 2 (particleHaar d N)) atTop (𝓝 0) := by
  have hw := isWeakGradient_comp_ofT hg
  obtain ⟨v, hv, -, h1, h2⟩ := exists_smooth_tendsto_H1 hw
  have key : ∀ F : Torus ((N : ℕ) * d) → ℝ, AEStronglyMeasurable F (haar ((N : ℕ) * d)) →
      eLpNorm (fun x => F (toT d N x)) 2 (particleHaar d N) = eLpNorm F 2 (haar ((N : ℕ) * d)) := by
    intro F hF
    have := eLpNorm_comp_measurePreserving (p := 2) hF
      (measurePreserving_toT (d := d) (N := N))
    simpa [Function.comp_def, torusEquiv_apply] using this
  refine ⟨fun n x => v n (toT d N x), fun n => isSmoothPeriodicParticle_comp_toT (hv n), ?_, ?_⟩
  · refine (h1.congr fun n => ?_)
    have hc1 : AEStronglyMeasurable (fun y => v n y - f (ofT d N y))
        (haar ((N : ℕ) * d)) :=
      ((hv n).memLp_top.mono_exponent (p := 2) le_top).aestronglyMeasurable.sub
        hw.memLp.aestronglyMeasurable
    rw [← key _ hc1]
    simp only [ofT_toT]
  · intro i j
    refine ((h2 (idx N d (i, j))).congr fun n => ?_)
    have hc : AEStronglyMeasurable (fun y => smoothGrad (v n) y (idx N d (i, j)) -
        tangentL d N (g (ofT d N y)) (idx N d (i, j))) (haar ((N : ℕ) * d)) := by
      refine ((hv n).continuous_coordPartial _).aestronglyMeasurable.sub ?_
      exact (memLp_coord_of_memLp hw.memLp_grad _).aestronglyMeasurable
    rw [← key _ hc]
    simp only [ofT_toT, smoothGrad_apply, tangentL_apply, Equiv.symm_apply_apply]
    congr 1
    funext x
    rw [particlePartial_comp_toT (hv n)]

/-! ### Generic analytic lemmas -/

section Analytic

variable {α : Type*} [MeasurableSpace α]

/-- `L²` convergence on a probability space: the squared integrals converge. -/
theorem tendsto_integral_sq_of_tendsto_eLpNorm {P : Measure α} [IsProbabilityMeasure P]
    {u : ℕ → α → ℝ} {w : α → ℝ} (hu : ∀ n, MemLp (u n) 2 P) (hw : MemLp w 2 P)
    (h : Tendsto (fun n => eLpNorm (u n - w) 2 P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, u n x ^ 2 ∂P) atTop (𝓝 (∫ x, w x ^ 2 ∂P)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hsq : ∀ v : α → ℝ, ∀ hv : MemLp v 2 P, ∫ x, v x ^ 2 ∂P = ‖hv.toLp v‖ ^ 2 := by
    intro v hv
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hv.coeFn_toLp] with x hx
    rw [hx]
    simp [sq]
  have hd : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hw.toLp w)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have : ∀ n, dist ((hu n).toLp (u n)) (hw.toLp w) = (eLpNorm (u n - w) 2 P).toReal := by
      intro n
      rw [dist_eq_norm, ← MemLp.toLp_sub (hu n) hw, Lp.norm_toLp]
    simp_rw [this]
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have := ((continuous_norm.tendsto _).comp hd).pow 2
  simpa only [Function.comp_def, ← hsq] using this

/-- `L²` convergence on a probability space: the integrals converge. -/
theorem tendsto_integral_of_tendsto_eLpNorm_two {P : Measure α} [IsProbabilityMeasure P]
    {u : ℕ → α → ℝ} {w : α → ℝ} (hu : ∀ n, MemLp (u n) 2 P)
    (h : Tendsto (fun n => eLpNorm (u n - w) 2 P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, u n x ∂P) atTop (𝓝 (∫ x, w x ∂P)) := by
  refine tendsto_integral_of_L1' w (Eventually.of_forall fun n => (hu n).integrable one_le_two) ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le)
    (fun n => ?_)
  exact eLpNorm_le_eLpNorm_of_exponent_le one_le_two

/-- Lower semicontinuity of the homogeneous entropy along a.e. convergence with convergent
integrals (Fatou). -/
theorem homogeneousEntropy_le_of_tendsto {P : Measure α} {v : ℕ → α → ℝ} {w : α → ℝ}
    (hvm : ∀ n, AEMeasurable (v n) P)
    (hae : ∀ᵐ x ∂P, Tendsto (fun k => v k x) atTop (𝓝 (w x)))
    (hint : Tendsto (fun k => ∫ x, v k x ∂P) atTop (𝓝 (∫ x, w x ∂P)))
    (hw0 : 0 ≤ ∫ x, w x ∂P)
    {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞} (hb : Tendsto b atTop (𝓝 B))
    (hle : ∀ k, homogeneousEntropy P (v k) ≤ b k) :
    homogeneousEntropy P w ≤ B := by
  rcases hw0.eq_or_lt with h0 | hpos
  · rw [homogeneousEntropy_of_integral_eq_zero h0.symm]; exact zero_le
  set a := ∫ x, w x ∂P with ha
  set ak : ℕ → ℝ := fun k => ∫ x, v k x ∂P with hak
  have hne : ∀ᶠ k in atTop, ak k ≠ 0 := hint.eventually_ne hpos.ne'
  set F : ℕ → α → ℝ≥0∞ := fun k x => ENNReal.ofReal (entropyIntegrand (ak k) (v k x)) with hF
  have hFm : ∀ k, AEMeasurable (F k) P := fun k => by
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    unfold entropyIntegrand
    have := hvm k
    fun_prop
  have hlim : ∀ᵐ x ∂P, Tendsto (fun k => F k x) atTop
      (𝓝 (ENNReal.ofReal (entropyIntegrand a (w x)))) := by
    filter_upwards [hae] with x hx
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    have h1 : Tendsto (fun k => ak k * klFun (v k x / ak k)) atTop (𝓝 (a * klFun (w x / a))) :=
      hint.mul ((continuous_klFun.tendsto _).comp (hx.div hint hpos.ne'))
    rw [entropyIntegrand_eq_mul_klFun hpos.ne']
    refine h1.congr' ?_
    filter_upwards [hne] with k hk
    rw [entropyIntegrand_eq_mul_klFun hk]
  have hEq : homogeneousEntropy P w = ∫⁻ x, liminf (fun k => F k x) atTop ∂P := by
    rw [homogeneousEntropy_of_integral_ne_zero hpos.ne']
    refine lintegral_congr_ae ?_
    filter_upwards [hlim] with x hx
    exact hx.liminf_eq.symm
  rw [hEq]
  refine (lintegral_liminf_le' hFm).trans ?_
  rw [← hb.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [hne] with k hk
  have := hle k
  rwa [homogeneousEntropy_of_integral_ne_zero hk] at this

end Analytic

/-! ### Smooth approximation in `H¹(P_N)` -/

variable (A : InteractionData d)

/-- The Gibbs energy `∫ ∑ᵢⱼ (∂ᵢⱼ φ)² dP_N` of a smooth periodic test, computed with the classical
partial derivatives. -/
noncomputable def particleSmoothEnergy (φ : ParticleSpace d N → ℝ) : ℝ :=
  ∫ x, ∑ i, ∑ j, particlePartial i j φ x ^ 2 ∂particleLaw A N

theorem eLpNorm_particleLaw_le :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ h : ParticleSpace d N → ℝ,
      AEStronglyMeasurable h (particleHaar d N) → eLpNorm h 2 (particleLaw A N) ≤ K * eLpNorm h 2 (particleHaar d N) := by
  obtain ⟨c, C, hc, hcC, hb⟩ := DGPS.Particle.particleDensity_bounded A N
  have h1 : particleLaw A N ≤ ENNReal.ofReal C • particleHaar d N := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [DGPS.particleLaw, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul]
    calc ∫⁻ x in s, ENNReal.ofReal (particleDensity A N x) ∂particleHaar d N
        ≤ ∫⁻ _ in s, ENNReal.ofReal C ∂particleHaar d N :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hb x).2
      _ = _ := by rw [setLIntegral_const]
  refine ⟨ENNReal.ofReal C ^ ((1 / (2 : ℝ≥0∞)).toReal), ?_, fun h hh => ?_⟩
  · exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  · refine (eLpNorm_mono_measure h h1).trans ?_
    rw [eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ hh, smul_eq_mul]

theorem tendsto_eLpNorm_particleLaw {u : ℕ → ParticleSpace d N → ℝ} {w : ParticleSpace d N → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (fun x => u n x - w x) (particleHaar d N))
    (h : Tendsto (fun n => eLpNorm (fun x => u n x - w x) 2 (particleHaar d N)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n - w) 2 (particleLaw A N)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hle⟩ := eLpNorm_particleLaw_le A (N := N)
  have h2 : Tendsto (fun n => K * eLpNorm (fun x => u n x - w x) 2 (particleHaar d N)) atTop
      (𝓝 (K * 0)) := ENNReal.Tendsto.const_mul h (Or.inr hK)
  rw [mul_zero] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun n => zero_le)
    (fun n => hle _ (hm n))

theorem memLp_two_law_of_smooth {N : ℕ+} {φ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) : MemLp φ 2 (particleLaw A N) :=
  (DGPS.Particle.memLp_particleLaw_iff A N).2 (hφ.memLp_top.mono_exponent (p := 2) le_top)

theorem memLp_two_law_partial_of_smooth {φ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) (i : Fin N) (j : Fin d) :
    MemLp (particlePartial i j φ) 2 (particleLaw A N) :=
  (DGPS.Particle.memLp_particleLaw_iff A N).2
    ((hφ.memLp_top_particlePartial i j).mono_exponent (p := 2) le_top)

theorem integral_sum_sq {μ : Measure (ParticleSpace d N)} {u : Fin N → Fin d → ParticleSpace d N → ℝ}
    (hu : ∀ i j, MemLp (u i j) 2 μ) :
    ∫ x, ∑ i, ∑ j, u i j x ^ 2 ∂μ = ∑ i, ∑ j, ∫ x, u i j x ^ 2 ∂μ := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hu i j).integrable_sq)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hu i j).integrable_sq)]

theorem exists_smooth_approx (f : ParticleH1 A N) :
    ∃ φ : ℕ → ParticleSpace d N → ℝ, (∀ n, IsSmoothPeriodicParticle (φ n)) ∧
      Tendsto (fun n => eLpNorm (φ n - f.1) 2 (particleLaw A N)) atTop (𝓝 0) ∧
      Tendsto (fun n => particleSmoothEnergy A (φ n)) atTop (𝓝 (particleEnergy A N f)) := by
  have hg := isParticleWeakGradient_particleWeakGradient f
  have hgH := (isParticleWeakGradient_iff A N _ _).1 hg
  obtain ⟨φ, hφ, h1, h2⟩ := exists_smooth_particle_tendsto hgH
  refine ⟨φ, hφ, tendsto_eLpNorm_particleLaw A
    (fun n => (hφ n).memLp_top.aestronglyMeasurable.sub hgH.memLp.aestronglyMeasurable) h1, ?_⟩
  rw [particleEnergy_eq]
  have hgc : ∀ i j, MemLp (fun x => particleWeakGradient f x i j) 2 (particleLaw A N) :=
    fun i j => memLp_particleCoord hg.memLp_grad i j
  rw [integral_sum_sq hgc]
  have e : ∀ n, particleSmoothEnergy A (φ n) =
      ∑ i, ∑ j, ∫ x, particlePartial i j (φ n) x ^ 2 ∂particleLaw A N := fun n =>
    integral_sum_sq (fun i j => memLp_two_law_partial_of_smooth A (hφ n) i j)
  simp_rw [e]
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  refine tendsto_integral_sq_of_tendsto_eLpNorm (fun n => memLp_two_law_partial_of_smooth A (hφ n) i j)
    (hgc i j) ?_
  exact tendsto_eLpNorm_particleLaw A
    (fun n => ((hφ n).memLp_top_particlePartial i j).aestronglyMeasurable.sub
      (memLp_particleCoord hgH.memLp_grad i j).aestronglyMeasurable) (h2 i j)

theorem memLp_two_law_of_particleH1 (f : ParticleH1 A N) : MemLp f.1 2 (particleLaw A N) :=
  (isParticleWeakGradient_particleWeakGradient f).memLp

/-- Entropy extension along a smooth approximation. -/
theorem homogeneousEntropy_sq_le_of_approx {φ : ℕ → ParticleSpace d N → ℝ}
    (hφ : ∀ n, IsSmoothPeriodicParticle (φ n)) (f : ParticleH1 A N)
    (hconv : Tendsto (fun n => eLpNorm (φ n - f.1) 2 (particleLaw A N)) atTop (𝓝 0))
    {x : ℕ → ℝ} {X : ℝ} (hx : Tendsto x atTop (𝓝 X))
    (hle : ∀ n, homogeneousEntropy (particleLaw A N) (fun y => φ n y ^ 2)
      ≤ ENNReal.ofReal (x n)) :
    homogeneousEntropy (particleLaw A N) (fun y => f.1 y ^ 2) ≤ ENNReal.ofReal X := by
  have hmem := fun n => memLp_two_law_of_smooth A (hφ n)
  have hf := memLp_two_law_of_particleH1 A f
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero hconv).exists_seq_tendsto_ae
  refine homogeneousEntropy_le_of_tendsto (v := fun k y => φ (ns k) y ^ 2)
    (b := fun k => ENNReal.ofReal (x (ns k))) (B := ENNReal.ofReal X)
    (fun k => (hmem (ns k)).aestronglyMeasurable.aemeasurable.pow_const 2) ?_ ?_
    (integral_nonneg fun y => sq_nonneg _) ?_ (fun k => hle (ns k))
  · filter_upwards [hae] with y hy using hy.pow 2
  · exact (tendsto_integral_sq_of_tendsto_eLpNorm hmem hf hconv).comp hns.tendsto_atTop
  · exact (ENNReal.continuous_ofReal.tendsto _).comp (hx.comp hns.tendsto_atTop)

end DGPS.FiniteN.Tools.WeightedSobolev

namespace DGPS.FiniteN

open DGPS DGPS.FiniteN.Tools.WeightedSobolev

/-- **FIN026 (fixed-`N` weighted Sobolev extension).** For a fixed `N` and the smooth positive
Gibbs density, `H¹(P_N) = H¹(m^N)` as sets, and any inequality proved for all smooth periodic
tests extends, with the same constants, to every `f ∈ H¹(P_N)`: entropy-energy `Ent(f²) ≤ K E(f)`,
Poincaré `Var(f) ≤ K E(f)`, and the defective entropy inequality
`Ent(f²) ≤ α E(f) + β ‖f‖₂²`. No uniformity in `N` is asserted. -/
theorem fixed_n_weighted_sobolev_extension {d : ℕ} (A : InteractionData d) (N : ℕ+) :
    (∀ f : ParticleSpace d N → ℝ, MemParticleH1 A N f ↔ MemParticleHaarH1 N f) ∧
    (∀ K : ℝ, (∀ φ : ParticleSpace d N → ℝ, IsSmoothPeriodicParticle φ →
        homogeneousEntropy (particleLaw A N) (fun y => φ y ^ 2)
          ≤ ENNReal.ofReal (K * particleSmoothEnergy A φ)) →
      ∀ f : ParticleH1 A N, homogeneousEntropy (particleLaw A N) (fun y => f.1 y ^ 2)
          ≤ ENNReal.ofReal (K * particleEnergy A N f)) ∧
    (∀ K : ℝ, (∀ φ : ParticleSpace d N → ℝ, IsSmoothPeriodicParticle φ →
        ProbabilityTheory.variance φ (particleLaw A N) ≤ K * particleSmoothEnergy A φ) →
      ∀ f : ParticleH1 A N,
        ProbabilityTheory.variance f.1 (particleLaw A N) ≤ K * particleEnergy A N f) ∧
    (∀ α β : ℝ, (∀ φ : ParticleSpace d N → ℝ, IsSmoothPeriodicParticle φ →
        homogeneousEntropy (particleLaw A N) (fun y => φ y ^ 2)
          ≤ ENNReal.ofReal (α * particleSmoothEnergy A φ
            + β * ∫ y, φ y ^ 2 ∂particleLaw A N)) →
      ∀ f : ParticleH1 A N, homogeneousEntropy (particleLaw A N) (fun y => f.1 y ^ 2)
          ≤ ENNReal.ofReal (α * particleEnergy A N f + β * ∫ y, f.1 y ^ 2 ∂particleLaw A N)) := by
  refine ⟨memParticleH1_iff A N, ?_, ?_, ?_⟩
  · intro K hK f
    obtain ⟨φ, hφ, h1, h2⟩ := exists_smooth_approx A f
    exact homogeneousEntropy_sq_le_of_approx A hφ f h1 (h2.const_mul K) (fun n => hK _ (hφ n))
  · intro K hK f
    obtain ⟨φ, hφ, h1, h2⟩ := exists_smooth_approx A f
    have hmem := fun n => memLp_two_law_of_smooth A (hφ n)
    have hf := memLp_two_law_of_particleH1 A f
    have t1 := tendsto_integral_sq_of_tendsto_eLpNorm hmem hf h1
    have t2 := (tendsto_integral_of_tendsto_eLpNorm_two hmem h1).pow 2
    have tv : Tendsto (fun n => ProbabilityTheory.variance (φ n) (particleLaw A N)) atTop
        (𝓝 (ProbabilityTheory.variance f.1 (particleLaw A N))) := by
      rw [ProbabilityTheory.variance_eq_sub hf]
      have : ∀ n, ProbabilityTheory.variance (φ n) (particleLaw A N) =
          ∫ y, φ n y ^ 2 ∂particleLaw A N - (∫ y, φ n y ∂particleLaw A N) ^ 2 := fun n => by
        rw [ProbabilityTheory.variance_eq_sub (hmem n)]
        rfl
      simp_rw [this]
      exact t1.sub t2
    exact le_of_tendsto_of_tendsto' tv (h2.const_mul K) fun n => hK _ (hφ n)
  · intro α β hK f
    obtain ⟨φ, hφ, h1, h2⟩ := exists_smooth_approx A f
    have hmem := fun n => memLp_two_law_of_smooth A (hφ n)
    have hf := memLp_two_law_of_particleH1 A f
    have t1 := tendsto_integral_sq_of_tendsto_eLpNorm hmem hf h1
    exact homogeneousEntropy_sq_le_of_approx A hφ f h1
      ((h2.const_mul α).add (t1.const_mul β)) (fun n => hK _ (hφ n))

end DGPS.FiniteN
