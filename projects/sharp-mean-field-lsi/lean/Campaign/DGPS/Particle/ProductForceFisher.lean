import DGPS.Particle.ProductForceVariance
import DGPS.Particle.Contractions
import DGPS.Analysis.RelativeFisher
import DGPS.Particle.DiagonalForce
import DGPS.Foundations.SobolevEmbedding
import DGPS.Foundations.SobolevCalculus

/-!
# Product force: relative Fisher information

The product law `ν_N = ⊗ᵢ ρ_{σ i}` has density `f² ` against the particle Gibbs measure `P_N` with
`f = ∏ᵢ √ρ_{σ i} · √Z · exp (H/2)`.  We compute its weak gradient, identify the campaign's
`ordinaryRelativeFisher` of `ν_N` against `P_N` (after the identification `(𝕋^d)^N ≃ 𝕋^{Nd}`) with
the explicit score functional `∫ ∑ᵢ |scoreᵢ|² dν_N`, remove the positivity hypothesis of
`product_force_conditional_variance_and_fisher_limit` (zero sets of `√ρ_s` carry no mass and the
weak gradient vanishes there), and restate the conclusion with `I(ν_N | P_N)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace DGPS.Particle.ProductForceFisher

open DGPS DGPS.Lipschitz DGPS.Particle DGPS.Particle.ProductRecovery
  DGPS.Particle.ProductForceVariance

variable {d : ℕ} {N : ℕ+}

theorem memLp_prod_eval {b : Fin N → Torus d → ℝ} (hb : ∀ k, MemLp (b k) 2 (haar d)) :
    MemLp (fun x : ParticleSpace d N => ∏ k, b k (x k)) 2 (particleHaar d N) := by
  have hm : AEStronglyMeasurable (fun x : ParticleSpace d N => ∏ k, b k (x k))
      (particleHaar d N) := by
    refine Finset.aestronglyMeasurable_fun_prod (f := fun k (x : ParticleSpace d N) => b k (x k)) _ fun k _ => ?_
    exact (hb k).aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_eval (fun _ : Fin N => haar d) k).quasiMeasurePreserving
  rw [memLp_two_iff_integrable_sq hm]
  have : (fun x : ParticleSpace d N => (∏ k, b k (x k)) ^ 2) = fun x => ∏ k, (b k (x k)) ^ 2 := by
    funext x; rw [Finset.prod_pow]
  rw [this]
  exact Integrable.fintype_prod (μ := fun _ => haar d) (f := fun k y => (b k y) ^ 2)
    (fun k => (hb k).integrable_sq)


theorem prod_update_split (a : Fin N → Torus d → ℝ) (x : ParticleSpace d N) (i : Fin N)
    (t : Torus d) :
    ∏ k, a k (Function.update x i t k) = a i t * ∏ k ∈ Finset.univ.erase i, a k (x k) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem prod_split (a : Fin N → Torus d → ℝ) (x : ParticleSpace d N) (i : Fin N) :
    ∏ k, a k (x k) = a i (x i) * ∏ k ∈ Finset.univ.erase i, a k (x k) := by
  rw [Finset.mul_prod_erase Finset.univ (fun k => a k (x k)) (Finset.mem_univ i)]

theorem isParticleHaarWeakGradient_prod (a : Fin N → Torus d → ℝ) (G : Fin N → Torus d → Tangent d)
    (h : ∀ k, IsWeakGradient (a k) (G k)) :
    IsParticleHaarWeakGradient N (fun x => ∏ k, a k (x k))
      (fun x i => (∏ k ∈ Finset.univ.erase i, a k (x k)) • G i (x i)) := by
  classical
  have hu : MemLp (fun x : ParticleSpace d N => ∏ k, a k (x k)) 2 (particleHaar d N) :=
    memLp_prod_eval fun k => (h k).memLp
  have hg : ∀ (i : Fin N) (l : Fin d), MemLp
      (fun x : ParticleSpace d N => (∏ k ∈ Finset.univ.erase i, a k (x k)) * G i (x i) l) 2
      (particleHaar d N) := by
    intro i l
    have := memLp_prod_eval (N := N)
      (b := fun k y => if k = i then G i y l else a k y) (fun k => by
        by_cases hk : k = i
        · subst hk; simpa using memLp_coord (h k).memLp_grad l
        · simpa only [hk, ite_false] using (h k).memLp)
    refine (this.ae_eq (Eventually.of_forall fun x => ?_))
    rw [prod_split (fun k y => if k = i then G i y l else a k y) x i]
    simp only [ite_true]
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by simp [Finset.ne_of_mem_erase hk]
  refine ⟨hu, ?_, fun φ hφ i l => ?_⟩
  · rw [memLp_pi_iff]
    intro i
    rw [memLp_piLp_iff]
    intro l
    simpa using hg i l
  · refine df_ibp_of_slice (g := fun x i => (∏ k ∈ Finset.univ.erase i, a k (x k)) • G i (x i))
      i l hu (by simpa using hg i l) (fun x => ?_) hφ
    set c := ∏ k ∈ Finset.univ.erase i, a k (x k) with hc
    refine ((h i).smul c).congr_ae (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
    · simp only [prod_update_split a x i t]; ring
    · have : ∏ k ∈ Finset.univ.erase i, a k (Function.update x i t k) = c :=
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp [this]


theorem isParticleHaarWeakGradient_mul_bdd {u w : ParticleSpace d N → ℝ}
    {gu gw : ParticleSpace d N → Fin N → Tangent d}
    (hu : IsParticleHaarWeakGradient N u gu) (hw : IsParticleHaarWeakGradient N w gw)
    (hub : MemLp u ⊤ (particleHaar d N)) (hwb : MemLp w ⊤ (particleHaar d N)) :
    IsParticleHaarWeakGradient N (fun x => u x * w x) (fun x => w x • gu x + u x • gw x) := by
  have hub' : MemLp (u ∘ (particleTorusEquiv d N).symm) ⊤ (haar ((N : ℕ) * d)) :=
    memLp_comp_particleTorusEquiv_symm.2 hub
  have hwb' : MemLp (w ∘ (particleTorusEquiv d N).symm) ⊤ (haar ((N : ℕ) * d)) :=
    memLp_comp_particleTorusEquiv_symm.2 hwb
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hu hw ⊢
  have h := weak_product_rule_L1 hu hw
  rw [particleGradT_add, particleGradT_smul, particleGradT_smul]
  refine isWeakGradient_iff_isWeakGradientLp.2 ⟨?_, ?_, h.ibp⟩
  · exact hu.memLp.mul (r := 2) hwb'
  · exact (hwb'.smul (r := 2) hu.memLp_grad).add (hub'.smul (r := 2) hw.memLp_grad)


theorem memLp_top_prod_eval {b : Fin N → Torus d → ℝ}
    (hm : ∀ k, AEStronglyMeasurable (b k) (haar d))
    (hb : ∀ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂haar d, |b k x| ≤ B) :
    MemLp (fun x : ParticleSpace d N => ∏ k, b k (x k)) ⊤ (particleHaar d N) := by
  choose B hB0 hB using hb
  have hm' : AEStronglyMeasurable (fun x : ParticleSpace d N => ∏ k, b k (x k))
      (particleHaar d N) := by
    refine Finset.aestronglyMeasurable_fun_prod (f := fun k (x : ParticleSpace d N) => b k (x k)) _ fun k _ => ?_
    exact (hm k).comp_quasiMeasurePreserving
      (measurePreserving_eval (fun _ : Fin N => haar d) k).quasiMeasurePreserving
  refine memLp_top_of_bound hm' (∏ k, B k) ?_
  have : ∀ᵐ x ∂particleHaar d N, ∀ k, |b k (x k)| ≤ B k := by
    rw [ae_all_iff]
    intro k
    exact (measurePreserving_eval (fun _ : Fin N => haar d) k).quasiMeasurePreserving.ae (hB k)
  filter_upwards [this] with x hx
  rw [Real.norm_eq_abs, Finset.abs_prod]
  gcongr with k _
  exact hx k

theorem continuous_particleTorusEquiv_symm :
    Continuous (particleTorusEquiv d N).symm := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : ∀ z : Torus ((N : ℕ) * d), (particleTorusEquiv d N).symm z i j = z (particleIdx d N (i, j)) := by
    intro z
    have := particleTorusEquiv_apply (d := d) (N := N) ((particleTorusEquiv d N).symm z)
      (particleIdx d N (i, j))
    simpa using this.symm
  simp_rw [this]
  exact continuous_apply _

theorem integral_withDensity_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {h : α → ℝ}
    (hm : AEMeasurable h μ) (h0 : ∀ x, 0 ≤ h x) (g : α → ℝ) :
    ∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (h x)) = ∫ x, h x * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (h0 x)]

theorem pi_withDensity_sq (b : Fin N → Torus d → ℝ) (hb : ∀ k, MemLp (b k) 2 (haar d))
    (ν : Fin N → Measure (Torus d)) [∀ k, SigmaFinite (ν k)]
    (hν : ∀ k, ν k = (haar d).withDensity fun y => ENNReal.ofReal (b k y ^ 2)) :
    Measure.pi ν = (particleHaar d N).withDensity
      fun x => ENNReal.ofReal ((∏ k, b k (x k)) ^ 2) := by
  refine Measure.pi_eq fun s hs => ?_
  have hν' : ∀ k, ν k (s k) = ENNReal.ofReal (∫ y in s k, b k y ^ 2 ∂haar d) := by
    intro k
    rw [hν k, withDensity_apply _ (hs k),
      ofReal_integral_eq_lintegral_ofReal (hb k).integrable_sq.restrict
        (Filter.Eventually.of_forall fun y => sq_nonneg _)]
  have hbox : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox,
    ← ofReal_integral_eq_lintegral_ofReal (memLp_prod_eval hb).integrable_sq.restrict
      (Filter.Eventually.of_forall fun y => sq_nonneg _)]
  simp_rw [hν']
  rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => setIntegral_nonneg (hs k) fun y _ => sq_nonneg _)]
  congr 1
  have hind : ∀ x : ParticleSpace d N, (Set.pi Set.univ s).indicator
      (fun x => (∏ k, b k (x k)) ^ 2) x =
      ∏ k, (s k).indicator (fun y => b k y ^ 2) (x k) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun k _ => (Set.indicator_of_mem (hx k (Set.mem_univ k)) (fun y => b k y ^ 2)).symm
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨k, hk⟩ : ∃ k, x k ∉ s k := by simpa [Set.mem_pi] using hx
      exact (Finset.prod_eq_zero (Finset.mem_univ k) (Set.indicator_of_notMem hk _)).symm
  rw [← integral_indicator hbox]
  simp_rw [hind]
  unfold particleHaar
  rw [integral_fintype_prod_eq_prod (μ := fun _ => haar d)
    (f := fun k y => (s k).indicator (fun y => b k y ^ 2) y)]
  exact Finset.prod_congr rfl fun k _ => integral_indicator (hs k)


/-! ### The particle Gibbs reference on `𝕋^{Nd}` and the particle relative Fisher information -/

theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    (μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm) := by
  have h1 : μ.withDensity g = μ.withDensity (hg.mk g) := withDensity_congr_ae hg.ae_eq_mk
  have h2 : (μ.map e).withDensity (g ∘ e.symm) =
      (μ.map e).withDensity (hg.mk g ∘ e.symm) := by
    refine withDensity_congr_ae ?_
    show ∀ᵐ x ∂μ.map e, (g ∘ e.symm) x = (hg.mk g ∘ e.symm) x
    rw [e.measurableEmbedding.ae_map_iff]
    filter_upwards [hg.ae_eq_mk] with x hx
    simpa using hx
  rw [h1, h2]
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, setLIntegral_map hs (hg.measurable_mk.comp e.symm.measurable)
      e.measurable]
  simp

/-- A bound `M` for the particle Hamiltonian. -/
noncomputable def hamBound (A : InteractionData d) (N : ℕ+) : ℝ :=
  (particleHamiltonian_bounded A N).choose

theorem hamBound_spec (A : InteractionData d) (N : ℕ+) (x : ParticleSpace d N) :
    |particleHamiltonian A N x| ≤ hamBound A N :=
  (particleHamiltonian_bounded A N).choose_spec.2 x

/-- The particle Gibbs law `P_N`, transported to `𝕋^{Nd}`, as a bounded positive reference
(density `p_N ∘ (particleTorusEquiv)⁻¹`, bounded between `exp (-2 M)` and `exp (2 M)`). -/
noncomputable def particleReference (A : InteractionData d) (N : ℕ+) :
    BoundedPositiveReference ((N : ℕ) * d) where
  density z := particleDensity A N ((particleTorusEquiv d N).symm z)
  measurable_density :=
    (particleDensity_measurable A N).comp (particleTorusEquiv d N).symm.measurable
  lower := Real.exp (-(2 * hamBound A N))
  upper := Real.exp (2 * hamBound A N)
  lower_pos := Real.exp_pos _
  lower_le := Eventually.of_forall fun z =>
    (particleDensity_bounds A N (hamBound_spec A N) _).1
  le_upper := Eventually.of_forall fun z =>
    (particleDensity_bounds A N (hamBound_spec A N) _).2
  mass_one := by
    have h := (measurePreserving_particleTorusEquiv d N).integral_comp'
      (fun z => particleDensity A N ((particleTorusEquiv d N).symm z))
    simp only [MeasurableEquiv.symm_apply_apply] at h
    rw [← h]
    exact integral_particleDensity A N

theorem particleReference_measure (A : InteractionData d) (N : ℕ+) :
    (particleReference A N).measure = (particleLaw A N).map (particleTorusEquiv d N) := by
  unfold particleLaw
  rw [map_withDensity_equiv _ _
    (particleDensity_measurable A N).ennreal_ofReal.aemeasurable,
    (measurePreserving_particleTorusEquiv d N).map_eq]
  rfl

/-- The relative Fisher information `I(ν | P_N)` of a law `ν` on `(𝕋^d)^N` against the particle
Gibbs measure `P_N`: the campaign's `ordinaryRelativeFisher` on `𝕋^{Nd}` after transporting both
measures along the measure-preserving identification `(𝕋^d)^N ≃ 𝕋^{Nd}`. -/
noncomputable def particleRelativeFisher (A : InteractionData d) (N : ℕ+)
    (ν : Measure (ParticleSpace d N)) : ℝ≥0∞ :=
  ordinaryRelativeFisher (ν.map (particleTorusEquiv d N)) (particleReference A N)

theorem particleTangentNormSq_eq_norm_gradT (g : ParticleSpace d N → Fin N → Tangent d)
    (x : ParticleSpace d N) :
    particleTangentNormSq (g x) = ‖particleGradT g (particleTorusEquiv d N x)‖ ^ 2 := by
  rw [tangent_norm_sq, particleTangentNormSq_eq]
  simp only [particleGradT_apply, MeasurableEquiv.symm_apply_apply]
  rw [Equiv.sum_comp (particleIdx d N).symm (fun p : Fin N × Fin d => g x p.1 p.2 ^ 2),
    Fintype.sum_prod_type]

/-- Evaluation of the particle relative Fisher information of `ν = f² P_N` through a weak gradient
`g` of `f` (with respect to `m^N`). -/
theorem particleRelativeFisher_eq (A : InteractionData d) {f : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} (hf : IsParticleHaarWeakGradient N f g)
    (hnn : 0 ≤ᵐ[particleHaar d N] f) {ν : Measure (ParticleSpace d N)}
    (hν : ν = (particleLaw A N).withDensity fun x => ENNReal.ofReal (f x ^ 2)) :
    particleRelativeFisher A N ν =
      4 * ∫⁻ x, ENNReal.ofReal (particleTangentNormSq (g x)) ∂particleLaw A N := by
  set e := particleTorusEquiv d N with he
  set P := particleReference A N with hP
  have hfm : AEMeasurable (f ∘ e.symm) (haar ((N : ℕ) * d)) :=
    (memLp_comp_particleTorusEquiv_symm.2 hf.memLp).aestronglyMeasurable.aemeasurable
  have hfm' : AEMeasurable (fun x => ENNReal.ofReal (f x ^ 2)) (particleLaw A N) :=
    ((hf.memLp.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal).mono_ac
      (particleLaw_absolutelyContinuous A N)
  have hmap : ν.map e =
      P.measure.withDensity fun z => ENNReal.ofReal ((f ∘ e.symm) z ^ 2) := by
    rw [hν, map_withDensity_equiv e _ hfm', hP, particleReference_measure]
    rfl
  have hac : ν.map e ≪ P.measure := by
    rw [hmap]; exact withDensity_absolutelyContinuous _ _
  have hnn' : ∀ᵐ z ∂haar ((N : ℕ) * d), 0 ≤ (f ∘ e.symm) z :=
    ((measurePreserving_particleTorusEquiv d N).symm e).quasiMeasurePreserving.ae hnn
  have hrn : (ν.map e).rnDeriv P.measure =ᵐ[P.measure]
      fun z => ENNReal.ofReal ((f ∘ e.symm) z ^ 2) := by
    rw [hmap]
    exact Measure.rnDeriv_withDensity₀ _
      ((hfm.pow_const 2).ennreal_ofReal.mono_ac P.measure_ac_haar)
  have hrel : relativeSqrt (ν.map e) P =ᵐ[haar ((N : ℕ) * d)] f ∘ e.symm := by
    refine P.haar_ac_measure.ae_le ?_
    filter_upwards [hrn, P.measure_ac_haar.ae_le hnn'] with z h1 h2
    simp only [relativeSqrt, h1, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq h2]
  have hws : IsWeakGradient (relativeSqrt (ν.map e) P) (particleGradT g) :=
    (isParticleHaarWeakGradient_iff_weakGradient.1 hf).congr_ae hrel.symm
      (Filter.EventuallyEq.refl _ _)
  unfold particleRelativeFisher
  rw [ordinaryRelativeFisher_eq hac hws, hP, particleReference_measure,
    lintegral_map_equiv]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [particleTangentNormSq_eq_norm_gradT, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-! ### The Gibbs factor `w = p_N^{-1/2}` and the product rule with a bounded factor -/

theorem isParticleHaarWeakGradient_mul_bdd' {u w : ParticleSpace d N → ℝ}
    {gu gw : ParticleSpace d N → Fin N → Tangent d}
    (hu : IsParticleHaarWeakGradient N u gu) (hw : IsParticleHaarWeakGradient N w gw)
    (hwb : MemLp w ⊤ (particleHaar d N))
    (hgw : ∃ C : ℝ, ∀ᵐ x ∂particleHaar d N, particleTangentNormSq (gw x) ≤ C) :
    IsParticleHaarWeakGradient N (fun x => u x * w x) (fun x => w x • gu x + u x • gw x) := by
  obtain ⟨C, hC⟩ := hgw
  have hwb' : MemLp (w ∘ (particleTorusEquiv d N).symm) ⊤ (haar ((N : ℕ) * d)) :=
    memLp_comp_particleTorusEquiv_symm.2 hwb
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hu hw ⊢
  have hgb : MemLp (particleGradT gw) ⊤ (haar ((N : ℕ) * d)) := by
    refine memLp_top_of_bound hw.memLp_grad.aestronglyMeasurable (Real.sqrt C) ?_
    have h := ((measurePreserving_particleTorusEquiv d N).symm _).quasiMeasurePreserving.ae hC
    filter_upwards [h] with z hz
    have := particleTangentNormSq_eq_norm_gradT gw ((particleTorusEquiv d N).symm z)
    rw [MeasurableEquiv.apply_symm_apply] at this
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by rw [← this]; exact hz))
  have h := weak_product_rule_L1 hu hw
  rw [particleGradT_add, particleGradT_smul, particleGradT_smul]
  refine isWeakGradient_iff_isWeakGradientLp.2 ⟨?_, ?_, h.ibp⟩
  · exact hu.memLp.mul (r := 2) hwb'
  · exact (hwb'.smul (r := 2) hu.memLp_grad).add (hu.memLp.smul (r := 2) hgb)

/-- The factor `w = √Z_N e^{H_N/2} = p_N^{-1/2}`. -/
noncomputable def wfun (A : InteractionData d) (N : ℕ+) (x : ParticleSpace d N) : ℝ :=
  Real.sqrt (particlePartition A N) * Real.exp (particleHamiltonian A N x / 2)

theorem continuous_wfun (A : InteractionData d) (N : ℕ+) : Continuous (wfun A N) :=
  continuous_const.mul
    (Real.continuous_exp.comp ((particleHamiltonian_continuous A N).div_const 2))

theorem memLp_top_wfun (A : InteractionData d) (N : ℕ+) : MemLp (wfun A N) ⊤ (particleHaar d N) := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := ParticleSpace d N)).exists_bound_of_continuousOn
    (continuous_wfun A N).continuousOn
  exact MemLp.of_bound (continuous_wfun A N).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ _))

theorem isParticleHaarWeakGradient_wfun (A : InteractionData d) (N : ℕ+)
    {g : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (particleHamiltonian A N) g) :
    IsParticleHaarWeakGradient N (wfun A N) (fun x => (wfun A N x / 2) • g x) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hU ⊢
  obtain ⟨M, hM⟩ := (isCompact_univ (X := ParticleSpace d N)).exists_bound_of_continuousOn
    (particleHamiltonian_continuous A N).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (fun _ => 0) (Set.mem_univ _))
  have hab : -M < M + 1 := by linarith
  have hrng : ∀ z : Torus ((N : ℕ) * d),
      particleHamiltonian A N ((particleTorusEquiv d N).symm z) ∈ Set.Icc (-M) (M + 1) := by
    intro z
    have := hM ((particleTorusEquiv d N).symm z) (Set.mem_univ _)
    rw [Real.norm_eq_abs, abs_le] at this
    exact ⟨this.1, by linarith [this.2]⟩
  have hK := particlePartition_pos A N
  set F : ℝ → ℝ := fun t => Real.sqrt (particlePartition A N) * Real.exp (t / 2) with hF
  have hFd : ContDiffOn ℝ ∞ F (Set.Icc (-M) (M + 1)) :=
    (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.div_const 2))).contDiffOn
  have hch := chain_rule_of_cont_rep
    (u := particleHamiltonian A N ∘ (particleTorusEquiv d N).symm) hU
    ((particleHamiltonian_continuous A N).comp continuous_particleTorusEquiv_symm)
    (Filter.Eventually.of_forall fun _ => rfl) hab hrng hFd
  have hd : ∀ t ∈ Set.Icc (-M) (M + 1),
      derivWithin F (Set.Icc (-M) (M + 1)) t =
        Real.sqrt (particlePartition A N) * Real.exp (t / 2) / 2 := by
    intro t ht
    have h1 : HasDerivAt F
        (Real.sqrt (particlePartition A N) * (Real.exp (t / 2) * (1 / 2))) t := by
      have := ((hasDerivAt_id t).div_const 2).exp.const_mul (Real.sqrt (particlePartition A N))
      simpa using this
    rw [h1.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht)]
    ring
  rw [show (fun x : ParticleSpace d N => (wfun A N x / 2) • g x) =
    fun x => (fun x => wfun A N x / 2) x • g x from rfl, particleGradT_smul]
  refine hch.congr_ae (Filter.Eventually.of_forall fun z => rfl)
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, hd _ (hrng z), wfun]

/-! ### The labeled product root and its gradient -/

theorem particleTangentNormSq_smul (c : ℝ) (v : Fin N → Tangent d) :
    particleTangentNormSq (c • v) = c ^ 2 * particleTangentNormSq v := by
  unfold particleTangentNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- The product amplitude `u(x) = ∏ᵢ √ρ_{σ i}(xᵢ)`. -/
noncomputable def amp (F : SpeciesFamily d) (σ : Fin N → Fin F.count) (x : ParticleSpace d N) :
    ℝ :=
  ∏ k, (F.density (σ k)).sqrt (x k)

/-- The weak gradient of `amp`. -/
noncomputable def ampGrad (F : SpeciesFamily d) (σ : Fin N → Fin F.count)
    (x : ParticleSpace d N) : Fin N → Tangent d :=
  fun i => (∏ k ∈ Finset.univ.erase i, (F.density (σ k)).sqrt (x k)) •
    F.sqrtGradient (σ i) (x i)

/-- The root `f_N = u · p_N^{-1/2}` of the density of the product law against `P_N`. -/
noncomputable def root (A : InteractionData d) (F : SpeciesFamily d) (σ : Fin N → Fin F.count)
    (x : ParticleSpace d N) : ℝ :=
  amp F σ x * wfun A N x

/-- The candidate weak gradient of `root`, for a weak gradient `g` of the Hamiltonian. -/
noncomputable def rootGrad (A : InteractionData d) (F : SpeciesFamily d) (σ : Fin N → Fin F.count)
    (g : ParticleSpace d N → Fin N → Tangent d) (x : ParticleSpace d N) : Fin N → Tangent d :=
  wfun A N x • ampGrad F σ x + amp F σ x • ((wfun A N x / 2) • g x)

theorem amp_isWeakGradient (F : SpeciesFamily d) (σ : Fin N → Fin F.count) :
    IsParticleHaarWeakGradient N (amp F σ) (ampGrad F σ) :=
  isParticleHaarWeakGradient_prod (fun k => (F.density (σ k)).sqrt)
    (fun k => F.sqrtGradient (σ k)) (fun k => F.isWeakGradient_sqrtGradient (σ k))

theorem root_isWeakGradient (A : InteractionData d) (F : SpeciesFamily d)
    (σ : Fin N → Fin F.count) {g : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (particleHamiltonian A N) g)
    (hb : ∃ C : ℝ, ∀ᵐ x ∂particleHaar d N, particleTangentNormSq (g x) ≤ C) :
    IsParticleHaarWeakGradient N (root A F σ) (rootGrad A F σ g) := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨W, hW⟩ := (isCompact_univ (X := ParticleSpace d N)).exists_bound_of_continuousOn
    (continuous_wfun A N).continuousOn
  refine isParticleHaarWeakGradient_mul_bdd' (amp_isWeakGradient F σ)
    (isParticleHaarWeakGradient_wfun A N hU) (memLp_top_wfun A N)
    ⟨(W / 2) ^ 2 * C, ?_⟩
  filter_upwards [hC] with x hx
  show particleTangentNormSq ((wfun A N x / 2) • g x) ≤ _
  rw [particleTangentNormSq_smul]
  have h0 : 0 ≤ particleTangentNormSq (g x) := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hw : |wfun A N x / 2| ≤ W / 2 := by
    rw [abs_div, abs_two]
    have := hW x (Set.mem_univ _)
    rw [Real.norm_eq_abs] at this
    linarith
  have hw2 : (wfun A N x / 2) ^ 2 ≤ (W / 2) ^ 2 := by
    rw [← sq_abs (wfun A N x / 2)]
    exact pow_le_pow_left₀ (abs_nonneg _) hw 2
  exact mul_le_mul hw2 hx h0 (sq_nonneg _)

theorem root_aemeasurable (A : InteractionData d) (F : SpeciesFamily d)
    (σ : Fin N → Fin F.count) : AEMeasurable (root A F σ) (particleHaar d N) :=
  ((memLp_prod_eval (fun k => (F.density (σ k)).memLp_sqrt)).aestronglyMeasurable.aemeasurable).mul
    (continuous_wfun A N).measurable.aemeasurable

theorem amp_nonneg_ae (F : SpeciesFamily d) (σ : Fin N → Fin F.count) :
    0 ≤ᵐ[particleHaar d N] amp F σ := by
  have : ∀ᵐ x ∂particleHaar d N, ∀ k, 0 ≤ (F.density (σ k)).sqrt (x k) := by
    rw [ae_all_iff]
    intro k
    have h0 : ∀ᵐ y ∂haar d, 0 ≤ (F.density (σ k)).sqrt y := by
      filter_upwards [(F.density (σ k)).sqrt_nonneg] with y hy
      exact hy
    exact (measurePreserving_eval (fun _ : Fin N => haar d) k).quasiMeasurePreserving.ae h0
  filter_upwards [this] with x hx
  exact Finset.prod_nonneg fun k _ => hx k

theorem wfun_pos (A : InteractionData d) (N : ℕ+) (x : ParticleSpace d N) : 0 < wfun A N x :=
  mul_pos (Real.sqrt_pos.2 (particlePartition_pos A N)) (Real.exp_pos _)

theorem root_nonneg_ae (A : InteractionData d) (F : SpeciesFamily d) (σ : Fin N → Fin F.count) :
    0 ≤ᵐ[particleHaar d N] root A F σ := by
  filter_upwards [amp_nonneg_ae F σ] with x hx
  exact mul_nonneg hx (wfun_pos A N x).le

theorem p_mul_wfun_sq (A : InteractionData d) (N : ℕ+) (x : ParticleSpace d N) :
    particleDensity A N x * wfun A N x ^ 2 = 1 := by
  have hK := particlePartition_pos A N
  have h1 : Real.exp (particleHamiltonian A N x / 2) ^ 2 = Real.exp (particleHamiltonian A N x) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : Real.exp (-particleHamiltonian A N x) * Real.exp (particleHamiltonian A N x) = 1 := by
    rw [← Real.exp_add]; simp
  unfold particleDensity wfun
  rw [mul_pow, Real.sq_sqrt hK.le, h1]
  calc (particlePartition A N)⁻¹ * Real.exp (-particleHamiltonian A N x) *
        (particlePartition A N * Real.exp (particleHamiltonian A N x))
      = (particlePartition A N)⁻¹ * particlePartition A N *
        (Real.exp (-particleHamiltonian A N x) * Real.exp (particleHamiltonian A N x)) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hK.ne', h2, one_mul]

theorem p_mul_rootsq (A : InteractionData d) (F : SpeciesFamily d) (σ : Fin N → Fin F.count)
    (x : ParticleSpace d N) :
    particleDensity A N x * root A F σ x ^ 2 = amp F σ x ^ 2 := by
  unfold root
  calc particleDensity A N x * (amp F σ x * wfun A N x) ^ 2
      = amp F σ x ^ 2 * (particleDensity A N x * wfun A N x ^ 2) := by ring
    _ = amp F σ x ^ 2 := by rw [p_mul_wfun_sq, mul_one]

theorem productLaw_eq_amp (F : SpeciesFamily d) (σ : Fin N → Fin F.count) :
    productLaw F σ = (particleHaar d N).withDensity fun x => ENNReal.ofReal (amp F σ x ^ 2) :=
  pi_withDensity_sq (fun k => (F.density (σ k)).sqrt) (fun k => (F.density (σ k)).memLp_sqrt) _
    (fun k => densityMeasure_coe (F.density (σ k)))

theorem productLaw_eq_root (A : InteractionData d) (F : SpeciesFamily d)
    (σ : Fin N → Fin F.count) :
    productLaw F σ = (particleLaw A N).withDensity fun x => ENNReal.ofReal (root A F σ x ^ 2) := by
  rw [productLaw_eq_amp, particleLaw,
    ← withDensity_mul₀ (particleDensity_measurable A N).aemeasurable.ennreal_ofReal
      ((root_aemeasurable A F σ).pow_const 2).ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (particleDensity_pos A N x).le, p_mul_rootsq]

/-! ### The energy identity -/

theorem ae_zero_set (F : SpeciesFamily d) (σ : Fin N → Fin F.count) :
    ∀ᵐ x ∂particleHaar d N, ∀ i, (F.density (σ i)).sqrt (x i) = 0 →
      F.sqrtGradient (σ i) (x i) = 0 := by
  rw [ae_all_iff]
  intro i
  have h0 : ∀ᵐ y ∂haar d, (F.density (σ i)).sqrt y = 0 → F.sqrtGradient (σ i) y = 0 :=
    gradient_zero_on_zero_set (F.isWeakGradient_sqrtGradient (σ i))
  exact (measurePreserving_eval (fun _ : Fin N => haar d) i).quasiMeasurePreserving.ae h0

theorem vector_identity {p w c a : ℝ} {G g : Tangent d} (hp : p * w ^ 2 = 1)
    (hG : a = 0 → G = 0) :
    4 * (p * ‖w • (c • G) + (a * c) • ((w / 2) • g)‖ ^ 2) =
      (a * c) ^ 2 * ‖((2 : ℝ) * a⁻¹) • G + g‖ ^ 2 := by
  by_cases ha : a = 0
  · subst ha
    rw [hG rfl]
    simp
  · have hv : w • (c • G) + (a * c) • ((w / 2) • g) =
        (w * c * a / 2) • (((2 : ℝ) * a⁻¹) • G + g) := by
      rw [smul_add, smul_smul, smul_smul, smul_smul]
      congr 2
      · field_simp
      · ring
    rw [hv, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    linear_combination ((a * c) ^ 2 * ‖((2 : ℝ) * a⁻¹) • G + g‖ ^ 2) * hp

theorem pointwise_energy (A : InteractionData d) (F : SpeciesFamily d) (σ : Fin N → Fin F.count)
    (g : ParticleSpace d N → Fin N → Tangent d) (i : Fin N) :
    ∀ᵐ x ∂particleHaar d N,
      4 * (particleDensity A N x * ‖rootGrad A F σ g x i‖ ^ 2) =
        amp F σ x ^ 2 * ‖((2 : ℝ) * ((F.density (σ i)).sqrt (x i))⁻¹) •
          F.sqrtGradient (σ i) (x i) + g x i‖ ^ 2 := by
  filter_upwards [ae_zero_set F σ] with x hx
  have hamp : amp F σ x = (F.density (σ i)).sqrt (x i) *
      ∏ k ∈ Finset.univ.erase i, (F.density (σ k)).sqrt (x k) :=
    prod_split (fun k => (F.density (σ k)).sqrt) x i
  have hr : rootGrad A F σ g x i = wfun A N x • ((∏ k ∈ Finset.univ.erase i,
      (F.density (σ k)).sqrt (x k)) • F.sqrtGradient (σ i) (x i)) +
      ((F.density (σ i)).sqrt (x i) * ∏ k ∈ Finset.univ.erase i, (F.density (σ k)).sqrt (x k)) •
        ((wfun A N x / 2) • g x i) := by
    simp only [rootGrad, ampGrad, Pi.add_apply, Pi.smul_apply, hamp]
  rw [hr, hamp]
  exact vector_identity (p_mul_wfun_sq A N x) (hx i)

/-! ### The relative Fisher information of the product law -/

/-- The relative Fisher information of the product law against the particle Gibbs measure is the
integral of the sum of the squared labeled scores `2 ∇ log √ρ_{σ i} + ∇_i U`. -/
theorem relativeFisher_productLaw (A : InteractionData d) (F : SpeciesFamily d)
    (σ : Fin N → Fin F.count) {g : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (particleHamiltonian A N) g)
    (hb : ∃ C : ℝ, ∀ᵐ x ∂particleHaar d N, particleTangentNormSq (g x) ≤ C) :
    particleRelativeFisher A N (productLaw F σ) =
      ∫⁻ z, ENNReal.ofReal (∑ i, ‖((2 : ℝ) * ((F.density (σ i)).sqrt (z i))⁻¹) •
          F.sqrtGradient (σ i) (z i) + g z i‖ ^ 2) ∂productLaw F σ := by
  rw [particleRelativeFisher_eq A (root_isWeakGradient A F σ hU hb) (root_nonneg_ae A F σ)
    (productLaw_eq_root A F σ)]
  have hamp : AEMeasurable (fun x => ENNReal.ofReal (amp F σ x ^ 2)) (particleHaar d N) :=
    ((amp_isWeakGradient F σ).memLp.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have hpm : Measurable fun x => ENNReal.ofReal (particleDensity A N x) :=
    (particleDensity_measurable A N).ennreal_ofReal
  have hL : ∫⁻ x, ENNReal.ofReal (particleTangentNormSq (rootGrad A F σ g x)) ∂particleLaw A N =
      ∫⁻ x, ENNReal.ofReal (particleDensity A N x) *
        ENNReal.ofReal (particleTangentNormSq (rootGrad A F σ g x)) ∂particleHaar d N := by
    rw [particleLaw]
    exact lintegral_withDensity_eq_lintegral_mul_non_measurable _ hpm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
  rw [hL, productLaw_eq_amp,
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hamp
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← lintegral_const_mul' _ _
      (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
  refine lintegral_congr_ae ?_
  have hall : ∀ᵐ x ∂particleHaar d N, ∀ i, 4 * (particleDensity A N x * ‖rootGrad A F σ g x i‖ ^ 2) =
      amp F σ x ^ 2 * ‖((2 : ℝ) * ((F.density (σ i)).sqrt (x i))⁻¹) •
        F.sqrtGradient (σ i) (x i) + g x i‖ ^ 2 := by
    rw [ae_all_iff]; exact fun i => pointwise_energy A F σ g i
  filter_upwards [hall] with x hx
  have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
  have hsum : 4 * (particleDensity A N x * particleTangentNormSq (rootGrad A F σ g x)) =
      amp F σ x ^ 2 * ∑ i, ‖((2 : ℝ) * ((F.density (σ i)).sqrt (x i))⁻¹) •
        F.sqrtGradient (σ i) (x i) + g x i‖ ^ 2 := by
    unfold particleTangentNormSq
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hx i
  simp only [Pi.mul_apply]
  rw [h4, ← ENNReal.ofReal_mul (particleDensity_pos A N x).le, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (sq_nonneg _), hsum]

/-! ### Positivity-free species facts -/

/-- `species_weighted` without positivity of the square roots: on the zero set of `u_s` both the
density and the weak gradient of `u_s` vanish almost everywhere. -/
theorem species_weighted' (F : SpeciesFamily d) (s : Fin F.count)
    {c : Torus d → Tangent d} (hc : AEStronglyMeasurable c (haar d)) {C : ℝ}
    (hC : ∀ᵐ x ∂haar d, ‖c x‖ ≤ C) :
    AEStronglyMeasurable
        (fun x => ((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x + c x)
        (speciesLaw F s) ∧
      Integrable
        (fun x => ‖((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x + c x‖ ^ 2)
        (speciesLaw F s) ∧
      Integrable
        (fun x => ‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x‖ ^ 2) (haar d) ∧
      ∫ x, ‖((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x + c x‖ ^ 2
          ∂speciesLaw F s =
        ∫ x, ‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x‖ ^ 2 ∂haar d := by
  have hu : AEStronglyMeasurable (F.density s).sqrt (haar d) :=
    (F.density s).memLp_sqrt.aestronglyMeasurable
  have hg : AEStronglyMeasurable (F.sqrtGradient s) (haar d) :=
    (F.isWeakGradient_sqrtGradient s).memLp_grad.aestronglyMeasurable
  have hw : AEStronglyMeasurable
      (fun x => ((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x + c x) (haar d) :=
    ((hu.aemeasurable.inv.const_mul (2 : ℝ)).aestronglyMeasurable.smul hg).add hc
  have hv : AEStronglyMeasurable
      (fun x => (2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x) (haar d) :=
    (hg.const_smul (2 : ℝ)).add (hu.smul hc)
  have hint : Integrable
      (fun x => ‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x‖ ^ 2) (haar d) := by
    have h1 : Integrable (fun x => ‖F.sqrtGradient s x‖ ^ 2) (haar d) :=
      (F.isWeakGradient_sqrtGradient s).memLp_grad.norm.integrable_sq
    have h2 : Integrable (fun x => (F.density s).sqrt x ^ 2) (haar d) :=
      (F.density s).integrable_density
    refine Integrable.mono' ((h1.const_mul 8).add (h2.const_mul (2 * C ^ 2)))
      (hv.norm.pow 2) ?_
    filter_upwards [hC] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have e1 : ‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x‖ ≤
        2 * ‖F.sqrtGradient s x‖ + |(F.density s).sqrt x| * C := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul]; simp
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    have e2 := pow_le_pow_left₀ (norm_nonneg _) e1 2
    refine e2.trans ?_
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (2 * ‖F.sqrtGradient s x‖ - |(F.density s).sqrt x| * C),
      sq_abs ((F.density s).sqrt x)]
  have hpt : ∀ᵐ x ∂haar d, (F.density s).density x •
      ‖((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x + c x‖ ^ 2 =
      ‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x‖ ^ 2 := by
    filter_upwards [gradient_zero_on_zero_set (F.isWeakGradient_sqrtGradient s)] with x h0
    by_cases hx0 : (F.density s).sqrt x = 0
    · rw [h0 hx0, AbsoluteDensity.density, hx0]
      simp
    have : (F.density s).sqrt x • (((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x +
        c x) = (2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x := by
      rw [smul_add, smul_smul]
      congr 2
      field_simp
    rw [← this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, AbsoluteDensity.density,
      smul_eq_mul]
  refine ⟨hw.mono_ac (speciesLaw_ac F s), ?_, hint, ?_⟩
  · unfold speciesLaw
    rw [integrable_densityMeasure_iff]
    exact hint.congr (by filter_upwards [hpt] with x hx; exact hx.symm)
  · unfold speciesLaw
    rw [integral_densityMeasure_smul]
    exact integral_congr_ae hpt

/-- `dissipation_facts` without positivity of the square roots. -/
theorem dissipation_facts' {A : InteractionData d} (hLip : LipschitzData A) (b : AbsoluteDrift A)
    (F : SpeciesFamily d)
    {B : Torus d → Torus d → Tangent d} (hBm : Measurable (Function.uncurry B)) {M : ℝ}
    (hB : ∀ x y, ‖B x y‖ ≤ M) (hBg : ∀ y, IsWeakGradient (fun x => A.W x y) (fun x => B x y))
    {gV : Torus d → Tangent d} (hgV : IsWeakGradient A.V gV) :
    (∀ s, AEStronglyMeasurable (driftA F gV s) (speciesLaw F s)) ∧
      (∀ s, Integrable (fun x => ‖driftA F gV s x‖ ^ 2) (speciesLaw F s)) ∧
      speciesDissipation A b F ≠ ⊤ ∧
      (speciesDissipation A b F).toReal =
        ∑ s, F.weight s *
          ∫ x, ‖limForce (speciesLaw F) (driftA F gV) B F.weight s x‖ ^ 2 ∂speciesLaw F s := by
  obtain ⟨C, hC⟩ := ae_bound_gV hLip hgV
  have hgm : AEStronglyMeasurable gV (haar d) := hgV.memLp_grad.aestronglyMeasurable
  have hKm : Measurable fun x => ∑ t, F.weight t • kernelMean (speciesLaw F t) B x :=
    Finset.measurable_sum _ fun t _ =>
      ((measurable_kernelMean (speciesLaw F t) hBm).const_smul (F.weight t) :
        Measurable (F.weight t • kernelMean (speciesLaw F t) B))
  have hKb : ∀ x, ‖∑ t, F.weight t • kernelMean (speciesLaw F t) B x‖ ≤ M := by
    intro x
    refine (norm_sum_le _ _).trans ?_
    calc ∑ t, ‖F.weight t • kernelMean (speciesLaw F t) B x‖ ≤ ∑ t, F.weight t * M :=
          Finset.sum_le_sum fun t _ => by
            rw [norm_smul, Real.norm_of_nonneg (F.weight_nonneg t)]
            exact mul_le_mul_of_nonneg_left (norm_kernelMean_le (speciesLaw F t) hB x)
              (F.weight_nonneg t)
      _ = M := by rw [← Finset.sum_mul, F.weight_sum, one_mul]
  have hcm : AEStronglyMeasurable
      (fun x => gV x + ∑ t, F.weight t • kernelMean (speciesLaw F t) B x) (haar d) :=
    hgm.add hKm.aestronglyMeasurable
  have hcb : ∀ᵐ x ∂haar d,
      ‖gV x + ∑ t, F.weight t • kernelMean (speciesLaw F t) B x‖ ≤ C + M := by
    filter_upwards [hC] with x hx
    exact (norm_add_le _ _).trans (add_le_add hx (hKb x))
  have hI : ∀ s, ENNReal.ofReal
      (∫ x, ‖limForce (speciesLaw F) (driftA F gV) B F.weight s x‖ ^ 2 ∂speciesLaw F s) =
      ∫⁻ x, ENNReal.ofReal
        (‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • b.force (barycenter F) x‖ ^ 2)
        ∂haar d := by
    intro s
    obtain ⟨-, -, h3, h4⟩ := species_weighted' F s hcm hcb
    have e1 : (fun x => ‖limForce (speciesLaw F) (driftA F gV) B F.weight s x‖ ^ 2) =
        fun x => ‖((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x +
          (gV x + ∑ t, F.weight t • kernelMean (speciesLaw F t) B x)‖ ^ 2 :=
      funext fun x => by rw [limForce_eq]
    rw [e1, h4, ofReal_integral_eq_lintegral_ofReal h3 (Eventually.of_forall fun x => sq_nonneg _)]
    refine lintegral_congr_ae ?_
    filter_upwards [force_ae_eq hLip b F hBm hB hBg hgV] with x hx
    have hx' : b.force (barycenter F) x =
        gV x + ∑ t, F.weight t • kernelMean (speciesLaw F t) B x := hx
    rw [hx']
  have hD : speciesDissipation A b F = ENNReal.ofReal (∑ s, F.weight s *
      ∫ x, ‖limForce (speciesLaw F) (driftA F gV) B F.weight s x‖ ^ 2 ∂speciesLaw F s) := by
    unfold speciesDissipation
    rw [ENNReal.ofReal_sum_of_nonneg fun s _ =>
      mul_nonneg (F.weight_nonneg s) (integral_nonneg fun _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ENNReal.ofReal_mul (F.weight_nonneg s), hI s]
  refine ⟨fun s => (species_weighted' F s hgm hC).1,
    fun s => (species_weighted' F s hgm hC).2.1, ?_, ?_⟩
  · rw [hD]; exact ENNReal.ofReal_ne_top
  · rw [hD]
    exact ENNReal.toReal_ofReal (Finset.sum_nonneg fun s _ =>
      mul_nonneg (F.weight_nonneg s) (integral_nonneg fun _ => sq_nonneg _))

/-! ### Identification of the explicit score functional with the relative Fisher information -/

theorem relativeFisher_eq_score (A : InteractionData d) (hLip : LipschitzData A) (F : SpeciesFamily d)
    {B : Torus d → Torus d → Tangent d} (hBm : Measurable (Function.uncurry B)) {M : ℝ}
    (hM : 0 ≤ M) (hB : ∀ x y, ‖B x y‖ ≤ M) {gV : Torus d → Tangent d}
    (hgV : IsWeakGradient A.V gV)
    (hasm : ∀ s, AEStronglyMeasurable (driftA F gV s) (speciesLaw F s))
    (hai : ∀ s, Integrable (fun x => ‖driftA F gV s x‖ ^ 2) (speciesLaw F s))
    (σ : Fin N → Fin F.count)
    (hPart : IsParticleWeakGradient A N (particleHamiltonian A N)
      (fun x i => gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j))) :
    particleRelativeFisher A N (productLaw F σ) =
      ENNReal.ofReal (∫ z, ∑ i, ‖score (driftA F gV) B σ i z‖ ^ 2 ∂productLaw F σ) := by
  have hU := (isParticleWeakGradient_iff A N _ _).1 hPart
  obtain ⟨C, hC⟩ := ae_bound_gV hLip hgV
  have hall : ∀ᵐ x ∂particleHaar d N, ∀ i, ‖gV (x i)‖ ≤ C := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin N => haar d) i).quasiMeasurePreserving.ae hC
  have hb : ∃ C' : ℝ, ∀ᵐ x : ParticleSpace d N ∂particleHaar d N, particleTangentNormSq
      ((fun x i => gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j)) x) ≤ C' := by
    refine ⟨N * (C + M) ^ 2, ?_⟩
    filter_upwards [hall] with x hx
    unfold particleTangentNormSq
    calc ∑ i, ‖gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j)‖ ^ 2
        ≤ ∑ _i : Fin N, (C + M) ^ 2 := Finset.sum_le_sum fun i _ => by
          have h := norm_score_le (a := fun _ : Fin 1 => gV) hM hB (fun _ => (0 : Fin 1)) i x
          exact pow_le_pow_left₀ (norm_nonneg _) (h.trans (add_le_add_left (hx i) _)) 2
      _ = N * (C + M) ^ 2 := by simp
  rw [relativeFisher_productLaw A F σ hU hb]
  have hs : ∀ z : ParticleSpace d N, ∑ i, ‖((2 : ℝ) * ((F.density (σ i)).sqrt (z i))⁻¹) •
      F.sqrtGradient (σ i) (z i) +
        (gV (z i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (z i) (z j))‖ ^ 2 =
      ∑ i, ‖score (driftA F gV) B σ i z‖ ^ 2 := fun z =>
    Finset.sum_congr rfl fun i _ => by simp only [score, driftA, add_assoc]
  have hint : Integrable (fun z : ParticleSpace d N => ∑ i, ‖score (driftA F gV) B σ i z‖ ^ 2)
      (productLaw F σ) :=
    integrable_finsetSum _ fun i _ => integrable_score_sq (speciesLaw F) hasm hai hBm hM hB σ i
  simp only [hs]
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z => Finset.sum_nonneg fun i _ => sq_nonneg _)).symm

end DGPS.Particle.ProductForceFisher

namespace DGPS.Lipschitz

open DGPS.Particle.ProductForceVariance DGPS.Particle.ProductRecovery DGPS.Particle.ProductForceFisher
  DGPS.Particle

/-- **Product force: conditional variance and relative Fisher information limit.**
For a Lipschitz family and species densities `ρ_s = u_s²` (no positivity assumption), there are a
bounded measurable kernel `B = ∇_x W` and a rounded labelling `σ` with proportions converging to
the weights such that for every weak gradient `gV` of `V` and `A_s = ∇ log ρ_s + ∇V`:
the relative score has conditional mean `A_s + B * ρ̄_N - N⁻¹ B * ρ_s` and conditional variance at
most `‖B‖∞² / N`; the campaign's relative Fisher information `I(ν_N | P_N)` of the product law
`ν_N` against the particle Gibbs measure `P_N` equals the explicit score functional
`∫ ∑ᵢ |scoreᵢ|² dν_N`; it is finite and
`N⁻¹ I(ν_N | P_N) = ∑_s p_s ∫ |conditional mean|² ρ_s + R_N` with `0 ≤ R_N ≤ ‖B‖∞² / N`; and
`N⁻¹ I(ν_N | P_N)` tends to the species dissipation `D_θ`. -/
theorem product_force_relative_fisher_limit {d : ℕ} (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (F : SpeciesFamily d) :
    ∃ (B : Torus d → Torus d → Tangent d) (M : ℝ) (σ : (N : ℕ+) → Fin N → Fin F.count),
      Measurable (Function.uncurry B) ∧ 0 ≤ M ∧ (∀ x y, ‖B x y‖ ≤ M) ∧
      (∀ y, IsWeakGradient (fun x => A.W x y) (fun x => B x y)) ∧
      (∀ s, Tendsto (fun N : ℕ+ => proportion (σ N) s) atTop (𝓝 (F.weight s))) ∧
      (∃ gV : Torus d → Tangent d, IsWeakGradient A.V gV) ∧
      (∀ (gV : Torus d → Tangent d) (N : ℕ+), IsWeakGradient A.V gV →
        IsParticleWeakGradient A N (particleHamiltonian A N)
          (fun x i => gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j))) ∧
      ∀ gV : Torus d → Tangent d, IsWeakGradient A.V gV →
        (∀ (N : ℕ+) (i : Fin N) (x : Torus d),
          ∫ z, score (driftA F gV) B (σ N) i (Function.update z i x) ∂productLaw F (σ N) =
            meanForce (speciesLaw F) (driftA F gV) B (σ N) (σ N i) x) ∧
        (∀ (N : ℕ+) (i : Fin N) (x : Torus d),
          ∫ z, ‖score (driftA F gV) B (σ N) i (Function.update z i x) -
              meanForce (speciesLaw F) (driftA F gV) B (σ N) (σ N i) x‖ ^ 2
            ∂productLaw F (σ N) ≤ M ^ 2 / ((N : ℕ) : ℝ)) ∧
        (∀ N : ℕ+, particleRelativeFisher A N (productLaw F (σ N)) =
          ENNReal.ofReal (∫ z, ∑ i, ‖score (driftA F gV) B (σ N) i z‖ ^ 2
            ∂productLaw F (σ N))) ∧
        (∀ N : ℕ+, particleRelativeFisher A N (productLaw F (σ N)) ≠ ⊤ ∧
          ∃ R : ℝ, 0 ≤ R ∧ R ≤ M ^ 2 / ((N : ℕ) : ℝ) ∧
            ((N : ℕ) : ℝ)⁻¹ * (particleRelativeFisher A N (productLaw F (σ N))).toReal =
              ∑ s, proportion (σ N) s *
                ∫ x, ‖meanForce (speciesLaw F) (driftA F gV) B (σ N) s x‖ ^ 2
                  ∂speciesLaw F s + R) ∧
        Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
          (particleRelativeFisher A N (productLaw F (σ N))).toReal) atTop
          (𝓝 (speciesDissipation A b F).toReal) ∧
        speciesDissipation A b F ≠ ⊤ := by
  obtain ⟨hgex, B, hBm, ⟨M0, hM0⟩, hBg, hPart⟩ := (particle_force_including_the_diagonal d).2.2 A hLip
  obtain ⟨σ, hσ, -⟩ := rounded_finite_species_product_entropy A F
  have hB : ∀ x y, ‖B x y‖ ≤ max M0 0 := fun x y => (hM0 x y).trans (le_max_left _ _)
  refine ⟨B, max M0 0, σ, hBm, le_max_right _ _, hB, hBg, hσ, hgex, hPart, ?_⟩
  intro gV hgV
  obtain ⟨hasm, hai, hne, hD⟩ := dissipation_facts' hLip b F hBm hB hBg hgV
  have hM : 0 ≤ max M0 0 := le_max_right _ _
  have hI : ∀ N : ℕ+, particleRelativeFisher A N (productLaw F (σ N)) =
      ENNReal.ofReal (∫ z, ∑ i, ‖score (driftA F gV) B (σ N) i z‖ ^ 2 ∂productLaw F (σ N)) :=
    fun N => relativeFisher_eq_score A hLip F hBm hM hB hgV hasm hai (σ N) (hPart gV N hgV)
  have hnn : ∀ N : ℕ+, 0 ≤ ∫ z, ∑ i, ‖score (driftA F gV) B (σ N) i z‖ ^ 2 ∂productLaw F (σ N) :=
    fun N => integral_nonneg fun z => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hT : ∀ N : ℕ+, (particleRelativeFisher A N (productLaw F (σ N))).toReal =
      ∫ z, ∑ i, ‖score (driftA F gV) B (σ N) i z‖ ^ 2 ∂productLaw F (σ N) := fun N => by
    rw [hI N, ENNReal.toReal_ofReal (hnn N)]
  refine ⟨fun N i x => condMean_eq (speciesLaw F) (driftA F gV) hBm hB (σ N) i x,
    fun N i x => (condVar_bounds (speciesLaw F) (driftA F gV) hBm hM hB (σ N) i x).2, hI,
    fun N => ⟨by rw [hI N]; exact ENNReal.ofReal_ne_top, ?_⟩, ?_, hne⟩
  · rw [hT N]
    exact fisher_decomp (speciesLaw F) hasm hai hBm hM hB (σ N)
  · simp only [hT]
    rw [hD]
    exact tendsto_fisher (speciesLaw F) hasm hai hBm hM hB σ F.weight hσ

end DGPS.Lipschitz
