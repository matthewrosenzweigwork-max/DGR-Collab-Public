import Mathlib
import DGPS.Examples.PositiveH1.Particle
import DGPS.Foundations.SobolevEmbedding
import DGPS.Particle.Contractions
import DGPS.Foundations.SobolevCalculus

/-!
# Finite-species rough product admissibility (H1016)

For the rough model `kernelData κ` on `𝕋¹` with Gibbs law `P_N = p_N m^N`, a species labeling
`σ : Fin N → Fin q` (species `s` has `n_s(N) = #σ⁻¹(s)` particles, so `∑ₛ n_s(N) = N`) and
absolute-admissible densities `ρ_s` (zero densities allowed), the labeled product measure
`ν_N = ⊗ᵢ ρ_{σ(i)} m` has root density `f_N = √(dν_N/dP_N) = ∏ᵢ √ρ_{σ(i)}(xᵢ) · p_N^{-1/2}`
(`root`), and we prove (`finite_species_rough_product_admissibility`):

* `f_N ∈ H¹(P_N)`, `∫ f_N² dP_N = 1`, `ν_N = f_N² P_N`, `f_N² = dν_N/dP_N` a.e., `f_N ≥ 0`;
* `4 E_N(f_N) = ∑ᵢ E_ν |s_{ρ_{σ(i)}}(Xᵢ) + (κ/N) ∑_{j≠i} R′(Xᵢ - Xⱼ)|²`, where the score
  `s_ρ = 2 (√ρ)'/√ρ` is `0` on `{√ρ = 0}` (`score`).

Reading choices: the species data enters only through the per-particle densities
`i ↦ ρ_{σ(i)}`, so the per-particle form `rough_product_admissibility` is proved first; `κ` is an
arbitrary real; `f_N` is the explicit function `root` (equal a.e. to `√(dν_N/dP_N)`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace DGPS.Examples.PositiveH1.Recovery

open DGPS DGPS.Lipschitz DGPS.Particle DGPS.Examples.PositiveH1.Particle
  DGPS.Examples.PositiveH1.Fourier

variable {N : ℕ+}

theorem memLp_prod_eval {b : Fin N → Torus 1 → ℝ} (hb : ∀ k, MemLp (b k) 2 (haar 1)) :
    MemLp (fun x : ParticleSpace 1 N => ∏ k, b k (x k)) 2 (particleHaar 1 N) := by
  have hm : AEStronglyMeasurable (fun x : ParticleSpace 1 N => ∏ k, b k (x k))
      (particleHaar 1 N) := by
    refine Finset.aestronglyMeasurable_fun_prod (f := fun k (x : ParticleSpace 1 N) => b k (x k)) _ fun k _ => ?_
    exact (hb k).aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_eval (fun _ : Fin N => haar 1) k).quasiMeasurePreserving
  rw [memLp_two_iff_integrable_sq hm]
  have : (fun x : ParticleSpace 1 N => (∏ k, b k (x k)) ^ 2) = fun x => ∏ k, (b k (x k)) ^ 2 := by
    funext x; rw [Finset.prod_pow]
  rw [this]
  exact Integrable.fintype_prod (μ := fun _ => haar 1) (f := fun k y => (b k y) ^ 2)
    (fun k => (hb k).integrable_sq)


theorem prod_update_split (a : Fin N → Torus 1 → ℝ) (x : ParticleSpace 1 N) (i : Fin N)
    (t : Torus 1) :
    ∏ k, a k (Function.update x i t k) = a i t * ∏ k ∈ Finset.univ.erase i, a k (x k) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem prod_split (a : Fin N → Torus 1 → ℝ) (x : ParticleSpace 1 N) (i : Fin N) :
    ∏ k, a k (x k) = a i (x i) * ∏ k ∈ Finset.univ.erase i, a k (x k) := by
  rw [Finset.mul_prod_erase Finset.univ (fun k => a k (x k)) (Finset.mem_univ i)]

theorem isParticleHaarWeakGradient_prod (a : Fin N → Torus 1 → ℝ) (G : Fin N → Torus 1 → Tangent 1)
    (h : ∀ k, IsWeakGradient (a k) (G k)) :
    IsParticleHaarWeakGradient N (fun x => ∏ k, a k (x k))
      (fun x i => (∏ k ∈ Finset.univ.erase i, a k (x k)) • G i (x i)) := by
  classical
  have hu : MemLp (fun x : ParticleSpace 1 N => ∏ k, a k (x k)) 2 (particleHaar 1 N) :=
    memLp_prod_eval fun k => (h k).memLp
  have hg : ∀ (i : Fin N) (l : Fin 1), MemLp
      (fun x : ParticleSpace 1 N => (∏ k ∈ Finset.univ.erase i, a k (x k)) * G i (x i) l) 2
      (particleHaar 1 N) := by
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


theorem isParticleHaarWeakGradient_mul_bdd {u w : ParticleSpace 1 N → ℝ}
    {gu gw : ParticleSpace 1 N → Fin N → Tangent 1}
    (hu : IsParticleHaarWeakGradient N u gu) (hw : IsParticleHaarWeakGradient N w gw)
    (hub : MemLp u ⊤ (particleHaar 1 N)) (hwb : MemLp w ⊤ (particleHaar 1 N)) :
    IsParticleHaarWeakGradient N (fun x => u x * w x) (fun x => w x • gu x + u x • gw x) := by
  have hub' : MemLp (u ∘ (particleTorusEquiv 1 N).symm) ⊤ (haar ((N : ℕ) * 1)) :=
    memLp_comp_particleTorusEquiv_symm.2 hub
  have hwb' : MemLp (w ∘ (particleTorusEquiv 1 N).symm) ⊤ (haar ((N : ℕ) * 1)) :=
    memLp_comp_particleTorusEquiv_symm.2 hwb
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hu hw ⊢
  have h := weak_product_rule_L1 hu hw
  rw [particleGradT_add, particleGradT_smul, particleGradT_smul]
  refine isWeakGradient_iff_isWeakGradientLp.2 ⟨?_, ?_, h.ibp⟩
  · exact hu.memLp.mul (r := 2) hwb'
  · exact (hwb'.smul (r := 2) hu.memLp_grad).add (hub'.smul (r := 2) hw.memLp_grad)


theorem memLp_top_prod_eval {b : Fin N → Torus 1 → ℝ}
    (hm : ∀ k, AEStronglyMeasurable (b k) (haar 1))
    (hb : ∀ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂haar 1, |b k x| ≤ B) :
    MemLp (fun x : ParticleSpace 1 N => ∏ k, b k (x k)) ⊤ (particleHaar 1 N) := by
  choose B hB0 hB using hb
  have hm' : AEStronglyMeasurable (fun x : ParticleSpace 1 N => ∏ k, b k (x k))
      (particleHaar 1 N) := by
    refine Finset.aestronglyMeasurable_fun_prod (f := fun k (x : ParticleSpace 1 N) => b k (x k)) _ fun k _ => ?_
    exact (hm k).comp_quasiMeasurePreserving
      (measurePreserving_eval (fun _ : Fin N => haar 1) k).quasiMeasurePreserving
  refine memLp_top_of_bound hm' (∏ k, B k) ?_
  have : ∀ᵐ x ∂particleHaar 1 N, ∀ k, |b k (x k)| ≤ B k := by
    rw [ae_all_iff]
    intro k
    exact (measurePreserving_eval (fun _ : Fin N => haar 1) k).quasiMeasurePreserving.ae (hB k)
  filter_upwards [this] with x hx
  rw [Real.norm_eq_abs, Finset.abs_prod]
  gcongr with k _
  exact hx k

theorem continuous_particleTorusEquiv_symm :
    Continuous (particleTorusEquiv 1 N).symm := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : ∀ z : Torus ((N : ℕ) * 1), (particleTorusEquiv 1 N).symm z i j = z (particleIdx 1 N (i, j)) := by
    intro z
    have := particleTorusEquiv_apply (d := 1) (N := N) ((particleTorusEquiv 1 N).symm z)
      (particleIdx 1 N (i, j))
    simpa using this.symm
  simp_rw [this]
  exact continuous_apply _

/-- The factor `w = √K e^{U/2} = p^{-1/2}`. -/
noncomputable def wfun (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) : ℝ :=
  Real.sqrt (K κ N) * Real.exp (U κ N x / 2)

theorem continuous_wfun (κ : ℝ) (N : ℕ+) : Continuous (wfun κ N) :=
  continuous_const.mul (Real.continuous_exp.comp ((continuous_U κ N).div_const 2))

theorem memLp_top_wfun (κ : ℝ) (N : ℕ+) : MemLp (wfun κ N) ⊤ (particleHaar 1 N) := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := ParticleSpace 1 N)).exists_bound_of_continuousOn
    (continuous_wfun κ N).continuousOn
  exact MemLp.of_bound (continuous_wfun κ N).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ _))

theorem isParticleHaarWeakGradient_wfun (κ : ℝ) (N : ℕ+) :
    IsParticleHaarWeakGradient N (wfun κ N) (fun x => (wfun κ N x / 2) • roughForce κ N x) := by
  have hU := (weak_rough_particle_gradient κ N).2.1
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hU ⊢
  obtain ⟨M, hM⟩ := (isCompact_univ (X := ParticleSpace 1 N)).exists_bound_of_continuousOn
    (continuous_U κ N).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (fun _ => 0) (Set.mem_univ _))
  have hab : -M < M + 1 := by linarith
  have hrng : ∀ z : Torus ((N : ℕ) * 1), U κ N ((particleTorusEquiv 1 N).symm z) ∈ Set.Icc (-M) (M + 1) := by
    intro z
    have := hM ((particleTorusEquiv 1 N).symm z) (Set.mem_univ _)
    rw [Real.norm_eq_abs, abs_le] at this
    exact ⟨this.1, by linarith [this.2]⟩
  have hK := K_pos κ N
  set F : ℝ → ℝ := fun t => Real.sqrt (K κ N) * Real.exp (t / 2) with hF
  have hFd : ContDiffOn ℝ ∞ F (Set.Icc (-M) (M + 1)) :=
    (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.div_const 2))).contDiffOn
  have hch := chain_rule_of_cont_rep (u := U κ N ∘ (particleTorusEquiv 1 N).symm) hU
    ((continuous_U κ N).comp continuous_particleTorusEquiv_symm)
    (Filter.Eventually.of_forall fun _ => rfl) hab hrng hFd
  have hd : ∀ t ∈ Set.Icc (-M) (M + 1),
      derivWithin F (Set.Icc (-M) (M + 1)) t = Real.sqrt (K κ N) * Real.exp (t / 2) / 2 := by
    intro t ht
    have h1 : HasDerivAt F (Real.sqrt (K κ N) * (Real.exp (t / 2) * (1 / 2))) t := by
      have := ((hasDerivAt_id t).div_const 2).exp.const_mul (Real.sqrt (K κ N))
      simpa using this
    rw [h1.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht)]
    ring
  rw [show (fun x : ParticleSpace 1 N => (wfun κ N x / 2) • roughForce κ N x) =
    fun x => (fun x => wfun κ N x / 2) x • roughForce κ N x from rfl, particleGradT_smul]
  refine hch.congr_ae (Filter.Eventually.of_forall fun z => rfl) (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, hd _ (hrng z), wfun]

theorem integral_withDensity_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {h : α → ℝ}
    (hm : AEMeasurable h μ) (h0 : ∀ x, 0 ≤ h x) (g : α → ℝ) :
    ∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (h x)) = ∫ x, h x * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (h0 x)]

theorem pi_withDensity_sq (b : Fin N → Torus 1 → ℝ) (hb : ∀ k, MemLp (b k) 2 (haar 1))
    (ν : Fin N → Measure (Torus 1)) [∀ k, SigmaFinite (ν k)]
    (hν : ∀ k, ν k = (haar 1).withDensity fun y => ENNReal.ofReal (b k y ^ 2)) :
    Measure.pi ν = (particleHaar 1 N).withDensity
      fun x => ENNReal.ofReal ((∏ k, b k (x k)) ^ 2) := by
  refine Measure.pi_eq fun s hs => ?_
  have hν' : ∀ k, ν k (s k) = ENNReal.ofReal (∫ y in s k, b k y ^ 2 ∂haar 1) := by
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
  have hind : ∀ x : ParticleSpace 1 N, (Set.pi Set.univ s).indicator
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
  rw [integral_fintype_prod_eq_prod (μ := fun _ => haar 1)
    (f := fun k y => (s k).indicator (fun y => b k y ^ 2) y)]
  exact Finset.prod_congr rfl fun k _ => integral_indicator (hs k)

/-! ### The labeled product root and its gradient -/

/-- The product amplitude `u(x) = ∏ᵢ √ρᵢ(xᵢ)`. -/
noncomputable def amp (r : Fin N → AbsoluteDensity 1) (x : ParticleSpace 1 N) : ℝ :=
  ∏ k, (r k).sqrt (x k)

/-- The score `s_ρ = ρ'/ρ = 2 (√ρ)'/√ρ` (equal to `0` on the zero set of `√ρ`). -/
noncomputable def score (ρ : AbsoluteDensity 1) (y : Torus 1) : ℝ :=
  2 * weakGradient ρ.sqrt ρ.sqrt_mem y 0 / ρ.sqrt y

/-- The square root `f_N = √(dν_N/dP_N) = u · p_N^{-1/2}` of the density of the product law. -/
noncomputable def root (κ : ℝ) (r : Fin N → AbsoluteDensity 1) (x : ParticleSpace 1 N) : ℝ :=
  amp r x * wfun κ N x

/-- The candidate weak gradient of `root`. -/
noncomputable def rootGrad (κ : ℝ) (r : Fin N → AbsoluteDensity 1) (x : ParticleSpace 1 N) :
    Fin N → Tangent 1 :=
  wfun κ N x • (fun i => (∏ k ∈ Finset.univ.erase i, (r k).sqrt (x k)) •
      weakGradient (r i).sqrt (r i).sqrt_mem (x i)) +
    amp r x • ((wfun κ N x / 2) • roughForce κ N x)

theorem amp_isWeakGradient (r : Fin N → AbsoluteDensity 1) :
    IsParticleHaarWeakGradient N (amp r)
      (fun x i => (∏ k ∈ Finset.univ.erase i, (r k).sqrt (x k)) •
        weakGradient (r i).sqrt (r i).sqrt_mem (x i)) :=
  isParticleHaarWeakGradient_prod (fun k => (r k).sqrt)
    (fun k => weakGradient (r k).sqrt (r k).sqrt_mem)
    (fun k => isWeakGradient_weakGradient (r k).sqrt_mem)

theorem memLp_top_amp (r : Fin N → AbsoluteDensity 1) :
    MemLp (amp r) ⊤ (particleHaar 1 N) :=
  memLp_top_prod_eval (b := fun k => (r k).sqrt)
    (fun k => (r k).memLp_sqrt.aestronglyMeasurable)
    (fun k => exists_ae_bound_one (isWeakGradient_weakGradient (r k).sqrt_mem))

theorem root_isWeakGradient (κ : ℝ) (r : Fin N → AbsoluteDensity 1) :
    IsParticleHaarWeakGradient N (root κ r) (rootGrad κ r) :=
  isParticleHaarWeakGradient_mul_bdd (amp_isWeakGradient r) (isParticleHaarWeakGradient_wfun κ N)
    (memLp_top_amp r) (memLp_top_wfun κ N)

theorem root_memParticleH1 (κ : ℝ) (r : Fin N → AbsoluteDensity 1) :
    MemParticleH1 (kernelData κ) N (root κ r) :=
  ⟨rootGrad κ r, (isParticleWeakGradient_iff _ _ _ _).2 (root_isWeakGradient κ r)⟩

theorem root_isParticleWeakGradient (κ : ℝ) (r : Fin N → AbsoluteDensity 1) :
    IsParticleWeakGradient (kernelData κ) N (root κ r) (rootGrad κ r) :=
  (isParticleWeakGradient_iff _ _ _ _).2 (root_isWeakGradient κ r)

/-! ### The Gibbs density -/

theorem particleLaw_eq (κ : ℝ) (N : ℕ+) :
    particleLaw (kernelData κ) N =
      (particleHaar 1 N).withDensity fun x => ENNReal.ofReal (p κ N x) := by
  unfold particleLaw
  congr 1
  funext x
  rw [density_eq]

theorem continuous_p (κ : ℝ) (N : ℕ+) : Continuous (p κ N) := by
  unfold p
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_U κ N).neg)

theorem p_nonneg (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) : 0 ≤ p κ N x :=
  mul_nonneg (inv_nonneg.2 (K_pos κ N).le) (Real.exp_pos _).le

theorem p_mul_wfun_sq (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    p κ N x * wfun κ N x ^ 2 = 1 := by
  have hK := K_pos κ N
  have h1 : Real.exp (U κ N x / 2) ^ 2 = Real.exp (U κ N x) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : Real.exp (-U κ N x) * Real.exp (U κ N x) = 1 := by
    rw [← Real.exp_add]; simp
  unfold p wfun
  rw [mul_pow, Real.sq_sqrt hK.le, h1]
  calc (K κ N)⁻¹ * Real.exp (-U κ N x) * (K κ N * Real.exp (U κ N x))
      = (K κ N)⁻¹ * K κ N * (Real.exp (-U κ N x) * Real.exp (U κ N x)) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hK.ne', h2, one_mul]

/-! ### Mass, density and nonnegativity -/

theorem wfun_pos (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) : 0 < wfun κ N x :=
  mul_pos (Real.sqrt_pos.2 (K_pos κ N)) (Real.exp_pos _)

theorem amp_nonneg_ae (r : Fin N → AbsoluteDensity 1) : 0 ≤ᵐ[particleHaar 1 N] amp r := by
  have : ∀ᵐ x ∂particleHaar 1 N, ∀ k, 0 ≤ (r k).sqrt (x k) := by
    rw [ae_all_iff]
    intro k
    have h0 : ∀ᵐ y ∂haar 1, 0 ≤ (r k).sqrt y := by
      filter_upwards [(r k).sqrt_nonneg] with y hy
      exact hy
    exact (measurePreserving_eval (fun _ : Fin N => haar 1) k).quasiMeasurePreserving.ae h0
  filter_upwards [this] with x hx
  exact Finset.prod_nonneg fun k _ => hx k

theorem root_nonneg_ae (κ : ℝ) (r : Fin N → AbsoluteDensity 1) :
    0 ≤ᵐ[particleHaar 1 N] root κ r := by
  filter_upwards [amp_nonneg_ae r] with x hx
  exact mul_nonneg hx (wfun_pos κ N x).le

theorem p_mul_rootsq (κ : ℝ) (r : Fin N → AbsoluteDensity 1) (x : ParticleSpace 1 N) :
    p κ N x * root κ r x ^ 2 = amp r x ^ 2 := by
  unfold root
  calc p κ N x * (amp r x * wfun κ N x) ^ 2
      = amp r x ^ 2 * (p κ N x * wfun κ N x ^ 2) := by ring
    _ = amp r x ^ 2 := by rw [p_mul_wfun_sq, mul_one]

/-- The labeled product measure `ν_N = ⊗ᵢ ρ_{σ(i)} m`. -/
noncomputable def labeledProduct (r : Fin N → AbsoluteDensity 1) : Measure (ParticleSpace 1 N) :=
  Measure.pi fun i => (densityMeasure (r i) : Measure (Torus 1))

theorem labeledProduct_eq (r : Fin N → AbsoluteDensity 1) :
    labeledProduct r = (particleHaar 1 N).withDensity fun x => ENNReal.ofReal (amp r x ^ 2) :=
  pi_withDensity_sq (fun k => (r k).sqrt) (fun k => (r k).memLp_sqrt) _
    (fun k => densityMeasure_coe (r k))

theorem root_aemeasurable (κ : ℝ) (r : Fin N → AbsoluteDensity 1) :
    AEMeasurable (root κ r) (particleHaar 1 N) :=
  (root_isWeakGradient κ r).memLp.aestronglyMeasurable.aemeasurable

theorem labeledProduct_eq_withDensity (κ : ℝ) (r : Fin N → AbsoluteDensity 1) :
    labeledProduct r =
      (particleLaw (kernelData κ) N).withDensity fun x => ENNReal.ofReal (root κ r x ^ 2) := by
  rw [labeledProduct_eq, particleLaw_eq,
    ← withDensity_mul₀ (continuous_p κ N).aemeasurable.ennreal_ofReal
      ((root_aemeasurable κ r).pow_const 2).ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (p_nonneg κ N x), p_mul_rootsq]

theorem integral_rootsq (κ : ℝ) (r : Fin N → AbsoluteDensity 1) :
    ∫ x, root κ r x ^ 2 ∂particleLaw (kernelData κ) N = 1 := by
  rw [particleLaw_eq, integral_withDensity_ofReal (continuous_p κ N).aemeasurable
    (p_nonneg κ N)]
  simp_rw [p_mul_rootsq]
  have : (fun x : ParticleSpace 1 N => amp r x ^ 2) = fun x => ∏ k, ((r k).sqrt (x k)) ^ 2 := by
    funext x; unfold amp; rw [Finset.prod_pow]
  rw [this]
  unfold particleHaar
  rw [integral_fintype_prod_eq_prod (μ := fun _ => haar 1) (f := fun k y => (r k).sqrt y ^ 2)]
  simp [(r _).mass_one]

/-! ### The energy identity -/

theorem real_identity {p w c a G F : ℝ} (hp : p * w ^ 2 = 1) (hG : a = 0 → G = 0) :
    4 * p * (w * (c * G) + a * c * (w / 2 * F)) ^ 2 = (a * c) ^ 2 * (2 * G / a + F) ^ 2 := by
  by_cases ha : a = 0
  · subst ha
    rw [hG rfl]
    simp
  · have h : 4 * p * (w * (c * G) + a * c * (w / 2 * F)) ^ 2 =
        4 * (p * w ^ 2) * (c * (G + a * F / 2)) ^ 2 := by ring
    rw [h, hp]
    field_simp
    ring

theorem ae_zero_set (r : Fin N → AbsoluteDensity 1) :
    ∀ᵐ x ∂particleHaar 1 N, ∀ i, (r i).sqrt (x i) = 0 →
      weakGradient (r i).sqrt (r i).sqrt_mem (x i) 0 = 0 := by
  rw [ae_all_iff]
  intro i
  have h0 : ∀ᵐ y ∂haar 1, (r i).sqrt y = 0 → weakGradient (r i).sqrt (r i).sqrt_mem y 0 = 0 := by
    filter_upwards [weakGradient_zero_on_zero_set (r i).sqrt_mem] with y hy h
    rw [hy h]
    simp
  exact (measurePreserving_eval (fun _ : Fin N => haar 1) i).quasiMeasurePreserving.ae h0

theorem rootGrad_apply (κ : ℝ) (r : Fin N → AbsoluteDensity 1) (x : ParticleSpace 1 N) (i : Fin N) :
    rootGrad κ r x i 0 = wfun κ N x * ((∏ k ∈ Finset.univ.erase i, (r k).sqrt (x k)) *
      weakGradient (r i).sqrt (r i).sqrt_mem (x i) 0) +
      amp r x * (wfun κ N x / 2 * roughForce κ N x i 0) := by
  simp [rootGrad]

theorem pointwise_energy (κ : ℝ) (r : Fin N → AbsoluteDensity 1) (i : Fin N) :
    ∀ᵐ x ∂particleHaar 1 N, 4 * (p κ N x * rootGrad κ r x i 0 ^ 2) =
      amp r x ^ 2 * (score (r i) (x i) + roughForce κ N x i 0) ^ 2 := by
  filter_upwards [ae_zero_set r] with x hx
  have hamp : amp r x = (r i).sqrt (x i) * ∏ k ∈ Finset.univ.erase i, (r k).sqrt (x k) :=
    prod_split (fun k => (r k).sqrt) x i
  rw [rootGrad_apply, hamp, ← mul_assoc]
  exact real_identity (p_mul_wfun_sq κ N x) (hx i)

theorem exists_p_bound (κ : ℝ) (N : ℕ+) : ∃ C : ℝ, ∀ x, ‖p κ N x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := ParticleSpace 1 N)).exists_bound_of_continuousOn
    (continuous_p κ N).continuousOn
  exact ⟨C, fun x => hC x (Set.mem_univ _)⟩

theorem integrable_p_mul_grad_sq (κ : ℝ) (r : Fin N → AbsoluteDensity 1) (i : Fin N) :
    Integrable (fun x => p κ N x * rootGrad κ r x i 0 ^ 2) (particleHaar 1 N) := by
  obtain ⟨C, hC⟩ := exists_p_bound κ N
  exact (memLp_particleCoord (root_isWeakGradient κ r).memLp_grad i 0).integrable_sq.bdd_mul
    (continuous_p κ N).aestronglyMeasurable (Filter.Eventually.of_forall hC)

theorem four_energy (κ : ℝ) (r : Fin N → AbsoluteDensity 1)
    (h : MemParticleH1 (kernelData κ) N (root κ r)) :
    4 * particleEnergy (kernelData κ) N ⟨root κ r, h⟩ =
      ∑ i, ∫ x, (score (r i) (x i) + roughForce κ N x i 0) ^ 2 ∂labeledProduct r := by
  rw [particleEnergy_eq_of_isParticleWeakGradient ⟨root κ r, h⟩ (root_isParticleWeakGradient κ r)]
  simp only [particleTangentNormSq_eq, Fin.sum_univ_one]
  rw [particleLaw_eq, integral_withDensity_ofReal (continuous_p κ N).aemeasurable (p_nonneg κ N)]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_p_mul_grad_sq κ r i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [labeledProduct_eq, integral_withDensity_ofReal
    (((memLp_top_amp r).aestronglyMeasurable.aemeasurable).pow_const 2)
    (fun x => sq_nonneg _), ← integral_const_mul]
  exact integral_congr_ae (pointwise_energy κ r i)

/-! ### The admissibility theorem -/

/-- Per-particle form: for any family `ρᵢ` of absolute-admissible densities on `𝕋¹`, the labeled
product law `ν = ⊗ᵢ ρᵢ m` has root density `f = √(dν/dP_N) = ∏ᵢ √ρᵢ(xᵢ) · p_N^{-1/2}` in `H¹(P_N)`
with mass one, and `4 E_N(f) = ∑ᵢ E_ν |s_{ρᵢ}(xᵢ) + (κ/N) ∑_{j≠i} R′(xᵢ - xⱼ)|²`. -/
theorem rough_product_admissibility (κ : ℝ) (N : ℕ+) (r : Fin N → AbsoluteDensity 1) :
    MemParticleH1 (kernelData κ) N (root κ r) ∧
    ∫ x, root κ r x ^ 2 ∂particleLaw (kernelData κ) N = 1 ∧
    labeledProduct r = (particleLaw (kernelData κ) N).withDensity
      (fun x => ENNReal.ofReal (root κ r x ^ 2)) ∧
    (fun x => root κ r x ^ 2) =ᵐ[particleLaw (kernelData κ) N]
      (fun x => ((labeledProduct r).rnDeriv (particleLaw (kernelData κ) N) x).toReal) ∧
    root κ r =ᵐ[particleLaw (kernelData κ) N]
      (fun x => Real.sqrt (((labeledProduct r).rnDeriv (particleLaw (kernelData κ) N) x).toReal)) ∧
    0 ≤ᵐ[particleLaw (kernelData κ) N] root κ r ∧
    ∀ h : MemParticleH1 (kernelData κ) N (root κ r),
      4 * particleEnergy (kernelData κ) N ⟨root κ r, h⟩ =
        ∑ i, ∫ x, (score (r i) (x i) + κ / (N : ℝ) *
          ∑ j ∈ Finset.univ.erase i, dR (x i - x j)) ^ 2 ∂labeledProduct r := by
  have hac := DGPS.Particle.particleLaw_absolutelyContinuous (kernelData κ) N
  have hν := labeledProduct_eq_withDensity κ r
  have hrn : (labeledProduct r).rnDeriv (particleLaw (kernelData κ) N) =ᵐ[particleLaw (kernelData κ) N]
      fun x => ENNReal.ofReal (root κ r x ^ 2) := by
    rw [hν]
    exact Measure.rnDeriv_withDensity₀ _
      ((((root_aemeasurable κ r).pow_const 2).ennreal_ofReal).mono_ac hac)
  have hnn : 0 ≤ᵐ[particleLaw (kernelData κ) N] root κ r := hac.ae_le (root_nonneg_ae κ r)
  refine ⟨root_memParticleH1 κ r, integral_rootsq κ r, hν, ?_, ?_, hnn, ?_⟩
  · filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal (sq_nonneg _)]
  · filter_upwards [hrn, hnn] with x hx h0
    rw [hx, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq h0]
  · intro h
    rw [four_energy κ r h]
    simp_rw [roughForce_apply]

/-- **H1016.** Finite-species rough product admissibility. Let `σ : Fin N → Fin q` be a species
labeling (species `s` has `n_s(N) = #σ⁻¹(s)` particles, `∑ₛ n_s(N) = N`) and `ρ_s` absolute-admissible
densities on `𝕋¹` (zero densities allowed). With `ν_N = ⊗ᵢ ρ_{σ(i)} m` the labeled product measure
and `P_N` the rough Gibbs law (density `p_N`), the root density `f_N = √(dν_N/dP_N)` (given by
`root`, with `f_N² = dν_N/dP_N` a.e.) lies in `H¹(P_N)`, has `∫ f_N² dP_N = 1`, and
`4 E_N(f_N) = ∑ᵢ E_ν |s_{ρ_{σ(i)}}(Xᵢ) + (κ/N) ∑_{j≠i} R′(Xᵢ - Xⱼ)|²`. -/
theorem finite_species_rough_product_admissibility (κ : ℝ) (N : ℕ+) {q : ℕ}
    (σ : Fin N → Fin q) (ρ : Fin q → AbsoluteDensity 1) :
    MemParticleH1 (kernelData κ) N (root κ fun i => ρ (σ i)) ∧
    ∫ x, root κ (fun i => ρ (σ i)) x ^ 2 ∂particleLaw (kernelData κ) N = 1 ∧
    labeledProduct (fun i => ρ (σ i)) = (particleLaw (kernelData κ) N).withDensity
      (fun x => ENNReal.ofReal (root κ (fun i => ρ (σ i)) x ^ 2)) ∧
    (fun x => root κ (fun i => ρ (σ i)) x ^ 2) =ᵐ[particleLaw (kernelData κ) N]
      (fun x => ((labeledProduct fun i => ρ (σ i)).rnDeriv (particleLaw (kernelData κ) N) x).toReal) ∧
    root κ (fun i => ρ (σ i)) =ᵐ[particleLaw (kernelData κ) N]
      (fun x => Real.sqrt
        (((labeledProduct fun i => ρ (σ i)).rnDeriv (particleLaw (kernelData κ) N) x).toReal)) ∧
    0 ≤ᵐ[particleLaw (kernelData κ) N] root κ (fun i => ρ (σ i)) ∧
    ∀ h : MemParticleH1 (kernelData κ) N (root κ fun i => ρ (σ i)),
      4 * particleEnergy (kernelData κ) N ⟨root κ fun i => ρ (σ i), h⟩ =
        ∑ i, ∫ x, (score (ρ (σ i)) (x i) + κ / (N : ℝ) *
          ∑ j ∈ Finset.univ.erase i, dR (x i - x j)) ^ 2
            ∂labeledProduct (fun i => ρ (σ i)) :=
  rough_product_admissibility κ N fun i => ρ (σ i)

end DGPS.Examples.PositiveH1.Recovery
