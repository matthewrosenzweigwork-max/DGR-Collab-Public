import DGPS.Lipschitz.EigenfunctionC1
import DGPS.Particle.ProductForceFisher

/-!
# LIP062: the weak particle dual generator identity

For a `C²` cylinder `c` of finitely many eigenfunction coordinates `Z_i = N^{-1/2} ∑ₗ eᵢ(Xₗ)`,
every `f ∈ H¹(P_N)` satisfies
`E_N(f) ≥ 2 ⟨f, G_N c⟩_{P_N} - E_N(c(Z_N))`,
see `weak_particle_dual_generator_identity`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff InnerProductSpace RealInnerProductSpace

namespace DGPS.Lipschitz

open DGPS DGPS.Analysis DGPS.Particle DGPS.Lipschitz.ParabolicChainRule
  DGPS.Lipschitz.WeightedGenerator DGPS.Particle.ProductForceFisher

variable {d : ℕ} {N : ℕ+}

/-! ### Calculus of particle weak gradients -/

theorem dg_add {u v : ParticleSpace d N → ℝ} {g k : ParticleSpace d N → Fin N → Tangent d}
    (hu : IsParticleHaarWeakGradient N u g) (hv : IsParticleHaarWeakGradient N v k) :
    IsParticleHaarWeakGradient N (fun x => u x + v x) (fun x => g x + k x) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hu hv ⊢
  rw [particleGradT_add]
  exact hu.add hv

theorem dg_smul {u : ParticleSpace d N → ℝ} {g : ParticleSpace d N → Fin N → Tangent d}
    (hu : IsParticleHaarWeakGradient N u g) (c : ℝ) :
    IsParticleHaarWeakGradient N (fun x => c * u x) (fun x => c • g x) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hu ⊢
  have e : particleGradT (fun x => c • g x) = fun z => c • particleGradT g z :=
    particleGradT_smul (fun _ => c) g
  rw [e]
  exact hu.smul c

theorem dg_zero : IsParticleHaarWeakGradient N (fun _ : ParticleSpace d N => (0 : ℝ))
    (fun _ => 0) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient, particleGradT_zero]
  exact isWeakGradient_zero

theorem dg_sum {ι : Type*} (s : Finset ι) {u : ι → ParticleSpace d N → ℝ}
    {g : ι → ParticleSpace d N → Fin N → Tangent d}
    (h : ∀ i ∈ s, IsParticleHaarWeakGradient N (u i) (g i)) :
    IsParticleHaarWeakGradient N (fun x => ∑ i ∈ s, u i x) (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dg_zero (d := d) (N := N)
  | insert a s ha ih =>
    have h1 := dg_add (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    simpa only [Finset.sum_insert ha] using h1

theorem dg_const (c : ℝ) : IsParticleHaarWeakGradient N (fun _ : ParticleSpace d N => c)
    (fun _ => 0) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient, particleGradT_zero]
  exact df_isWeakGradient_const c

/-- A function of a single particle slot. -/
theorem dg_slot (l : Fin N) {u : Torus d → ℝ} {Y : Torus d → Tangent d}
    (hu : IsWeakGradient u Y) :
    IsParticleHaarWeakGradient N (fun x => u (x l)) (fun x k => if k = l then Y (x l) else 0) := by
  classical
  have h := isParticleHaarWeakGradient_prod (N := N) (fun k => if k = l then u else fun _ => 1)
    (fun k => if k = l then Y else fun _ => 0) (fun k => by
      by_cases hk : k = l
      · simpa [hk] using hu
      · simpa [hk] using df_isWeakGradient_const (d := d) 1)
  have e1 : (fun x : ParticleSpace d N => ∏ k, (if k = l then u else fun _ => (1 : ℝ)) (x k)) =
      fun x => u (x l) := by
    funext x
    rw [Finset.prod_eq_single l]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have e2 : (fun (x : ParticleSpace d N) (i : Fin N) =>
      (∏ k ∈ Finset.univ.erase i, (if k = l then u else fun _ => (1 : ℝ)) (x k)) •
        (if i = l then Y else fun _ => (0 : Tangent d)) (x i)) =
      fun x k => if k = l then Y (x l) else 0 := by
    funext x i
    by_cases hi : i = l
    · subst hi
      rw [Finset.prod_eq_one]
      · simp
      · intro k hk
        simp [Finset.ne_of_mem_erase hk]
    · simp [hi]
  rw [e1, e2] at h
  exact h

theorem dg_memLp_top {u : ParticleSpace d N → ℝ} (hu : Continuous u) :
    MemLp u ⊤ (particleHaar d N) := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := ParticleSpace d N)).exists_bound_of_continuousOn
    hu.continuousOn
  exact MemLp.of_bound hu.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ _))

theorem dg_mul {u w : ParticleSpace d N → ℝ} {gu gw : ParticleSpace d N → Fin N → Tangent d}
    (hu : IsParticleHaarWeakGradient N u gu) (hw : IsParticleHaarWeakGradient N w gw)
    (hcu : Continuous u) (hcw : Continuous w) :
    IsParticleHaarWeakGradient N (fun x => u x * w x) (fun x => w x • gu x + u x • gw x) :=
  isParticleHaarWeakGradient_mul_bdd hu hw (dg_memLp_top hcu) (dg_memLp_top hcw)

/-- Integration by parts between two `H¹(m^N)` functions in the slot `(i, j)`. -/
theorem dg_ibp {u y : ParticleSpace d N → ℝ} {g Y : ParticleSpace d N → Fin N → Tangent d}
    (hu : IsParticleHaarWeakGradient N u g) (hy : IsParticleHaarWeakGradient N y Y)
    (i : Fin N) (j : Fin d) :
    ∫ x, u x * Y x i j ∂particleHaar d N = -∫ x, g x i j * y x ∂particleHaar d N := by
  have hu' := isParticleHaarWeakGradient_iff_weakGradient.1 hu
  have hy' := isParticleHaarWeakGradient_iff_weakGradient.1 hy
  have h := ibp_H1 hu' hy' (particleIdx d N (i, j))
  have hint : ∀ F : Torus ((N : ℕ) * d) → ℝ,
      ∫ x, F (particleTorusEquiv d N x) ∂particleHaar d N = ∫ z, F z ∂haar ((N : ℕ) * d) :=
    fun F => (measurePreserving_particleTorusEquiv d N).integral_comp' F
  rw [← hint, ← hint] at h
  simpa [particleGradT_apply, Function.comp_def] using h

/-! ### The cylinder coordinates and the chain rule -/

/-- The normalised empirical coordinates `Z_i = N^{-1/2} ∑ₗ vᵢ(X_l)`. -/
noncomputable def dualZ (N : ℕ+) {n : ℕ} (v : Fin n → Torus d → ℝ) (x : ParticleSpace d N) :
    Fin n → ℝ := fun i => (Real.sqrt (N : ℝ))⁻¹ * ∑ l, v i (x l)

/-- The first partial derivative of a cylinder function. -/
noncomputable def dc {n : ℕ} (c : (Fin n → ℝ) → ℝ) (i : Fin n) (z : Fin n → ℝ) : ℝ :=
  fderiv ℝ c z (Pi.single i 1)

theorem dg_c1 {ψ : ParticleSpace d N → ℝ} (hψ : ContDiff ℝ 1 (ψ ∘ particleLift)) :
    IsParticleHaarWeakGradient N ψ (fun x i => WithLp.toLp 2 fun j => particlePartial i j ψ x) := by
  have h1 : IsC1Periodic (ψ ∘ (particleTorusEquiv d N).symm) := by
    have : (ψ ∘ (particleTorusEquiv d N).symm) ∘ torusLift =
        (ψ ∘ particleLift) ∘ (particleLinEquiv d N).symm := by
      funext z
      simp [particleTorusEquiv_symm_lift]
    unfold IsC1Periodic
    rw [this]
    exact hψ.comp (particleLinEquiv d N).symm.contDiff
  rw [isParticleHaarWeakGradient_iff_weakGradient]
  have h2 := h1.isWeakGradient
  have h3 : particleGradT (fun x i => (WithLp.toLp 2 fun j => particlePartial i j ψ x :
      Tangent d)) = smoothGrad (ψ ∘ (particleTorusEquiv d N).symm) := by
    funext z
    ext k
    rw [particleGradT_apply, smoothGrad_apply]
    simp only
    have := particlePartial_eq_coordPartial ψ ((particleIdx d N).symm k).1
      ((particleIdx d N).symm k).2 ((particleTorusEquiv d N).symm z)
    simpa using this
  rw [h3]
  exact h2

/-- The lifted coordinate map. -/
noncomputable def dualZl (N : ℕ+) {n : ℕ} (v : Fin n → Torus d → ℝ) (y : Fin N → Fin d → ℝ) :
    Fin n → ℝ := fun i => (Real.sqrt (N : ℝ))⁻¹ * ∑ l, (v i ∘ torusLift) (y l)

theorem dualZl_contDiff {n : ℕ} {v : Fin n → Torus d → ℝ} (hv : ∀ i, IsC1Periodic (v i)) :
    ContDiff ℝ 1 (dualZl N v) := by
  refine contDiff_pi.2 fun i => ?_
  refine contDiff_const.mul (ContDiff.sum fun l _ => ?_)
  exact (hv i).comp (contDiff_apply ℝ _ l)

theorem dualZl_hasFDerivAt {n : ℕ} {v : Fin n → Torus d → ℝ} (hv : ∀ i, IsC1Periodic (v i))
    (y : Fin N → Fin d → ℝ) :
    HasFDerivAt (dualZl N v)
      (ContinuousLinearMap.pi fun i => (Real.sqrt (N : ℝ))⁻¹ •
        ∑ l, (fderiv ℝ (v i ∘ torusLift) (y l)).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin d → ℝ) l)) y := by
  rw [hasFDerivAt_pi']
  intro i
  have h1 : ∀ l : Fin N, HasFDerivAt (fun y' : Fin N → Fin d → ℝ => (v i ∘ torusLift) (y' l))
      ((fderiv ℝ (v i ∘ torusLift) (y l)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin d → ℝ) l)) y := by
    intro l
    have hg : HasFDerivAt (v i ∘ torusLift) (fderiv ℝ (v i ∘ torusLift) (y l)) (y l) :=
      (((hv i).differentiable one_ne_zero) (y l)).hasFDerivAt
    exact hg.comp y (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin N => Fin d → ℝ) l).hasFDerivAt
  have h2 := (HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => h1 l).const_mul
    (Real.sqrt (N : ℝ))⁻¹
  refine h2.congr_fderiv ?_
  ext h
  simp

theorem particlePartial_comp_dualZ {n : ℕ} {v : Fin n → Torus d → ℝ}
    (hv : ∀ i, IsC1Periodic (v i)) {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ContDiff ℝ 1 ((fun x => φ (dualZ N v x)) ∘ particleLift) ∧
    ∀ (l : Fin N) (j : Fin d) (x : ParticleSpace d N),
      particlePartial l j (fun x => φ (dualZ N v x)) x =
        (Real.sqrt (N : ℝ))⁻¹ * ∑ i, fderiv ℝ φ (dualZ N v x) (Pi.single i 1) *
          coordPartial j (v i) (x l) := by
  have hcomp : ((fun x => φ (dualZ N v x)) ∘ particleLift) = φ ∘ dualZl N v := by
    funext y
    show φ (dualZ N v (particleLift y)) = φ (dualZl N v y)
    rw [show dualZ N v (particleLift y) = dualZl N v y from by
      funext i
      simp [dualZ, dualZl, particleLift]]
  refine ⟨hcomp ▸ hφ.comp (dualZl_contDiff hv), ?_⟩
  intro l j x
  unfold particlePartial
  rw [hcomp]
  set y0 : Fin N → Fin d → ℝ := fun k => SharpLSI.secT (x k) with hy0
  have hz : dualZl N v y0 = dualZ N v x := by
    funext i
    simp [dualZ, dualZl, y0, SharpLSI.liftT_secT]
  have hD := (hφ.differentiable one_ne_zero (dualZl N v y0)).hasFDerivAt.comp y0
    (dualZl_hasFDerivAt hv y0)
  rw [hD.fderiv, ContinuousLinearMap.comp_apply, hz]
  set w : Fin n → ℝ := (ContinuousLinearMap.pi fun i => (Real.sqrt (N : ℝ))⁻¹ •
        ∑ l', (fderiv ℝ (v i ∘ torusLift) (y0 l')).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin d → ℝ) l'))
      (Pi.single l (Pi.single j (1 : ℝ))) with hw
  have hwi : ∀ i, w i = (Real.sqrt (N : ℝ))⁻¹ * coordPartial j (v i) (x l) := by
    intro i
    simp only [hw, ContinuousLinearMap.pi_apply, smul_apply,
      sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul]
    congr 1
    rw [Finset.sum_eq_single l]
    · simp [coordPartial, y0]
    · intro b _ hb
      simp [hb]
    · simp
  have hsum : w = ∑ i, w i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, hwi]
  ring

theorem dg_cyl {n : ℕ} {v : Fin n → Torus d → ℝ} (hv : ∀ i, IsC1Periodic (v i))
    {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    IsParticleHaarWeakGradient N (fun x => φ (dualZ N v x))
      (fun x l => WithLp.toLp 2 fun j => (Real.sqrt (N : ℝ))⁻¹ *
        ∑ i, fderiv ℝ φ (dualZ N v x) (Pi.single i 1) * coordPartial j (v i) (x l)) := by
  obtain ⟨h1, h2⟩ := particlePartial_comp_dualZ (N := N) hv hφ
  have := dg_c1 h1
  simp only [h2] at this
  exact this

theorem continuous_dualZ {n : ℕ} {v : Fin n → Torus d → ℝ} (hv : ∀ i, IsC1Periodic (v i)) :
    Continuous (dualZ N v : ParticleSpace d N → Fin n → ℝ) := by
  refine continuous_pi fun i => continuous_const.mul (continuous_finsetSum _ fun l _ => ?_)
  exact (hv i).continuous_torus.comp (continuous_apply l)

/-! ### The Gibbs density -/

/-- The mean-field interaction part of the Hamiltonian. -/
noncomputable def particleInteraction (A : InteractionData d) (N : ℕ+) (x : ParticleSpace d N) :
    ℝ := (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, A.W (x i) (x j)

theorem particleHamiltonian_eq (A : InteractionData d) (N : ℕ+) :
    particleHamiltonian A N = fun x => ∑ l, A.V (x l) + particleInteraction A N x := rfl

theorem dg_hamiltonian (A : InteractionData d) {gV : Torus d → Tangent d}
    (hgV : IsWeakGradient A.V gV) {gU : ParticleSpace d N → Fin N → Tangent d}
    (hgU : IsParticleHaarWeakGradient N (particleInteraction A N) gU) :
    IsParticleHaarWeakGradient N (particleHamiltonian A N) (fun x l => gV (x l) + gU x l) := by
  classical
  have h1 := dg_sum (N := N) (Finset.univ : Finset (Fin N)) (fun l _ => dg_slot l hgV)
  have h2 := dg_add h1 hgU
  rw [particleHamiltonian_eq]
  convert h2 using 1
  funext x k
  simp [Finset.sum_apply]

theorem dg_density (A : InteractionData d) {g : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (particleHamiltonian A N) g) :
    IsParticleHaarWeakGradient N (particleDensity A N) (fun x => (-particleDensity A N x) • g x) := by
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
  set F : ℝ → ℝ := fun t => (particlePartition A N)⁻¹ * Real.exp (-t) with hF
  have hFd : ContDiffOn ℝ ∞ F (Set.Icc (-M) (M + 1)) :=
    (contDiff_const.mul (Real.contDiff_exp.comp contDiff_neg)).contDiffOn
  have hch := chain_rule_of_cont_rep
    (u := particleHamiltonian A N ∘ (particleTorusEquiv d N).symm) hU
    ((particleHamiltonian_continuous A N).comp continuous_particleTorusEquiv_symm)
    (Filter.Eventually.of_forall fun _ => rfl) hab hrng hFd
  have hd : ∀ t ∈ Set.Icc (-M) (M + 1),
      derivWithin F (Set.Icc (-M) (M + 1)) t = -((particlePartition A N)⁻¹ * Real.exp (-t)) := by
    intro t ht
    have h1 : HasDerivAt F (-((particlePartition A N)⁻¹ * Real.exp (-t))) t := by
      have := (((hasDerivAt_id t).neg).exp).const_mul (particlePartition A N)⁻¹
      simpa using this
    rw [h1.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht)]
  rw [show (fun x : ParticleSpace d N => (-particleDensity A N x) • g x) =
    fun x => (fun x => -particleDensity A N x) x • g x from rfl, particleGradT_smul]
  refine hch.congr_ae (Filter.Eventually.of_forall fun z => rfl)
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, hd _ (hrng z), particleDensity]

/-! ### The Laplacian identity for the eigenfunctions -/

theorem dg_laplacian_ae {u g : Torus d → ℝ} {G : Torus d → Tangent d}
    {H : Fin d → Fin d → Torus d → ℝ} (hH : IsWeakHessian u G H) (hl : IsWeakLaplacian u g) :
    (fun x => ∑ j, H j j x) =ᵐ[haar d] g := by
  have hmem : MemLp (fun x => (∑ j, H j j x) - g x) 2 (haar d) :=
    (memLp_finsetSum Finset.univ fun j _ => hH.memLp_hess j j).sub hl.memLp_lap
  have h0 : (fun x => (∑ j, H j j x) - g x) =ᵐ[haar d] 0 := by
    refine ae_eq_zero_of_forall_integral_mul_eq_zero hmem fun φ hφ => ?_
    have hint : ∀ j, Integrable (fun x => H j j x * φ x) (haar d) := fun j =>
      integrable_mul_of_memLp_two (hH.memLp_hess j j) hφ.memLp_top
    have e1 : ∀ j, ∫ x, H j j x * φ x ∂haar d =
        ∫ x, u x * coordPartial j (coordPartial j φ) x ∂haar d := by
      intro j
      have a := hH.grad.ibp (coordPartial j φ) (hφ.isSmoothPeriodic_coordPartial j) j
      have b := hH.ibp j j φ hφ
      rw [a]
      linarith
    have e2 : ∫ x, u x * periodicLaplacian φ x ∂haar d =
        ∑ j, ∫ x, u x * coordPartial j (coordPartial j φ) x ∂haar d := by
      unfold periodicLaplacian
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum]
      intro j _
      exact integrable_mul_of_memLp_two hH.grad.memLp
        ((hφ.isSmoothPeriodic_coordPartial j).isSmoothPeriodic_coordPartial j).memLp_top
    have e3 : ∫ x, (∑ j, H j j x) * φ x ∂haar d = ∑ j, ∫ x, H j j x * φ x ∂haar d := by
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum _ fun j _ => hint j
    have e4 := hl.ibp φ hφ
    have hI1 : Integrable (fun x => (∑ j, H j j x) * φ x) (haar d) := by
      simp_rw [Finset.sum_mul]
      exact integrable_finsetSum _ fun j _ => hint j
    have hI2 : Integrable (fun x => g x * φ x) (haar d) :=
      integrable_mul_of_memLp_two hl.memLp_lap hφ.memLp_top
    simp_rw [sub_mul]
    rw [integral_sub hI1 hI2, e3, Finset.sum_congr rfl fun j _ => e1 j, ← e2, e4]
    ring
  filter_upwards [h0] with x hx
  simpa [sub_eq_zero] using hx

/-! ### The pointwise algebra -/

theorem dg_pointwise {n d N : ℕ} (s ρ : ℝ) (hs : s * s = (N : ℝ)⁻¹)
    (Gf Hs : Fin n → Fin N → Fin d → ℝ) (gV gU : Fin N → Fin d → ℝ) (vv : Fin n → Fin N → ℝ)
    (a lam : Fin n → ℝ) (dc2 : Fin n → Fin n → ℝ)
    (hl : ∀ i l, ∑ j, Hs i l j = ∑ j, gV l j * Gf i l j - lam i * vv i l) :
    ∑ l, ∑ j, ((∑ i, s * (a i * Gf i l j)) * (-ρ * (gV l j + gU l j)) +
      ρ * ∑ i, s * (Gf i l j * (s * ∑ p, dc2 i p * Gf p l j) + a i * Hs i l j)) =
    -ρ * (∑ i, lam i * (s * ∑ l, vv i l) * a i -
      ∑ i, ∑ k, ((N : ℝ)⁻¹ * ∑ l, ∑ j, Gf i l j * Gf k l j) * dc2 i k +
      ∑ i, (s * ∑ l, ∑ j, gU l j * Gf i l j) * a i) := by
  have h1 : ∀ l j, ((∑ i, s * (a i * Gf i l j)) * (-ρ * (gV l j + gU l j)) +
      ρ * ∑ i, s * (Gf i l j * (s * ∑ p, dc2 i p * Gf p l j) + a i * Hs i l j)) =
      ∑ i, (-(ρ * s * a i * (gV l j * Gf i l j)) - ρ * s * a i * (gU l j * Gf i l j) +
        ∑ p, ρ * (s * s) * (dc2 i p * (Gf i l j * Gf p l j)) + ρ * s * (a i * Hs i l j)) := by
    intro l j
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have eT : Gf i l j * (s * ∑ p, dc2 i p * Gf p l j) =
        s * ∑ p, dc2 i p * (Gf i l j * Gf p l j) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [eT, show ∑ p, ρ * (s * s) * (dc2 i p * (Gf i l j * Gf p l j)) =
      ρ * (s * s) * ∑ p, dc2 i p * (Gf i l j * Gf p l j) from (Finset.mul_sum _ _ _).symm]
    ring
  have sw : ∀ f : Fin N → Fin d → Fin n → ℝ,
      ∑ l, ∑ j, ∑ i, f l j i = ∑ i, ∑ l, ∑ j, f l j i := by
    intro f
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d))) (t := (Finset.univ : Finset (Fin n)))]
    rw [Finset.sum_comm]
  have sw2 : ∀ f : Fin N → Fin d → Fin n → Fin n → ℝ,
      ∑ l, ∑ j, ∑ i, ∑ p, f l j i p = ∑ i, ∑ p, ∑ l, ∑ j, f l j i p := by
    intro f
    rw [sw (fun l j i => ∑ p, f l j i p)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d))) (t := (Finset.univ : Finset (Fin n)))]
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => h1 l j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [sw (fun l j i => ρ * s * a i * (gV l j * Gf i l j)),
    sw (fun l j i => ρ * s * a i * (gU l j * Gf i l j)),
    sw2 (fun l j i p => ρ * (s * s) * (dc2 i p * (Gf i l j * Gf p l j))),
    sw (fun l j i => ρ * s * (a i * Hs i l j))]
  have hP4 : ∀ i, ∑ l, ∑ j, ρ * s * (a i * Hs i l j) =
      ρ * s * a i * (∑ l, ∑ j, gV l j * Gf i l j - lam i * ∑ l, vv i l) := by
    intro i
    have : ∑ l, ∑ j, ρ * s * (a i * Hs i l j) = ρ * s * a i * ∑ l, ∑ j, Hs i l j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    congr 1
    rw [Finset.sum_congr rfl fun l _ => hl i l, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ => hP4 i]
  have c1 : ∀ (X : Fin N → Fin d → Fin n → ℝ) (i : Fin n),
      ∑ l, ∑ j, ρ * s * a i * X l j i = ρ * s * a i * ∑ l, ∑ j, X l j i := by
    intro X i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ => c1 (fun l j i => gV l j * Gf i l j) i,
    Finset.sum_congr rfl fun i _ => c1 (fun l j i => gU l j * Gf i l j) i]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hW : ∀ p, ∑ l, ∑ j, ρ * (s * s) * (dc2 i p * (Gf i l j * Gf p l j)) =
      ρ * (((N : ℝ)⁻¹ * ∑ l, ∑ j, Gf i l j * Gf p l j) * dc2 i p) := by
    intro p
    have : ∑ l, ∑ j, ρ * (s * s) * (dc2 i p * (Gf i l j * Gf p l j)) =
        ρ * (s * s) * dc2 i p * ∑ l, ∑ j, Gf i l j * Gf p l j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, ← hs]
    ring
  rw [Finset.sum_congr rfl fun p _ => hW p, ← Finset.mul_sum]
  ring

/-! ### The dual generator -/

/-- The second partial derivative `∂_k ∂_i c` of a cylinder function. -/
noncomputable def dc2 {n : ℕ} (c : (Fin n → ℝ) → ℝ) (i k : Fin n) (z : Fin n → ℝ) : ℝ :=
  fderiv ℝ (dc c i) z (Pi.single k 1)

/-- The carré du champ matrix `A_{ik} = N⁻¹ ∑ₗ ∇eᵢ(X_l) · ∇eₖ(X_l)`. -/
noncomputable def dualA (N : ℕ+) {n : ℕ} (v : Fin n → Torus d → ℝ) (i k : Fin n)
    (x : ParticleSpace d N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ l, ⟪smoothGrad (v i) (x l), smoothGrad (v k) (x l)⟫_ℝ

/-- The drift coefficient `D_i = N^{-1/2} ∑ₗ ∇_l U_N · ∇eᵢ(X_l)`. -/
noncomputable def dualD (N : ℕ+) {n : ℕ} (v : Fin n → Torus d → ℝ)
    (gU : ParticleSpace d N → Fin N → Tangent d) (i : Fin n) (x : ParticleSpace d N) : ℝ :=
  (Real.sqrt (N : ℝ))⁻¹ * ∑ l, ⟪gU x l, smoothGrad (v i) (x l)⟫_ℝ

/-- The particle generator `G_N c` of a cylinder function `c(Z_N)`:
`∑ᵢ λᵢ Z_i ∂ᵢ c - ∑ᵢₖ A_{ik} ∂ᵢₖ c + ∑ᵢ D_i ∂ᵢ c`, evaluated at `Z_N(x)`. -/
noncomputable def dualGen (N : ℕ+) {n : ℕ} (lam : Fin n → ℝ) (v : Fin n → Torus d → ℝ)
    (c : (Fin n → ℝ) → ℝ) (gU : ParticleSpace d N → Fin N → Tangent d) (x : ParticleSpace d N) :
    ℝ :=
  ∑ i, lam i * dualZ N v x i * dc c i (dualZ N v x) -
    ∑ i, ∑ k, dualA N v i k x * dc2 c i k (dualZ N v x) +
    ∑ i, dualD N v gU i x * dc c i (dualZ N v x)

theorem contDiff_dc {n : ℕ} {c : (Fin n → ℝ) → ℝ} (hc : ContDiff ℝ 2 c) (i : Fin n) :
    ContDiff ℝ 1 (dc c i) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ c) := hc.fderiv_right (by norm_num)
  exact h1.clm_apply contDiff_const

theorem dg_psi (A : InteractionData d) {n : ℕ} {v : Fin n → Torus d → ℝ}
    {H : Fin n → Fin d → Fin d → Torus d → ℝ}
    (hv : ∀ i, IsC1Periodic (v i)) (hH : ∀ i, IsWeakHessian (v i) (smoothGrad (v i)) (H i))
    {c : (Fin n → ℝ) → ℝ} (hc : ContDiff ℝ 2 c)
    {gV : Torus d → Tangent d} {gU : ParticleSpace d N → Fin N → Tangent d}
    (hgV : IsWeakGradient A.V gV)
    (hgU : IsParticleHaarWeakGradient N (particleInteraction A N) gU) (l : Fin N) (j : Fin d) :
    ∃ g : ParticleSpace d N → Fin N → Tangent d,
      IsParticleHaarWeakGradient N (fun x => particleDensity A N x *
        ∑ i, (Real.sqrt (N : ℝ))⁻¹ * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) g ∧
      ∀ x, g x l j =
        (∑ i, (Real.sqrt (N : ℝ))⁻¹ * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
          (-particleDensity A N x * (gV (x l) j + gU x l j)) +
        particleDensity A N x * ∑ i, (Real.sqrt (N : ℝ))⁻¹ *
          (smoothGrad (v i) (x l) j * ((Real.sqrt (N : ℝ))⁻¹ *
            ∑ p, dc2 c i p (dualZ N v x) * smoothGrad (v p) (x l) j) +
            dc c i (dualZ N v x) * H i j j (x l)) := by
  classical
  have hρ := dg_density A (dg_hamiltonian A hgV hgU)
  have hρc : Continuous (particleDensity A N) := particleDensity_continuous A N
  have ha : ∀ i, IsParticleHaarWeakGradient N (fun x => dc c i (dualZ N v x)) _ :=
    fun i => dg_cyl hv (contDiff_dc hc i)
  have hq : ∀ i, IsParticleHaarWeakGradient N (fun x : ParticleSpace d N => smoothGrad (v i) (x l) j)
      _ := fun i => dg_slot l (hessian_col (hH i) j)
  have hac : ∀ i, Continuous (fun x : ParticleSpace d N => dc c i (dualZ N v x)) := fun i =>
    ((contDiff_dc hc i).continuous).comp (continuous_dualZ hv)
  have hqc : ∀ i, Continuous (fun x : ParticleSpace d N => smoothGrad (v i) (x l) j) := fun i => by
    simp only [smoothGrad_apply]
    exact ((hv i).continuous_coordPartial j).comp (continuous_apply l)
  have hprod := fun i => dg_mul (ha i) (hq i) (hac i) (hqc i)
  have hterm := fun i => dg_smul (hprod i) (Real.sqrt (N : ℝ))⁻¹
  have hsum := dg_sum (N := N) Finset.univ (fun i _ => hterm i)
  have hΨc : Continuous (fun x : ParticleSpace d N =>
      ∑ i, (Real.sqrt (N : ℝ))⁻¹ * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul ((hac i).mul (hqc i))
  have hfin := dg_mul hρ hsum hρc hΨc
  refine ⟨_, hfin, fun x => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sum, smoothGrad_apply]
  simp [vecOf, dc2]

/-! ### The energy inequality -/

theorem dg_energy (A : InteractionData d) (f F : ParticleH1 A N)
    {gf gF : ParticleSpace d N → Fin N → Tangent d}
    (hf : IsParticleWeakGradient A N f.1 gf) (hF : IsParticleWeakGradient A N F.1 gF) :
    2 * ∫ x, ∑ i, ∑ j, gf x i j * gF x i j ∂particleLaw A N ≤
      particleEnergy A N f + particleEnergy A N F := by
  have hfc : ∀ i j, MemLp (fun x => gf x i j) 2 (particleLaw A N) :=
    fun i j => memLp_particleCoord hf.memLp_grad i j
  have hFc : ∀ i j, MemLp (fun x => gF x i j) 2 (particleLaw A N) :=
    fun i j => memLp_particleCoord hF.memLp_grad i j
  have i1 : Integrable (fun x => ∑ i, ∑ j, gf x i j ^ 2) (particleLaw A N) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hfc i j).integrable_sq
  have i2 : Integrable (fun x => ∑ i, ∑ j, gF x i j ^ 2) (particleLaw A N) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hFc i j).integrable_sq
  have i3 : Integrable (fun x => ∑ i, ∑ j, gf x i j * gF x i j) (particleLaw A N) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hfc i j).integrable_mul (hFc i j)
  rw [particleEnergy_eq_of_isParticleWeakGradient f hf,
    particleEnergy_eq_of_isParticleWeakGradient F hF]
  simp only [particleTangentNormSq_eq]
  rw [← integral_add i1 i2, ← integral_const_mul]
  refine integral_mono (i3.const_mul 2) (i1.add i2) fun x => ?_
  simp only [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  nlinarith [sq_nonneg (gf x i j - gF x i j)]


/-! ### The main identity -/

theorem dg_inner (a b : Tangent d) : ⟪a, b⟫_ℝ = ∑ j, a j * b j := by
  simp [PiLp.inner_apply, mul_comm]

theorem dg_slot_ae {p : Torus d → Prop} (h : ∀ᵐ z ∂haar d, p z) (l : Fin N) :
    ∀ᵐ x ∂particleHaar d N, p (x l) :=
  (measurePreserving_eval (fun _ : Fin N => haar d) l).quasiMeasurePreserving.ae h

/-- **Weak particle dual generator identity.**  For a `C²` cylinder `c` of finitely many
`C¹ ∩ H²` eigenfunction coordinates and every `f ∈ H¹(P_N)`,
`E_N(f) ≥ 2 ⟨f, G_N c⟩_{P_N} - E_N(c(Z_N))`. -/
theorem weak_particle_dual_generator_identity (A : InteractionData d) {n : ℕ}
    (lam : Fin n → ℝ) (v : Fin n → Torus d → ℝ) (H : Fin n → Fin d → Fin d → Torus d → ℝ)
    (hv : ∀ i, IsC1Periodic (v i)) (hH : ∀ i, IsWeakHessian (v i) (smoothGrad (v i)) (H i))
    {gV : Torus d → Tangent d} (hgV : IsWeakGradient A.V gV)
    (hlap : ∀ i, IsWeakLaplacian (v i) (fun z => ⟪gV z, smoothGrad (v i) z⟫_ℝ - lam i * v i z))
    {c : (Fin n → ℝ) → ℝ} (hc : ContDiff ℝ 2 c)
    {gU : ParticleSpace d N → Fin N → Tangent d}
    (hgU : IsParticleHaarWeakGradient N (particleInteraction A N) gU) (f : ParticleH1 A N) :
    ∃ hmem : MemParticleH1 A N (fun x => c (dualZ N v x)),
      2 * ∫ x, f.1 x * dualGen N lam v c gU x ∂particleLaw A N -
        particleEnergy A N ⟨_, hmem⟩ ≤ particleEnergy A N f := by
  classical
  set s : ℝ := (Real.sqrt (N : ℝ))⁻¹ with hs
  have hss : s * s = (N : ℝ)⁻¹ := by
    rw [hs, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hc1 : ContDiff ℝ 1 c := hc.of_le (by norm_num)
  obtain ⟨gF, hF1, hgF⟩ : ∃ gF : ParticleSpace d N → Fin N → Tangent d,
      IsParticleHaarWeakGradient N (fun x => c (dualZ N v x)) gF ∧
      ∀ x l j, gF x l j = ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j) :=
    ⟨_, dg_cyl hv hc1, fun x l j => by
      simp [smoothGrad_apply, Finset.mul_sum, dc, hs]⟩
  have hFA := (isParticleWeakGradient_iff A N _ _).2 hF1
  refine ⟨⟨_, hFA⟩, ?_⟩
  have hfA := isParticleWeakGradient_particleWeakGradient f
  have hfH := (isParticleWeakGradient_iff A N _ _).1 hfA
  have hE := dg_energy A f ⟨_, ⟨_, hFA⟩⟩ hfA hFA
  suffices hB : ∫ x, ∑ i, ∑ j, particleWeakGradient f x i j * gF x i j ∂particleLaw A N =
      ∫ x, f.1 x * dualGen N lam v c gU x ∂particleLaw A N by linarith
  have hex := fun l j => dg_psi (N := N) A hv hH hc hgV hgU l j
  choose g hg hgx using hex
  have hρ : Continuous (particleDensity A N) := particleDensity_continuous A N
  have hI1 : ∀ l j, Integrable (fun x => (particleDensity A N x *
      ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
        particleWeakGradient f x l j) (particleHaar d N) := fun l j =>
    (hg l j).memLp.integrable_mul (memLp_particleCoord hfH.memLp_grad l j)
  have hI2 : ∀ l j, Integrable (fun x => g l j x l j * f.1 x) (particleHaar d N) := fun l j =>
    (memLp_particleCoord (hg l j).memLp_grad l j).integrable_mul hfH.memLp
  have hterm : ∀ l j, ∫ x, (particleDensity A N x *
      ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
        particleWeakGradient f x l j ∂particleHaar d N =
      -∫ x, g l j x l j * f.1 x ∂particleHaar d N := fun l j =>
    dg_ibp (hg l j) hfH l j
  -- the a.e. Laplacian identity in every slot
  have hlapae : ∀ i, ∀ᵐ z ∂haar d, ∑ j, H i j j z =
      ⟪gV z, smoothGrad (v i) z⟫_ℝ - lam i * v i z := fun i =>
    dg_laplacian_ae (hH i) (hlap i)
  have hae : ∀ᵐ x ∂particleHaar d N, ∑ l, ∑ j, g l j x l j =
      -particleDensity A N x * dualGen N lam v c gU x := by
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun l => dg_slot_ae (hlapae i) l]
      with x hx
    have hl : ∀ i l, ∑ j, H i j j (x l) =
        ∑ j, gV (x l) j * smoothGrad (v i) (x l) j - lam i * v i (x l) := fun i l => by
      rw [hx i l, dg_inner]
    have e := dg_pointwise (N := N) s (particleDensity A N x) hss
      (fun i l j => smoothGrad (v i) (x l) j) (fun i l j => H i j j (x l))
      (fun l j => gV (x l) j) (fun l j => gU x l j) (fun i l => v i (x l))
      (fun i => dc c i (dualZ N v x)) lam (fun i p => dc2 c i p (dualZ N v x)) hl
    simp only [hgx]
    refine e.trans ?_
    simp only [dualGen, dualA, dualD, dualZ, dg_inner, hs]
  rw [integral_particleLaw, integral_particleLaw]
  have h1 : ∀ x, particleDensity A N x * ∑ i, ∑ j, particleWeakGradient f x i j * gF x i j =
      ∑ l, ∑ j, (particleDensity A N x *
        ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
          particleWeakGradient f x l j := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgF]
    ring
  have h2 : ∑ l, ∑ j, ∫ x, g l j x l j * f.1 x ∂particleHaar d N =
      ∫ x, (∑ l, ∑ j, g l j x l j) * f.1 x ∂particleHaar d N := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ fun j _ => hI2 l j)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_finsetSum _ (fun j _ => hI2 l j)]
  calc ∫ x, particleDensity A N x * ∑ i, ∑ j, particleWeakGradient f x i j * gF x i j
        ∂particleHaar d N
      = ∫ x, ∑ l, ∑ j, (particleDensity A N x *
        ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
          particleWeakGradient f x l j ∂particleHaar d N := integral_congr_ae
          (Filter.Eventually.of_forall h1)
    _ = ∑ l, ∑ j, ∫ x, (particleDensity A N x *
        ∑ i, s * (dc c i (dualZ N v x) * smoothGrad (v i) (x l) j)) *
          particleWeakGradient f x l j ∂particleHaar d N := by
      rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ fun j _ => hI1 l j)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_finsetSum _ (fun j _ => hI1 l j)]
    _ = ∑ l, ∑ j, -∫ x, g l j x l j * f.1 x ∂particleHaar d N :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => hterm l j
    _ = -∫ x, (∑ l, ∑ j, g l j x l j) * f.1 x ∂particleHaar d N := by
      rw [← h2]
      simp [Finset.sum_neg_distrib]
    _ = ∫ x, particleDensity A N x * (f.1 x * dualGen N lam v c gU x) ∂particleHaar d N := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
      ring

end DGPS.Lipschitz
