import DGPS.Examples.RoughBoundary.Regularity
import DGPS.Examples.RoughBoundary.NonlinearSpeciesRate
import DGPS.Examples.RoughBoundary.ParticleRate
import DGPS.Examples.RoughBoundary.BottleneckPrefactorRUF048
import DGPS.Examples.RoughBoundary.FreeEnergy
import DGPS.Examples.RoughBoundary.SemicontinuityCountersequence
import DGPS.Examples.RoughBoundary.LandscapeSelection
import DGPS.Analysis.RateTopology

/-!
# Fixed rough counterexample: final assembly (RUF049)

Assembles the integrated RUF modules into the frozen statement `T03`,
`DGPS.RegularityBoundary.rough_counterexample_fixed`. The parameter is the finite choice
`L_fixed` selected by RUF026, with `ε = 1/L_fixed` and kernel `W = (11/12)|U(x) - U(y)|²`.

Consumed: RUF009 (`H¹` obstruction), RUF026 (parameter selection), RUF033 and RUF036 (scalar and
species rates), RUF038 (particle sandwich), RUF048 (bottleneck prefactor).

New content beyond the assembly: a uniform positive-definiteness lemma for the Hessian near a
nondegenerate remote minimum (`hess_ball_RUF049`) and the ENNReal squeeze
(`tendsto_particle_zero_RUF049`).
-/

open MeasureTheory Set Filter Topology Metric
open scoped Real ENNReal NNReal ContDiff

namespace DGPS.RegularityBoundary

/-- Hölder membership on the product torus: `f ∈ C^α` for a real exponent `α`. -/
def HolderClass (α : ℝ) : Set (Torus 2 → ℝ) :=
  {f | ∃ C : ℝ≥0, HolderWith C (Real.toNNReal α) f}

/-- Weak `W^{1,p}` membership on the product torus. -/
def WeakSobolevOne (p : ℝ) : Set (Torus 2 → ℝ) :=
  {u | ∃ g : Torus 2 → Tangent 2, IsWeakGradientLp (ENNReal.ofReal p) u g}

end DGPS.RegularityBoundary

namespace DGPS.Models

open DGPS.Analysis.RateTopology (RoughKernelClass pairPt)
open DGPS.Examples.RoughBoundary.Model
  (kappa cU cU_nonneg modelW_holder modelW_symm modelW_diag Wtor Wtor_pairPt
    isWeakGradientLp_Wtor gradW modelData continuous_Wtor)
open DGPS.Examples.RoughBoundary.Landscape
  (kappa0 RoughLandscapeCertificate PotentialLandscapeCertificate)
open DGPS.Examples.RoughBoundary.Semicontinuity (featurePotential)
open DGPS.Examples.RoughBoundary.Feature (Ufeat)

/-- A selected finite parameter choice (RUF026): a length `L > 0` whose primary feature
`U_{L,1/L}` carries the landscape certificate. The interaction is built with `ε = 1/L`. -/
structure RoughFiniteChoice where
  L : ℝ
  hL : 0 < L
  cert : RoughLandscapeCertificate (Ufeat L (1 / L))

/-- The fixed rough kernel `W_{L,1/L}` of a choice, as an element of the rough class `K`. -/
noncomputable def roughFixed (c : RoughFiniteChoice) : RoughKernelClass where
  W := Wtor c.L (1 / c.L)
  continuous := continuous_Wtor c.hL _
  symm := fun x y => by rw [Wtor_pairPt, Wtor_pairPt, modelW_symm]
  diag := fun x => by rw [Wtor_pairPt, modelW_diag]
  sobolev := ⟨gradW c.L (1 / c.L), by
    have h := isWeakGradientLp_Wtor c.hL (1 / c.L) (le_refl (1 : ℝ)) one_lt_two
    rwa [ENNReal.ofReal_one] at h⟩

/-- The canonical weak-drift provider of the fixed rough kernel. -/
noncomputable def roughFixedDrift (c : RoughFiniteChoice) :
    DGPS.AbsoluteDrift (roughFixed c).toInteraction :=
  (roughFixed c).drift

lemma roughFixed_interaction_RUF049 (c : RoughFiniteChoice) :
    (roughFixed c).toInteraction = modelData c.hL (1 / c.L) := by
  apply DGPS.InteractionData.ext rfl
  funext x y
  exact Wtor_pairPt c.L (1 / c.L) x y

lemma scalarRate_transport_RUF049 {A B : DGPS.InteractionData 1} (h : A = B)
    (b : DGPS.AbsoluteDrift A) (b' : DGPS.AbsoluteDrift B) :
    DGPS.scalarRate A b = DGPS.scalarRate B b' := by
  subst h
  exact DGPS.Analysis.RateTopology.scalarRate_eq_of_providers b b'

lemma speciesRate_transport_RUF049 {A B : DGPS.InteractionData 1} (h : A = B)
    (b : DGPS.AbsoluteDrift A) (b' : DGPS.AbsoluteDrift B) :
    DGPS.speciesRate A b = DGPS.speciesRate B b' := by
  subst h
  exact DGPS.Analysis.RateTopology.speciesRate_eq_of_providers b b'

/-- A critical point of `F` at which the Hessian is positive definite has a uniform Hessian lower
bound on a closed ball around it. -/
lemma hess_ball_RUF049 {F : EuclideanSpace ℝ (Fin 2) → ℝ} (hF : ContDiff ℝ ∞ F)
    {t0 : EuclideanSpace ℝ (Fin 2)}
    (hpos : ∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ F) t0 v v) :
    ∃ r : ℝ, 0 < r ∧ ∃ lam : ℝ, 0 < lam ∧
      ∀ x ∈ closedBall t0 r, ∀ v : EuclideanSpace ℝ (Fin 2),
        lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hHc : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    (hF2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hcont : Continuous fun v : EuclideanSpace ℝ (Fin 2) => fderiv ℝ (fderiv ℝ F) t0 v v := by
    fun_prop
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu
    exact zero_ne_one hu
  have hmpos : 0 < fderiv ℝ (fderiv ℝ F) t0 u u := hpos u hu0
  have hscale : ∀ (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)),
      fderiv ℝ (fderiv ℝ F) t0 (c • v) (c • v) = c ^ 2 * fderiv ℝ (fderiv ℝ F) t0 v v := by
    intro c v
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hlow : ∀ v : EuclideanSpace ℝ (Fin 2),
      fderiv ℝ (fderiv ℝ F) t0 u u * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) t0 v v := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp
    · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hwmem : ‖v‖⁻¹ • v ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 : fderiv ℝ (fderiv ℝ F) t0 u u ≤
          fderiv ℝ (fderiv ℝ F) t0 (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := isMinOn_iff.mp hmin _ hwmem
      have key := hscale ‖v‖ (‖v‖⁻¹ • v)
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at key
      rw [key]
      nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖v‖)]
  have hcontAt : ContinuousAt (fderiv ℝ (fderiv ℝ F)) t0 := hHc.continuousAt
  have hball := (Metric.continuousAt_iff (f := fderiv ℝ (fderiv ℝ F)) (a := t0)).mp hcontAt
    (fderiv ℝ (fderiv ℝ F) t0 u u / 2) (by linarith)
  obtain ⟨δ, hδ, hδH⟩ := hball
  refine ⟨δ / 2, half_pos hδ, fderiv ℝ (fderiv ℝ F) t0 u u / 2, by linarith, fun x hx v => ?_⟩
  have hxd : dist x t0 < δ := lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith)
  have hHx : ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) t0‖ <
      fderiv ℝ (fderiv ℝ F) t0 u u / 2 := by
    exact (dist_eq_norm (fderiv ℝ (fderiv ℝ F) x) (fderiv ℝ (fderiv ℝ F) t0)).symm.trans_lt
      (hδH hxd)
  have hop := ContinuousLinearMap.le_opNorm₂
    (fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) t0) v v
  rw [sub_apply, sub_apply] at hop
  have h2 : ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) t0‖ * ‖v‖ * ‖v‖ ≤
      fderiv ℝ (fderiv ℝ F) t0 u u / 2 * ‖v‖ * ‖v‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHx.le (norm_nonneg v)) (norm_nonneg v)
  have hA : ‖fderiv ℝ (fderiv ℝ F) x v v - fderiv ℝ (fderiv ℝ F) t0 v v‖ ≤
      fderiv ℝ (fderiv ℝ F) t0 u u / 2 * ‖v‖ ^ 2 := by
    nlinarith [hop, h2]
  rw [Real.norm_eq_abs] at hA
  have hab := abs_le.mp hA
  nlinarith [hab.1, hlow v]

/-- A critical point of a potential satisfying the landscape certificate: the remote minimum
`aM 0` is a nonzero critical point with positive definite Hessian. -/
lemma remote_critical_RUF049 {F : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hcert : PotentialLandscapeCertificate F) :
    ∃ t : EuclideanSpace ℝ (Fin 2), fderiv ℝ F t = 0 ∧ t ≠ 0 ∧
      ∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ F) t v v := by
  obtain ⟨-, -, -, hzero, -, -, hloc⟩ := hcert
  obtain ⟨Δ, B, aM, aS, hΔ, hΔB, -, -, hcM, -, -, -, hHM, -, -, -, hlow, -⟩ := hloc
  have hF0 : F 0 = 0 := (hzero 0).mpr rfl
  have hne : aM 0 ≠ 0 := by
    intro h
    have h1 := hlow 0
    rw [h, hF0] at h1
    linarith
  exact ⟨aM 0, hcM 0, hne, fun v hv => hHM 0 v hv⟩

/-- Tendsto of an ENNReal sequence dominated by `K N⁻² e^{-bN}`. -/
lemma tendsto_particle_zero_RUF049 {r : ℕ+ → ℝ≥0∞} {K b : ℝ} {N₀ : ℕ} (hb : 0 < b)
    (hle : ∀ N : ℕ+, N₀ ≤ (N : ℕ) →
      r N ≤ ENNReal.ofReal (K * (((N : ℕ) : ℝ) ^ 2)⁻¹ * Real.exp (-(((N : ℕ) : ℝ) * b)))) :
    Tendsto r atTop (𝓝 0) := by
  have hKN : Tendsto (fun N : ℕ+ => (N : ℕ)) atTop atTop :=
    tendsto_atTop_atTop.mpr fun n => ⟨⟨n + 1, Nat.succ_pos n⟩, fun N hN => by
      have h1 : n + 1 ≤ (N : ℕ) := hN
      omega⟩
  have hK : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hKN
  have hinv : Tendsto (fun N : ℕ+ => (((N : ℕ) : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp hK)
  have hexp : Tendsto (fun N : ℕ+ => Real.exp (-(((N : ℕ) : ℝ) * b))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hK.atTop_mul_const hb)
  have hg := (hinv.mul hexp).const_mul K
  simp only [mul_zero] at hg
  have hE := ENNReal.tendsto_ofReal hg
  rw [ENNReal.ofReal_zero] at hE
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE ?_ ?_
  · exact Filter.Eventually.of_forall fun N => zero_le
  · refine Filter.eventually_atTop.2 ⟨⟨N₀ + 1, Nat.succ_pos N₀⟩, fun N hN => ?_⟩
    have h1 : N₀ + 1 ≤ (N : ℕ) := hN
    exact (hle N (by omega)).trans_eq (congrArg ENNReal.ofReal (mul_assoc _ _ _))

/-- The rough counterexample for a fixed choice: all clauses of `T03` for `roughFixed c`. -/
lemma rough_all_RUF049 (c : RoughFiniteChoice) :
    (∀ α : ℝ, 0 < α → α < 1 → (roughFixed c).W ∈ DGPS.RegularityBoundary.HolderClass α) ∧
    (∀ p : ℝ, 1 ≤ p → p < 2 →
      (roughFixed c).W ∈ DGPS.RegularityBoundary.WeakSobolevOne p) ∧
    ¬ ((roughFixed c).W ∈ DGPS.H1Haar 2) ∧
    DGPS.scalarRate (roughFixed c).toInteraction (roughFixedDrift c) =
      ENNReal.ofReal DGPS.a0 ∧
    DGPS.speciesRate (roughFixed c).toInteraction (roughFixedDrift c) =
      ENNReal.ofReal DGPS.a0 ∧
    Tendsto (DGPS.particleRateAll (roughFixed c).toInteraction) atTop (𝓝 0) ∧
    Tendsto (DGPS.particleRateSym (roughFixed c).toInteraction) atTop (𝓝 0) := by
  have hε : (1 / c.L) ≠ 0 := (one_div_pos.mpr c.hL).ne'
  have hA := roughFixed_interaction_RUF049 c
  have hdec := DGPS.Examples.RoughBoundary.FreeEnergy.freeEnergyDecomposition_of_certificate
    (1 / c.L) c.cert
  have bM : DGPS.AbsoluteDrift (modelData c.hL (1 / c.L)) := hA ▸ roughFixedDrift c
  have hscal := (DGPS.Examples.RoughBoundary.Nonlinear.exact_scalar_rate_of_the_rough_example
    c.hL hε hdec bM).1
  have hspec := (DGPS.Examples.RoughBoundary.Nonlinear.exact_arbitrary_finite_species_rate
    c.hL hε hdec bM).1
  have hP : PotentialLandscapeCertificate
      (featurePotential kappa0 (Ufeat c.L (1 / c.L))) := c.cert
  obtain ⟨t, hcrit, ht0, hpos⟩ := remote_critical_RUF049 hP
  obtain ⟨r, hr, lam, hlam, hball⟩ := hess_ball_RUF049 hP.1 hpos
  have hnt : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have hr₀ : 0 < min r (‖t‖ / 2) := lt_min hr (half_pos hnt)
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∉ closedBall t (min r (‖t‖ / 2)) := by
    intro h
    rw [mem_closedBall, dist_zero_left] at h
    have h2 := min_le_right r (‖t‖ / 2)
    linarith
  have hH : ∀ x ∈ closedBall t (min r (‖t‖ / 2)), ∀ v : EuclideanSpace ℝ (Fin 2),
      lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (featurePotential kappa0 (Ufeat c.L (1 / c.L)))) x v v :=
    fun x hx => hball x (closedBall_subset_closedBall (min_le_left _ _) hx)
  obtain ⟨CG, hCG, JS, hJS, cA, hcA, b0, hb0, N₀, hN⟩ :=
    DGPS.Examples.RoughBoundary.Bottleneck.exact_bottleneck_upper_bound_prefactor c.hL c.cert t
      (min r (‖t‖ / 2)) lam hr₀ hlam hcrit h0 hH
  have hb : 0 < b0 / 2 := half_pos hb0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α h0' h1'
    have hk : 0 ≤ kappa := by unfold kappa; norm_num
    have hM : 0 ≤ kappa * 2 ^ (1 - α / 2) * cU c.L (1 / c.L) α :=
      mul_nonneg (mul_nonneg hk (Real.rpow_nonneg (by norm_num) _)) (cU_nonneg c.hL _ _)
    have hpair : ∀ x y x' y' : Torus 1,
        |(roughFixed c).W (pairPt x y) - (roughFixed c).W (pairPt x' y')| ≤
          kappa * 2 ^ (1 - α / 2) * cU c.L (1 / c.L) α *
            Real.sqrt (DGPS.torusDist x x' ^ 2 + DGPS.torusDist y y' ^ 2) ^
              ((Real.toNNReal α : ℝ≥0) : ℝ) := by
      intro x y x' y'
      rw [Real.coe_toNNReal α h0'.le]
      show |Wtor c.L (1 / c.L) (pairPt x y) - Wtor c.L (1 / c.L) (pairPt x' y')| ≤ _
      rw [Wtor_pairPt, Wtor_pairPt]
      exact modelW_holder c.hL (1 / c.L) h0' h1' x y x' y'
    obtain ⟨C, hC⟩ := DGPS.Examples.RoughBoundary.Semicontinuity.exists_holderWith_of_pair_bound_SEM011
      (D := (roughFixed c).W) (α := Real.toNNReal α) hM hpair
    exact ⟨C, hC⟩
  · intro p hp1 hp2
    exact ⟨gradW c.L (1 / c.L), isWeakGradientLp_Wtor c.hL (1 / c.L) hp1 hp2⟩
  · exact (DGPS.Examples.RoughBoundary.Regularity.bulk_obstruction_to_interaction_h1 c.hL hε
      isOpen_univ univ_nonempty).2.2.2.2.1
  · rw [scalarRate_transport_RUF049 hA (roughFixedDrift c) bM]
    exact hscal
  · rw [speciesRate_transport_RUF049 hA (roughFixedDrift c) bM]
    exact hspec
  · rw [hA]
    exact tendsto_particle_zero_RUF049 hb (fun N hNN =>
      (DGPS.Examples.RoughBoundary.Particle.every_fixed_particle_rate_is_positive_and_finite
        c.hL (1 / c.L) N).2.2.2.2.1.trans (hN N hNN))
  · rw [hA]
    exact tendsto_particle_zero_RUF049 hb (fun N hNN => hN N hNN)

end DGPS.Models

namespace DGPS.RegularityBoundary

/-- **T03 (RUF049): fixed rough counterexample.** For the permanently selected finite parameter
`L_fixed` (RUF026) and `W = (11/12)|U(x) - U(y)|²`, the kernel lies in `C^α` for all
`0 < α < 1`, in `W^{1,p}` for all `1 ≤ p < 2`, and not in `H¹`; both the scalar and the species
rate equal `a0`, and both particle rates tend to zero. -/
theorem rough_counterexample_fixed :
    ∃ choice : DGPS.Models.RoughFiniteChoice,
      let A := DGPS.Models.roughFixed choice
      let b := DGPS.Models.roughFixedDrift choice
      (∀ α : ℝ, 0 < α → α < 1 → A.W ∈ HolderClass α) ∧
      (∀ p : ℝ, 1 ≤ p → p < 2 → A.W ∈ WeakSobolevOne p) ∧
      ¬ (A.W ∈ DGPS.H1Haar 2) ∧
      DGPS.scalarRate A.toInteraction b = ENNReal.ofReal DGPS.a0 ∧
      DGPS.speciesRate A.toInteraction b = ENNReal.ofReal DGPS.a0 ∧
      Tendsto (DGPS.particleRateAll A.toInteraction) atTop (𝓝 0) ∧
      Tendsto (DGPS.particleRateSym A.toInteraction) atTop (𝓝 0) := by
  obtain ⟨-, L₀, -, hL₀, -, -, L_fixed, hLL, -, hcert⟩ :=
    DGPS.Examples.RoughBoundary.Landscape.common_finite_parameter_selection
  have hLpos : 0 < L_fixed := by linarith
  exact ⟨⟨L_fixed, hLpos, hcert⟩, DGPS.Models.rough_all_RUF049 ⟨L_fixed, hLpos, hcert⟩⟩

end DGPS.RegularityBoundary
