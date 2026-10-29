import DGPS.Basic.SquareRootHeatRecovery
import DGPS.Analysis.WeakConvolution
import DGPS.Variational.SpeciesGap
import DGPS.Measure.EntropyChain

/-!
# Joint entropy, energy and score convergence under heat recovery (LIP020)

For a fixed finite species family `F`, applying the heat semigroup `H_t` (`t → 0⁺`) to every
species density preserves finiteness of entropy, makes `H(H_t ρ | m) → H(ρ | m)`, converges the
energies of bounded continuous potentials, and converges the drift-score vectors
`2 ∇u_s + u_s b(ρ̄)` strongly in `L²`; consequently `G_θ` and `D_θ` converge.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Real

namespace DGPS.Lipschitz

open DGPS

variable {d : ℕ}

/-- The heat-flowed absolute density `H_t ρ` (for `t > 0`; junk value `ρ` otherwise). -/
noncomputable def heatDensity (ρ : AbsoluteDensity d) (t : ℝ) : AbsoluteDensity d :=
  if ht : 0 < t then
    { sqrt := fun y => √(heatOp t ρ.density y)
      sqrt_mem := ⟨_, (isSmoothPeriodic_sqrt_heatOp ht ρ.memLp_sqrt ρ.mass_one).isWeakGradient⟩
      sqrt_nonneg := Eventually.of_forall fun _ => Real.sqrt_nonneg _
      mass_one := by
        obtain ⟨-, h2, h3⟩ := heat_density_facts ht ρ.memLp_sqrt ρ.mass_one
        refine Eq.trans (integral_congr_ae (Eventually.of_forall fun y => ?_)) h3
        exact Real.sq_sqrt (h2 y).le }
  else ρ

theorem heatDensity_sqrt {ρ : AbsoluteDensity d} {t : ℝ} (ht : 0 < t) :
    (heatDensity ρ t).sqrt = fun y => √(heatOp t ρ.density y) := by
  simp only [heatDensity, ht, ↓reduceDIte]

theorem heatDensity_density {ρ : AbsoluteDensity d} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    (heatDensity ρ t).density x = heatOp t ρ.density x := by
  obtain ⟨-, h2, -⟩ := heat_density_facts ht ρ.memLp_sqrt ρ.mass_one
  simp only [AbsoluteDensity.density, heatDensity_sqrt ht]
  exact Real.sq_sqrt (h2 x).le

theorem weakGradient_heatDensity {ρ : AbsoluteDensity d} {t : ℝ} (ht : 0 < t) :
    weakGradient (heatDensity ρ t).sqrt (heatDensity ρ t).sqrt_mem =ᵐ[haar d]
      smoothGrad fun y => √(heatOp t ρ.density y) := by
  have hv := isSmoothPeriodic_sqrt_heatOp ht ρ.memLp_sqrt ρ.mass_one
  have h1 := isWeakGradient_weakGradient (heatDensity ρ t).sqrt_mem
  have h2 : IsWeakGradient (heatDensity ρ t).sqrt
      (smoothGrad fun y => √(heatOp t ρ.density y)) := by
    rw [heatDensity_sqrt ht]
    exact hv.isWeakGradient
  exact h1.ae_eq h2
/-! ### Heat-flowed species families -/

/-- The family obtained by applying the heat flow at time `t` to every species density. -/
noncomputable def heatFamily (F : SpeciesFamily d) (t : ℝ) : SpeciesFamily d where
  count := F.count
  weight := F.weight
  weight_pos := F.weight_pos
  weight_sum := F.weight_sum
  density := fun s => heatDensity (F.density s) t

/-! ### L¹ convergence implies weak convergence -/

theorem integral_densityMeasure (ρ : AbsoluteDensity d) (f : Torus d → ℝ) :
    ∫ x, f x ∂(densityMeasure ρ : Measure (Torus d)) = ∫ x, ρ.density x * f x ∂haar d := by
  rw [densityMeasure_coe, integral_withDensity_eq_integral_toReal_smul₀
    ((ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

theorem tendsto_densityMeasure_of_L1 {ι : Type*} {l : Filter ι} (ρt : ι → AbsoluteDensity d)
    (ρ : AbsoluteDensity d)
    (h : Tendsto (fun i => ∫ x, |(ρt i).density x - ρ.density x| ∂haar d) l (𝓝 0)) :
    Tendsto (fun i => densityMeasure (ρt i)) l (𝓝 (densityMeasure ρ)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simp only [integral_densityMeasure]
  have hi : ∀ σ : AbsoluteDensity d, Integrable (fun x => σ.density x * f x) (haar d) := fun σ =>
    (σ.integrable_density.norm.mul_const ‖f‖).mono'
      (σ.integrable_density.aestronglyMeasurable.mul f.continuous.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 := h.const_mul ‖f‖
  rw [mul_zero] at h0
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) h0
  have hint : Integrable (fun x => ‖f‖ * |(ρt i).density x - ρ.density x|) (haar d) :=
    (((ρt i).integrable_density.sub ρ.integrable_density).norm.const_mul ‖f‖)
  rw [← integral_const_mul, ← integral_sub (hi _) (hi _)]
  refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun x => ?_)
  have h1 : |f x| ≤ ‖f‖ := by simpa using f.norm_coe_le_norm x
  calc ‖(ρt i).density x * f x - ρ.density x * f x‖
      = |(ρt i).density x - ρ.density x| * |f x| := by
        rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |(ρt i).density x - ρ.density x| * ‖f‖ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = ‖f‖ * |(ρt i).density x - ρ.density x| := mul_comm _ _

theorem tendsto_L1_heatDensity (ρ : AbsoluteDensity d) :
    Tendsto (fun t : ℝ => ∫ x, |(heatDensity ρ t).density x - ρ.density x| ∂haar d) (𝓝[>] 0)
      (𝓝 0) := by
  refine (tendsto_integral_abs_heatOp_sub ρ.memLp_sqrt).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have := heatDensity_density (ρ := ρ) ht x
  simp only [AbsoluteDensity.density] at this ⊢
  rw [this]
  rfl
theorem tendsto_L1_barycenter_heatFamily (F : SpeciesFamily d) :
    Tendsto (fun t : ℝ => ∫ x, |(barycenter (heatFamily F t)).density x -
      (barycenter F).density x| ∂haar d) (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ => ∑ s, F.weight s * ∫ x, |(heatDensity (F.density s) t).density x -
      (F.density s).density x| ∂haar d) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin F.count)) fun s _ =>
      (tendsto_L1_heatDensity (F.density s)).const_mul (F.weight s)
    simpa using this
  refine squeeze_zero (fun t => integral_nonneg fun x => abs_nonneg _) (fun t => ?_) hs
  have hi : ∀ s, Integrable (fun x => |(heatDensity (F.density s) t).density x -
      (F.density s).density x|) (haar d) := fun s =>
    ((heatDensity (F.density s) t).integrable_density.sub (F.density s).integrable_density).abs
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun s _ => (hi s).const_mul _]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
    (integrable_finsetSum _ fun s _ => (hi s).const_mul _) (Eventually.of_forall fun x => ?_)
  have e1 : (barycenter (heatFamily F t)).density x =
      ∑ s, F.weight s * (heatDensity (F.density s) t).density x :=
    (heatFamily F t).barycenter_density_apply x
  have e2 : (barycenter F).density x = ∑ s, F.weight s * (F.density s).density x :=
    F.barycenter_density_apply x
  beta_reduce
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (F.weight_nonneg s)]

/-! ### Entropy contraction and convergence -/

theorem integral_heatKernelT_sub {t : ℝ} (ht : 0 < t) (x : Torus d) :
    ∫ w, heatKernelT t (x - w) ∂haar d = 1 := by
  rw [integral_sub_left_eq_self (fun z => heatKernelT t z) (haar d) x]
  exact integral_heatKernelT ht

theorem tangent_mul_log {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    a * Real.log a + (Real.log a + 1) * (s - a) ≤ s * Real.log s := by
  rcases hs.eq_or_lt with h0 | h0
  · subst h0
    simp only [zero_sub, zero_mul, Real.log_zero]
    nlinarith
  · have h := entropyIntegrand_nonneg ha hs
    rw [entropyIntegrand, Real.log_div h0.ne' ha.ne'] at h
    nlinarith

theorem heat_mul_log_le {t : ℝ} (ht : 0 < t) (ρ : AbsoluteDensity d) (x : Torus d) :
    heatOp t ρ.density x * Real.log (heatOp t ρ.density x) ≤
      heatOp t (fun w => ρ.density w * Real.log (ρ.density w)) x := by
  have hK := continuous_heatKernelT (d := d) ht
  have hρ := ρ.integrable_density
  have hl := ρ.integrable_density_mul_log
  set a := heatOp t ρ.density x with ha_def
  have ha : 0 < a := heatOp_pos ht hρ (Eventually.of_forall ρ.density_nonneg) ρ.integral_density x
  have hk1 : Integrable (fun w => heatKernelT t (x - w)) (haar d) :=
    integrable_of_continuous_torus (hK.comp (continuous_const.sub continuous_id))
  have i1 := integrable_conv_integrand hK hρ x
  have i2 := integrable_conv_integrand hK hl x
  have hmono : ∫ w, heatKernelT t (x - w) * (a * Real.log a + (Real.log a + 1) * (ρ.density w - a))
      ∂haar d ≤ ∫ w, heatKernelT t (x - w) * (ρ.density w * Real.log (ρ.density w)) ∂haar d := by
    refine integral_mono ?_ i2 fun w => ?_
    · have := (hk1.const_mul (a * Real.log a - (Real.log a + 1) * a)).add
        (i1.const_mul (Real.log a + 1))
      refine this.congr (Eventually.of_forall fun w => ?_)
      simp only [Pi.add_apply]
      ring
    · exact mul_le_mul_of_nonneg_left (tangent_mul_log ha (ρ.density_nonneg w))
        (heatKernelT_pos ht _).le
  have heq : ∫ w, heatKernelT t (x - w) * (a * Real.log a + (Real.log a + 1) * (ρ.density w - a))
      ∂haar d = a * Real.log a := by
    have e : ∀ w, heatKernelT t (x - w) * (a * Real.log a + (Real.log a + 1) * (ρ.density w - a)) =
        (a * Real.log a - (Real.log a + 1) * a) * heatKernelT t (x - w) +
          (Real.log a + 1) * (heatKernelT t (x - w) * ρ.density w) := fun w => by ring
    simp_rw [e]
    rw [integral_add (hk1.const_mul _) (i1.const_mul _), integral_const_mul, integral_const_mul,
      integral_heatKernelT_sub ht x]
    have : ∫ w, heatKernelT t (x - w) * ρ.density w ∂haar d = a := rfl
    rw [this]
    ring
  rw [heq] at hmono
  exact hmono

theorem entropy_toReal_heat_le {t : ℝ} (ht : 0 < t) (ρ : AbsoluteDensity d) :
    (relativeEntropy (densityMeasure (heatDensity ρ t) : Measure (Torus d)) (haar d)).toReal ≤
      (relativeEntropy (densityMeasure ρ : Measure (Torus d)) (haar d)).toReal := by
  rw [(absoluteDensity_entropy_finite (heatDensity ρ t)).2.2.2,
    (absoluteDensity_entropy_finite ρ).2.2.2]
  have hl := ρ.integrable_density_mul_log
  have hh := memLp_heatOp (d := d) ht (p := 1) le_rfl (by simp) (memLp_one_iff_integrable.2 hl)
  calc ∫ x, (heatDensity ρ t).density x * Real.log ((heatDensity ρ t).density x) ∂haar d
      ≤ ∫ x, heatOp t (fun w => ρ.density w * Real.log (ρ.density w)) x ∂haar d := by
        refine integral_mono (absoluteDensity_entropy_finite (heatDensity ρ t)).1
          (memLp_one_iff_integrable.1 hh) fun x => ?_
        rw [heatDensity_density ht]
        exact heat_mul_log_le ht ρ x
    _ = ∫ x, ρ.density x * Real.log (ρ.density x) ∂haar d := integral_heatOp ht hl

theorem tendsto_toReal_relativeEntropy {ι : Type*} {l : Filter ι}
    (ν : ι → ProbabilityMeasure (Torus d)) (ν0 : ProbabilityMeasure (Torus d))
    (hν : Tendsto ν l (𝓝 ν0))
    (hfin : ∀ i, relativeEntropy (ν i : Measure (Torus d)) (haar d) ≠ ⊤)
    (hfin0 : relativeEntropy (ν0 : Measure (Torus d)) (haar d) ≠ ⊤)
    (hle : ∀ᶠ i in l, (relativeEntropy (ν i : Measure (Torus d)) (haar d)).toReal ≤
      (relativeEntropy (ν0 : Measure (Torus d)) (haar d)).toReal) :
    Tendsto (fun i => (relativeEntropy (ν i : Measure (Torus d)) (haar d)).toReal) l
      (𝓝 (relativeEntropy (ν0 : Measure (Torus d)) (haar d)).toReal) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hlsc := SharpLSI.lowerSemicontinuous_klDiv (haar d) ν0 (a : EReal) (by
      change (a : EReal) < ((InformationTheory.klDiv (ν0 : Measure (Torus d)) (haar d) : ℝ≥0∞) : EReal)
      rw [← Analysis.relativeEntropy_eq_klDiv, ← EReal.coe_ennreal_toReal hfin0]
      exact EReal.coe_lt_coe_iff.2 ha)
    filter_upwards [hν.eventually hlsc] with i hi
    change (a : EReal) < ((InformationTheory.klDiv (ν i : Measure (Torus d)) (haar d) : ℝ≥0∞) : EReal) at hi
    rw [← Analysis.relativeEntropy_eq_klDiv, ← EReal.coe_ennreal_toReal (hfin i)] at hi
    exact EReal.coe_lt_coe_iff.1 hi
  · filter_upwards [hle] with i hi using lt_of_le_of_lt hi ha

theorem tendsto_entropy_heatDensity (ρ : AbsoluteDensity d) :
    Tendsto (fun t : ℝ => (relativeEntropy (densityMeasure (heatDensity ρ t) : Measure (Torus d))
      (haar d)).toReal) (𝓝[>] 0)
      (𝓝 (relativeEntropy (densityMeasure ρ : Measure (Torus d)) (haar d)).toReal) := by
  refine tendsto_toReal_relativeEntropy _ _ (tendsto_densityMeasure_of_L1 _ ρ
    (tendsto_L1_heatDensity ρ)) (fun t => (absoluteDensity_entropy_finite _).2.2.1)
    (absoluteDensity_entropy_finite ρ).2.2.1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht using entropy_toReal_heat_le ht ρ

/-! ### Weak convergence, energies and the species gap -/

theorem tendsto_densityMeasure_heatDensity (ρ : AbsoluteDensity d) :
    Tendsto (fun t : ℝ => densityMeasure (heatDensity ρ t)) (𝓝[>] 0) (𝓝 (densityMeasure ρ)) :=
  tendsto_densityMeasure_of_L1 _ ρ (tendsto_L1_heatDensity ρ)

theorem tendsto_densityMeasure_barycenter_heatFamily (F : SpeciesFamily d) :
    Tendsto (fun t : ℝ => densityMeasure (barycenter (heatFamily F t))) (𝓝[>] 0)
      (𝓝 (densityMeasure (barycenter F))) :=
  tendsto_densityMeasure_of_L1 _ _ (tendsto_L1_barycenter_heatFamily F)

theorem tendsto_energy_heatDensity (ρ : AbsoluteDensity d) (U : BoundedContinuousFunction (Torus d) ℝ) :
    Tendsto (fun t : ℝ => ∫ x, U x ∂(densityMeasure (heatDensity ρ t) : Measure (Torus d)))
      (𝓝[>] 0) (𝓝 (∫ x, U x ∂(densityMeasure ρ : Measure (Torus d)))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (tendsto_densityMeasure_heatDensity ρ) U

theorem tendsto_energy_barycenter_heatFamily (F : SpeciesFamily d)
    (U : BoundedContinuousFunction (Torus d) ℝ) :
    Tendsto (fun t : ℝ => ∫ x, U x ∂(densityMeasure (barycenter (heatFamily F t)) :
      Measure (Torus d))) (𝓝[>] 0)
      (𝓝 (∫ x, U x ∂(densityMeasure (barycenter F) : Measure (Torus d)))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (tendsto_densityMeasure_barycenter_heatFamily F) U

theorem tendsto_speciesGap_heatFamily (A : InteractionData d) (F : SpeciesFamily d) :
    Tendsto (fun t : ℝ => speciesGap A (heatFamily F t)) (𝓝[>] 0) (𝓝 (speciesGap A F)) := by
  rw [← NNReal.tendsto_coe]
  simp only [coe_speciesGap, speciesRawGap]
  have hsum : Tendsto (fun t : ℝ => ∑ s : Fin F.count, F.weight s *
      (relativeEntropy (densityMeasure (heatDensity (F.density s) t) : Measure (Torus d))
        (haar d)).toReal) (𝓝[>] 0)
      (𝓝 (∑ s : Fin F.count, F.weight s *
        (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d)) (haar d)).toReal)) :=
    tendsto_finsetSum _ fun s _ => (tendsto_entropy_heatDensity (F.density s)).const_mul _
  have hb := tendsto_densityMeasure_barycenter_heatFamily F
  have hp := ((continuous_potentialEnergy A).tendsto _).comp hb
  have hi := ((continuous_interactionEnergy A).tendsto _).comp hb
  exact ((hsum.add hp).add (hi.const_mul _)).sub tendsto_const_nhds

/-! ### Strong convergence of square roots and their gradients -/

theorem tendsto_eLpNorm_two_of_integral {E : Type*} [NormedAddCommGroup E] {ι : Type*}
    {l : Filter ι} {h : ι → Torus d → E} (hm : ∀ᶠ i in l, MemLp (h i) 2 (haar d))
    (hi : Tendsto (fun i => ∫ x, ‖h i x‖ ^ 2 ∂haar d) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (h i) 2 (haar d)) l (𝓝 0) := by
  have key : ∀ᶠ i in l, eLpNorm (h i) 2 (haar d) =
      ENNReal.ofReal ((∫ x, ‖h i x‖ ^ 2 ∂haar d) ^ (1 / 2 : ℝ)) := by
    filter_upwards [hm] with i hi
    rw [hi.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]
  refine Tendsto.congr' (key.mono fun i hi => hi.symm) ?_
  have := ENNReal.tendsto_ofReal (hi.rpow_const (p := (1 / 2 : ℝ)) (Or.inr (by norm_num)))
  simpa using this

theorem tendsto_eLpNorm_one_of_integral {ι : Type*} {l : Filter ι} {h : ι → Torus d → ℝ}
    (hm : ∀ i, Integrable (h i) (haar d))
    (hi : Tendsto (fun i => ∫ x, |h i x| ∂haar d) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (h i) 1 (haar d)) l (𝓝 0) := by
  have key : ∀ i, eLpNorm (h i) 1 (haar d) = ENNReal.ofReal (∫ x, |h i x| ∂haar d) := fun i => by
    rw [eLpNorm_one_eq_lintegral_enorm (hm i).aestronglyMeasurable, ← ofReal_integral_norm_eq_lintegral_enorm (hm i)]
    simp only [Real.norm_eq_abs]
  simp_rw [key]
  simpa using ENNReal.tendsto_ofReal hi

theorem tendsto_eLpNorm_sqrt_gradient_heat (ρ : AbsoluteDensity d) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => (heatDensity ρ t).sqrt x - ρ.sqrt x) 2 (haar d))
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun t : ℝ => eLpNorm (fun x => weakGradient (heatDensity ρ t).sqrt
      (heatDensity ρ t).sqrt_mem x - weakGradient ρ.sqrt ρ.sqrt_mem x) 2 (haar d))
      (𝓝[>] 0) (𝓝 0) := by
  have hu := isWeakGradient_weakGradient ρ.sqrt_mem
  have hH : Tendsto (fun t : ℝ => ∫ x, (√(heatOp t ρ.density x) - ρ.sqrt x) ^ 2 ∂haar d +
      ∫ x, ‖smoothGrad (fun y => √(heatOp t ρ.density y)) x -
        weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar d) (𝓝[>] 0) (𝓝 0) :=
    tendsto_H1_sqrt_heatOp hu ρ.sqrt_nonneg ρ.mass_one
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  constructor
  · have h1 : Tendsto (fun t : ℝ => ∫ x, (√(heatOp t ρ.density x) - ρ.sqrt x) ^ 2 ∂haar d)
        (𝓝[>] 0) (𝓝 0) :=
      squeeze_zero (fun t => integral_nonneg fun x => sq_nonneg _) (fun t =>
        le_add_of_nonneg_right (integral_nonneg fun x => sq_nonneg _)) hH
    refine tendsto_eLpNorm_two_of_integral (h := fun t x => (heatDensity ρ t).sqrt x - ρ.sqrt x)
      (hpos.mono fun t ht => (heatDensity ρ t).memLp_sqrt.sub ρ.memLp_sqrt) ?_
    refine Tendsto.congr' (hpos.mono fun t ht => ?_) h1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, sq_abs, heatDensity_sqrt ht]
  · have h2 : Tendsto (fun t : ℝ => ∫ x, ‖smoothGrad (fun y => √(heatOp t ρ.density y)) x -
        weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar d) (𝓝[>] 0) (𝓝 0) :=
      squeeze_zero (fun t => integral_nonneg fun x => sq_nonneg _) (fun t =>
        le_add_of_nonneg_left (integral_nonneg fun x => sq_nonneg _)) hH
    have h3 := tendsto_eLpNorm_two_of_integral (l := 𝓝[>] (0 : ℝ))
      (h := fun t x => smoothGrad (fun y => √(heatOp t ρ.density y)) x -
        weakGradient ρ.sqrt ρ.sqrt_mem x)
      (hpos.mono fun t ht => ?_) h2
    · refine Tendsto.congr' (hpos.mono fun t ht => ?_) h3
      exact eLpNorm_congr_ae ((weakGradient_heatDensity ht).symm.sub Filter.EventuallyEq.rfl)
    · have hv := isSmoothPeriodic_sqrt_heatOp ht ρ.memLp_sqrt ρ.mass_one
      exact hv.isWeakGradient.memLp_grad.sub hu.memLp_grad

theorem tendsto_eLpNorm_of_tendsto_sub {ι : Type*} {l : Filter ι} {E : Type*}
    [NormedAddCommGroup E] {w : ι → Torus d → E} {w0 : Torus d → E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (h : Tendsto (fun i => eLpNorm (fun x => w i x - w0 x) p (haar d)) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (w i) p (haar d)) l (𝓝 (eLpNorm w0 p (haar d))) := by
  have up : ∀ i, eLpNorm (w i) p (haar d) ≤
      eLpNorm w0 p (haar d) + eLpNorm (fun x => w i x - w0 x) p (haar d) := fun i => by
    have e : w i = w0 + (fun x => w i x - w0 x) := by funext x; simp
    calc eLpNorm (w i) p (haar d) = eLpNorm (w0 + (fun x => w i x - w0 x)) p (haar d) := by
          rw [← e]
      _ ≤ _ := eLpNorm_add_le hp
  have lo : ∀ i, eLpNorm w0 p (haar d) - eLpNorm (fun x => w i x - w0 x) p (haar d) ≤
      eLpNorm (w i) p (haar d) := fun i => by
    rw [tsub_le_iff_right]
    have e : w0 = w i + -(fun x => w i x - w0 x) := by funext x; simp
    calc eLpNorm w0 p (haar d) = eLpNorm (w i + -(fun x => w i x - w0 x)) p (haar d) := by
          rw [← e]
      _ ≤ _ := (eLpNorm_add_le hp).trans (le_of_eq (by rw [eLpNorm_neg]))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_ lo up
  · have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := eLpNorm w0 p (haar d))) h
      (Or.inr ENNReal.zero_ne_top)
    simpa using this
  · have := (tendsto_const_nhds (x := eLpNorm w0 p (haar d))).add h
    simpa using this

/-! ### The drift of a species family and its stability -/

theorem force_ae_eq_lipschitz (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (ρ : AbsoluteDensity d) :
    b.force ρ =ᵐ[haar d] fun x => smoothGrad A.V x +
      ∫ y, ρ.density y • interactionGradient A x y ∂haar d := by
  have h := absoluteDrift_unique b (lipschitz_absoluteDrift A hLip) ρ
  refine h.trans (Eventually.of_forall fun x => ?_)
  show smoothGrad A.V x + ∫ y, densityRep ρ y • interactionGradient A x y ∂haar d = _
  rw [interactionForce_eq]

theorem memLp_top_force (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (ρ : AbsoluteDensity d) : MemLp (b.force ρ) ∞ (haar d) := by
  obtain ⟨L, hL0, hW, hmeas, hbd, hB, hWB, key⟩ := weakGradient_convolution A hLip
  obtain ⟨LV, hLV0, hV⟩ := hLip.exists_V_const
  have hVg := Lipschitz.exists_weak_gradient hLV0 hV
  have hc := (key.1 ρ.density (Lipschitz.isProbDensity_density ρ)).1
  have hs := isWeakGradientLp_add hVg.1 hc
  exact MemLp.ae_eq (force_ae_eq_lipschitz A hLip b ρ).symm hs.memLp_grad

theorem eLpNorm_force_sub_le (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (ρ η : AbsoluteDensity d) :
    eLpNorm (fun x => b.force ρ x - b.force η x) ∞ (haar d) ≤
      eLpNorm (fun p : Torus d × Torus d => interactionGradient A p.1 p.2) ∞
        ((haar d).prod (haar d)) *
        eLpNorm (fun y => ρ.density y - η.density y) 1 (haar d) := by
  obtain ⟨L, hL0, hW, hmeas, hbd, hB, hWB, key⟩ := weakGradient_convolution A hLip
  have hx := Measure.ae_ae_of_ae_prod hbd
  have hρ := force_ae_eq_lipschitz A hLip b ρ
  have hη := force_ae_eq_lipschitz A hLip b η
  refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (key.2.1 ρ.density η.density
    (Lipschitz.isProbDensity_density ρ) (Lipschitz.isProbDensity_density η))
  filter_upwards [hρ, hη, hx] with x h1 h2 h3
  have hint : ∀ σ : AbsoluteDensity d,
      Integrable (fun y => σ.density y • interactionGradient A x y) (haar d) := fun σ => by
    refine (σ.integrable_density.norm.const_mul L).mono' ?_ ?_
    · exact σ.integrable_density.aestronglyMeasurable.smul
        ((hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    · filter_upwards [h3] with y hy
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
  show b.force ρ x - b.force η x =
    ∫ y, (ρ.density y - η.density y) • interactionGradient A x y ∂haar d
  rw [h1, h2, add_sub_add_left_eq_sub]
  simp only [sub_smul]
  rw [integral_sub (hint ρ) (hint η)]

/-- The weighted drift-score vector `2 ∇u_s + u_s b(ρ̄)` of species `s`. -/
noncomputable def driftScore (A : InteractionData d) (b : AbsoluteDrift A) (F : SpeciesFamily d)
    (s : Fin F.count) (x : Torus d) : Tangent d :=
  (2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • b.force (barycenter F) x

theorem tendsto_eLpNorm_driftScore_sub (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (F : SpeciesFamily d) (s : Fin F.count) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => driftScore A b (heatFamily F t) s x -
      driftScore A b F s x) 2 (haar d)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hv, hg⟩ := tendsto_eLpNorm_sqrt_gradient_heat (F.density s)
  obtain ⟨L, hL0, hW, hmeas, hbd, hB, hWB, key⟩ := weakGradient_convolution A hLip
  have hf : eLpNorm (b.force (barycenter F)) ∞ (haar d) ≠ ⊤ :=
    (memLp_top_force A hLip b _).eLpNorm_ne_top
  have hBn := hB.eLpNorm_ne_top
  have hu2 : eLpNorm (F.density s).sqrt 2 (haar d) ≠ ⊤ := (F.density s).memLp_sqrt.eLpNorm_ne_top
  have hc := tendsto_eLpNorm_one_of_integral
    (h := fun t x => (barycenter (heatFamily F t)).density x - (barycenter F).density x)
    (fun t => (barycenter (heatFamily F t)).integrable_density.sub
      (barycenter F).integrable_density) (tendsto_L1_barycenter_heatFamily F)
  set Bn := eLpNorm (fun p : Torus d × Torus d => interactionGradient A p.1 p.2) ∞
    ((haar d).prod (haar d)) with hBn_def
  set u := (F.density s).sqrt with hu_def
  set f := b.force (barycenter F) with hf_def
  set a : ℝ → ℝ≥0∞ := fun t => eLpNorm (fun x => (heatFamily F t).sqrtGradient s x -
    F.sqrtGradient s x) 2 (haar d) with ha_def
  set bb : ℝ → ℝ≥0∞ := fun t => eLpNorm (fun x => ((heatFamily F t).density s).sqrt x - u x) 2
    (haar d) with hbb_def
  set c : ℝ → ℝ≥0∞ := fun t => eLpNorm (fun x => (barycenter (heatFamily F t)).density x -
    (barycenter F).density x) 1 (haar d) with hc_def
  have ha : Tendsto a (𝓝[>] 0) (𝓝 0) := hg
  have hbb : Tendsto bb (𝓝[>] 0) (𝓝 0) := hv
  have hc' : Tendsto c (𝓝[>] 0) (𝓝 0) := hc
  have T : Tendsto (fun t : ℝ => ‖(2 : ℝ)‖ₑ * a t + bb t * eLpNorm f ∞ (haar d) +
      (eLpNorm u 2 (haar d) + bb t) * (Bn * c t)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t => ‖(2 : ℝ)‖ₑ * a t) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul ha (Or.inr (by simp))
    have h2 : Tendsto (fun t => bb t * eLpNorm f ∞ (haar d)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hbb (Or.inr hf)
    have h3 : Tendsto (fun t => Bn * c t) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hc' (Or.inr hBn)
    have h4 : Tendsto (fun t => eLpNorm u 2 (haar d) + bb t) (𝓝[>] 0)
        (𝓝 (eLpNorm u 2 (haar d))) := by
      simpa using (tendsto_const_nhds (x := eLpNorm u 2 (haar d))).add hbb
    have h5 := ENNReal.Tendsto.mul h4 (Or.inr ENNReal.zero_ne_top) h3 (Or.inr hu2)
    simpa using (h1.add h2).add h5
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds T (fun t => bot_le)
    (fun t => ?_)
  have hdec : (fun x => driftScore A b (heatFamily F t) s x - driftScore A b F s x) =
      (fun x => (2 : ℝ) • ((heatFamily F t).sqrtGradient s x - F.sqrtGradient s x)) +
      (fun x => (((heatFamily F t).density s).sqrt x - u x) • f x) +
      (fun x => ((heatFamily F t).density s).sqrt x •
        (b.force (barycenter (heatFamily F t)) x - f x)) := by
    funext x
    simp only [driftScore, Pi.add_apply, hu_def, hf_def]
    module
  rw [hdec]
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have e1 : eLpNorm (fun x => (2 : ℝ) • ((heatFamily F t).sqrtGradient s x -
      F.sqrtGradient s x)) 2 (haar d) = ‖(2 : ℝ)‖ₑ * a t :=
    eLpNorm_const_smul (2 : ℝ) (fun x => (heatFamily F t).sqrtGradient s x -
      F.sqrtGradient s x) 2 (haar d)
  have e2 : eLpNorm (fun x => (((heatFamily F t).density s).sqrt x - u x) • f x) 2 (haar d) ≤
      bb t * eLpNorm f ∞ (haar d) :=
    eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top_of_pos (φ := fun x =>
      ((heatFamily F t).density s).sqrt x - u x) (f := f) 2 (by norm_num)
  have hv_t : eLpNorm (fun x => ((heatFamily F t).density s).sqrt x) 2 (haar d) ≤
      eLpNorm u 2 (haar d) + bb t := by
    have e : (fun x => ((heatFamily F t).density s).sqrt x) =
        u + (fun x => ((heatFamily F t).density s).sqrt x - u x) := by funext x; simp
    rw [e]; exact eLpNorm_add_le hp
  have e3 : eLpNorm (fun x => ((heatFamily F t).density s).sqrt x •
      (b.force (barycenter (heatFamily F t)) x - f x)) 2 (haar d) ≤
      (eLpNorm u 2 (haar d) + bb t) * (Bn * c t) :=
    (eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top_of_pos (φ := fun x =>
      ((heatFamily F t).density s).sqrt x) (f := fun x =>
      b.force (barycenter (heatFamily F t)) x - f x) 2 (by norm_num)).trans
      (mul_le_mul' hv_t (eLpNorm_force_sub_le A hLip b _ _))
  have h12 := (eLpNorm_add_le (p := 2) (μ := haar d) (f := fun x => (2 : ℝ) • ((heatFamily F t).sqrtGradient s x -
      F.sqrtGradient s x)) (g := fun x => (((heatFamily F t).density s).sqrt x - u x) • f x) hp)
  refine (eLpNorm_add_le (p := 2) (μ := haar d) hp).trans ?_
  rw [e1] at h12
  have := add_le_add (h12.trans (add_le_add le_rfl e2)) e3
  exact this

theorem lintegral_ofReal_norm_sq_eq {w : Torus d → Tangent d}
    (hw : AEStronglyMeasurable w (haar d)) :
    ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ∂haar d = eLpNorm w 2 (haar d) ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hw]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [Nat.cast_ofNat]
  rw [inv_mul_cancel₀ (by norm_num), ENNReal.rpow_one]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two]

theorem speciesDissipation_eq_eLpNorm (A : InteractionData d) (b : AbsoluteDrift A)
    (F : SpeciesFamily d) :
    speciesDissipation A b F =
      ∑ s, ENNReal.ofReal (F.weight s) * eLpNorm (driftScore A b F s) 2 (haar d) ^ 2 := by
  unfold speciesDissipation
  refine Finset.sum_congr rfl fun s _ => ?_
  have hm : AEStronglyMeasurable (driftScore A b F s) (haar d) :=
    (((F.isWeakGradient_sqrtGradient s).memLp_grad.aestronglyMeasurable.const_smul (2 : ℝ)).add
      ((F.density s).memLp_sqrt.aestronglyMeasurable.smul
        (b.measurable_force _).aestronglyMeasurable))
  rw [← lintegral_ofReal_norm_sq_eq hm]
  rfl

theorem tendsto_eLpNorm_driftScore (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (F : SpeciesFamily d) (s : Fin F.count) :
    Tendsto (fun t : ℝ => eLpNorm (driftScore A b (heatFamily F t) s) 2 (haar d)) (𝓝[>] 0)
      (𝓝 (eLpNorm (driftScore A b F s) 2 (haar d))) :=
  tendsto_eLpNorm_of_tendsto_sub (by norm_num) (tendsto_eLpNorm_driftScore_sub A hLip b F s)

theorem tendsto_speciesDissipation_heatFamily (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (F : SpeciesFamily d) :
    Tendsto (fun t : ℝ => speciesDissipation A b (heatFamily F t)) (𝓝[>] 0)
      (𝓝 (speciesDissipation A b F)) := by
  have key : ∀ t : ℝ, speciesDissipation A b (heatFamily F t) =
      ∑ s : Fin F.count, ENNReal.ofReal (F.weight s) *
        eLpNorm (driftScore A b (heatFamily F t) s) 2 (haar d) ^ 2 := fun t =>
    speciesDissipation_eq_eLpNorm A b (heatFamily F t)
  rw [speciesDissipation_eq_eLpNorm A b F]
  refine Tendsto.congr (fun t => (key t).symm) ?_
  refine tendsto_finsetSum (Finset.univ : Finset (Fin F.count)) fun s _ => ?_
  exact ENNReal.Tendsto.const_mul
    (((ENNReal.continuous_pow 2).tendsto _).comp (tendsto_eLpNorm_driftScore A hLip b F s))
    (Or.inr ENNReal.ofReal_ne_top)

/-- **Joint entropy, energy and score convergence under heat recovery (LIP020).**
For a fixed finite species family `F` (with the heat time applied to every species density):
every species has finite entropy; the entropy contracts and converges,
`H(H_t ρ_s | m) → H(ρ_s | m)`; species and barycenter measures converge weakly, hence energies of
bounded continuous potentials converge; the potential and interaction energies of the barycenter,
and hence `G_θ`, converge; the drift-score vectors `2 ∇u_s + u_s b(ρ̄)` converge strongly in
`L²`; and so does the dissipation `D_θ`.  All limits are as `t → 0⁺`. -/
theorem joint_entropy_energy_and_score_convergence_under_heat_recovery
    (A : InteractionData d) (hLip : LipschitzData A) (b : AbsoluteDrift A)
    (F : SpeciesFamily d) :
    (∀ s : Fin F.count,
      relativeEntropy (densityMeasure (F.density s) : Measure (Torus d)) (haar d) ≠ ⊤ ∧
        Integrable (fun x => (F.density s).density x * Real.log ((F.density s).density x))
          (haar d)) ∧
    (∀ (s : Fin F.count) (t : ℝ), 0 < t →
      (relativeEntropy (densityMeasure (heatDensity (F.density s) t) : Measure (Torus d))
        (haar d)).toReal ≤
      (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d)) (haar d)).toReal) ∧
    (∀ s : Fin F.count, Tendsto (fun t : ℝ =>
      (relativeEntropy (densityMeasure (heatDensity (F.density s) t) : Measure (Torus d))
        (haar d)).toReal) (𝓝[>] 0)
      (𝓝 (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d)) (haar d)).toReal)) ∧
    (∀ s : Fin F.count, Tendsto (fun t : ℝ => densityMeasure (heatDensity (F.density s) t))
      (𝓝[>] 0) (𝓝 (densityMeasure (F.density s)))) ∧
    Tendsto (fun t : ℝ => densityMeasure (barycenter (heatFamily F t))) (𝓝[>] 0)
      (𝓝 (densityMeasure (barycenter F))) ∧
    (∀ U : BoundedContinuousFunction (Torus d) ℝ,
      (∀ s : Fin F.count, Tendsto (fun t : ℝ =>
        ∫ x, U x ∂(densityMeasure (heatDensity (F.density s) t) : Measure (Torus d)))
        (𝓝[>] 0) (𝓝 (∫ x, U x ∂(densityMeasure (F.density s) : Measure (Torus d))))) ∧
      Tendsto (fun t : ℝ => ∫ x, U x ∂(densityMeasure (barycenter (heatFamily F t)) :
        Measure (Torus d))) (𝓝[>] 0)
        (𝓝 (∫ x, U x ∂(densityMeasure (barycenter F) : Measure (Torus d))))) ∧
    Tendsto (fun t : ℝ => potentialEnergy A (densityMeasure (barycenter (heatFamily F t))))
      (𝓝[>] 0) (𝓝 (potentialEnergy A (densityMeasure (barycenter F)))) ∧
    Tendsto (fun t : ℝ => interactionEnergy A (densityMeasure (barycenter (heatFamily F t))))
      (𝓝[>] 0) (𝓝 (interactionEnergy A (densityMeasure (barycenter F)))) ∧
    Tendsto (fun t : ℝ => speciesGap A (heatFamily F t)) (𝓝[>] 0) (𝓝 (speciesGap A F)) ∧
    (∀ s : Fin F.count, Tendsto (fun t : ℝ => eLpNorm (fun x =>
      driftScore A b (heatFamily F t) s x - driftScore A b F s x) 2 (haar d)) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ s : Fin F.count, Tendsto (fun t : ℝ => eLpNorm (driftScore A b (heatFamily F t) s) 2
      (haar d)) (𝓝[>] 0) (𝓝 (eLpNorm (driftScore A b F s) 2 (haar d)))) ∧
    Tendsto (fun t : ℝ => speciesDissipation A b (heatFamily F t)) (𝓝[>] 0)
      (𝓝 (speciesDissipation A b F)) := by
  have hb := tendsto_densityMeasure_barycenter_heatFamily F
  refine ⟨fun s => ⟨(absoluteDensity_entropy_finite (F.density s)).2.2.1,
      (absoluteDensity_entropy_finite (F.density s)).1⟩,
    fun s t ht => entropy_toReal_heat_le ht (F.density s),
    fun s => tendsto_entropy_heatDensity (F.density s),
    fun s => tendsto_densityMeasure_heatDensity (F.density s), hb,
    fun U => ⟨fun s => tendsto_energy_heatDensity (F.density s) U,
      tendsto_energy_barycenter_heatFamily F U⟩,
    ((continuous_potentialEnergy A).tendsto _).comp hb,
    ((continuous_interactionEnergy A).tendsto _).comp hb,
    tendsto_speciesGap_heatFamily A F,
    fun s => tendsto_eLpNorm_driftScore_sub A hLip b F s,
    fun s => tendsto_eLpNorm_driftScore A hLip b F s,
    tendsto_speciesDissipation_heatFamily A hLip b F⟩

end DGPS.Lipschitz
