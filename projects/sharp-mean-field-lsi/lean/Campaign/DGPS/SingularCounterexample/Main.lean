import DGPS.SingularCounterexample.Baselines.Cosine
import DGPS.SingularCounterexample.Baselines.Green
import DGPS.SingularCounterexample.BarrierNorms
import DGPS.SingularCounterexample.BarrierGeometry
import DGPS.SingularCounterexample.Particle.WellPosed
import DGPS.SingularCounterexample.Particle.ZeroRates
import DGPS.SingularCounterexample.MeanField.BinaryRecovery

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace DGPS.SingularCounterexample

/-- A bounded baseline kernel belongs to circle `L²`. -/
theorem baseline_memLp (B : BaselineKernel) : MemLp B.g 2 (haar 1) := by
  rcases B.bounded_g with ⟨C, hC, hbound⟩
  refine MemLp.of_bound B.measurable_g.aestronglyMeasurable C ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact hbound x

/-- The baseline plus the singular barrier remains in circle `L²`. -/
theorem perturbedKernel_memLp (B : BaselineKernel) (β η : ℝ) :
    MemLp (perturbedKernel B β η) 2 (haar 1) := by
  have hbase : MemLp B.g 2 (haar 1) := baseline_memLp B
  have hbar : MemLp barrier 2 (haar 1) := barrier_memLp (by norm_num) (by norm_num)
  have hηbar : MemLp (fun x => η * barrier x) 2 (haar 1) := hbar.const_mul η
  have hsum : MemLp (fun x => B.g x + η * barrier x) 2 (haar 1) := hbase.add hηbar
  have hscale : MemLp (fun x => β * (B.g x + η * barrier x)) 2 (haar 1) :=
    hsum.const_mul β
  change MemLp (fun x => β * (B.g x + η * barrier x)) 2 (haar 1)
  exact hscale

/-- Integrable Fourier coefficients are additive in the real-valued input. -/
theorem coeff1_add_integrable {f g : Circle → ℝ}
    (hf : Integrable f (haar 1)) (hg : Integrable g (haar 1)) (n : ℤ) :
    coeff1 (fun x => f x + g x) n = coeff1 f n + coeff1 g n := by
  rw [coeff1_eq_fourierCoeff, DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral,
    coeff1_eq_fourierCoeff, DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral,
    coeff1_eq_fourierCoeff, DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]
  calc
    _ = ∫ x, ((fun x : Circle => UnitAddTorus.mFourier (-freqZ n) x * (f x : ℂ)) +
        (fun x => UnitAddTorus.mFourier (-freqZ n) x * (g x : ℂ))) x ∂haar 1 := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [Pi.add_apply, Complex.ofReal_add]
          ring
    _ = _ := integral_add
      (by simpa only [smul_eq_mul] using SharpLSI.integrable_mFourier_smul' hf (-freqZ n))
      (by simpa only [smul_eq_mul] using SharpLSI.integrable_mFourier_smul' hg (-freqZ n))

/-- Integrable Fourier coefficients respect real scalar multiplication. -/
theorem coeff1_real_smul_integrable {f : Circle → ℝ}
    (c : ℝ) (n : ℤ) :
    coeff1 (fun x => c * f x) n = (c : ℂ) * coeff1 f n := by
  rw [coeff1_eq_fourierCoeff, DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral,
    coeff1_eq_fourierCoeff, DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]
  calc
    _ = ∫ x, (c : ℂ) * (UnitAddTorus.mFourier (-freqZ n) x * (f x : ℂ)) ∂haar 1 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Complex.ofReal_mul]
      ring
    _ = _ := integral_const_mul _ _

/-- The coefficient decomposition of the singular perturbation. -/
theorem perturbedKernel_coeff1 (B : BaselineKernel) (β η : ℝ) (n : ℤ) :
    coeff1 (perturbedKernel B β η) n =
      (β : ℂ) * (coeff1 B.g n + (η : ℂ) * coeff1 barrier n) := by
  have hbase : Integrable B.g (haar 1) := (baseline_memLp B).integrable (by norm_num)
  have hbar : Integrable barrier (haar 1) :=
    (barrier_memLp (p := 2) (by norm_num) (by norm_num)).integrable (by norm_num)
  have hηbar : Integrable (fun x => η * barrier x) (haar 1) := hbar.const_mul η
  have hadd := coeff1_add_integrable hbase hηbar n
  have hscale := coeff1_real_smul_integrable
    (f := fun x => B.g x + η * barrier x) β n
  change coeff1 (fun x => β * (B.g x + η * barrier x)) n = _
  calc
    _ = (β : ℂ) * coeff1 (fun x => B.g x + η * barrier x) n := hscale
    _ = (β : ℂ) * (coeff1 B.g n + coeff1 (fun x => η * barrier x) n) := by rw [hadd]
    _ = (β : ℂ) * (coeff1 B.g n + (η : ℂ) * coeff1 barrier n) := by
      rw [coeff1_real_smul_integrable (f := barrier) η n]

/-- The barrier's established pointwise and off-collision regularity properties. -/
theorem barrier_elementary_properties :
    (∀ x, 0 ≤ barrier x) ∧ (∀ x, barrier (-x) = barrier x) ∧ barrier 0 = 0 ∧
      Measurable barrier ∧ Tendsto barrier (𝓝[≠] (0 : Circle)) atTop ∧
      ContDiffOn ℝ ∞ (fun t : ℝ => barrier (torusPoint t))
        {t : ℝ | torusPoint t ≠ (0 : Circle)} ∧
      (∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → MemLp barrier p (haar 1)) := by
  refine ⟨barrier_nonneg, barrier_even, barrier_zero, barrier_measurable,
    barrier_tendsto_collision, barrier_smooth_off_collision, ?_⟩
  intro p hp hpfin
  exact barrier_memLp hp hpfin

/-- The complete frozen T0 barrier conclusion: every finite Lp, every Hs below one-half,
and strictly positive real nonzero Fourier coefficients, together with the pointwise and
off-collision properties. -/
theorem barrier_exists_and_properties :
    (∀ x, 0 ≤ barrier x) ∧
    (∀ x, barrier (-x) = barrier x) ∧
    barrier 0 = 0 ∧
    Measurable barrier ∧
    Tendsto barrier (𝓝[≠] (0 : Circle)) atTop ∧
    ContDiffOn ℝ ∞ (fun t : ℝ => barrier (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)} ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → MemLp barrier p (haar 1)) ∧
    (∀ s : ℝ, s < 1 / 2 → MemCircleHs s barrier) ∧
    HasPosNonzeroFourier barrier := by
  exact ⟨barrier_nonneg, barrier_even, barrier_zero, barrier_measurable,
    barrier_tendsto_collision, barrier_smooth_off_collision,
    (fun p hp hpfin => barrier_memLp hp hpfin),
    (fun s hs => barrier_mem_hs hs), barrier_has_pos_nonzero_fourier⟩

/-- The perturbed kernel diverges at collision through nonzero circle points. -/
theorem perturbedKernel_tendsto_collision (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) :
    Tendsto (perturbedKernel B β η) (𝓝[≠] (0 : Circle)) atTop := by
  rcases B.bounded_g with ⟨G, hG, hbound⟩
  refine tendsto_atTop.2 fun b => ?_
  let R : ℝ := (b / β + G) / η + 1
  have hR : b < β * (-G + η * R) := by
    dsimp [R]
    field_simp
    nlinarith [mul_pos hβ hη]
  have hevent := barrier_tendsto_collision.eventually (eventually_ge_atTop R)
  filter_upwards [hevent] with x hx
  have hbase : -G ≤ B.g x := (abs_le.mp (hbound x)).1
  have hinner : -G + η * R ≤ B.g x + η * barrier x :=
    add_le_add hbase (mul_le_mul_of_nonneg_left hx hη.le)
  change b ≤ β * (B.g x + η * barrier x)
  exact le_of_lt (lt_of_lt_of_le hR (mul_le_mul_of_nonneg_left hinner hβ.le))

/-- Basic frozen pair-interaction hypotheses, together with the actual singular divergence. -/
theorem perturbedInteraction_basic_properties (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) :
    Measurable (Function.uncurry (perturbedInteraction B β η)) ∧
      (∃ C : ℝ, ∀ x y, -C ≤ perturbedInteraction B β η x y) ∧
      (∀ x y, perturbedInteraction B β η x y = perturbedInteraction B β η y x) ∧
      (∀ x, perturbedInteraction B β η x x = 0) ∧
      Tendsto (perturbedKernel B β η) (𝓝[≠] (0 : Circle)) atTop := by
  rcases perturbedInteraction_borel_lower_bound B hβ hη with ⟨hm, ⟨C, hC⟩⟩
  exact ⟨hm, ⟨C, hC⟩, perturbedInteraction_even B β η,
    perturbedInteraction_self B β η, perturbedKernel_tendsto_collision B hβ hη⟩

/-- Off-collision smoothness is conditional on the baseline's own off-zero smoothness. -/
theorem perturbedKernel_smooth_off_collision (B : BaselineKernel) (β η : ℝ)
    (hB : ContDiffOn ℝ ∞ (fun t : ℝ => B.g (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)}) :
    ContDiffOn ℝ ∞ (fun t : ℝ => perturbedKernel B β η (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)} := by
  change ContDiffOn ℝ ∞ (fun t => β * (B.g (torusPoint t) +
    η * barrier (torusPoint t))) _
  have hsum : ContDiffOn ℝ ∞
      (fun t => B.g (torusPoint t) + η * barrier (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)} := by
    have hbar := barrier_smooth_off_collision.const_smul η
    simpa only [smul_eq_mul] using hB.add hbar
  have hscale := hsum.const_smul β
  simpa only [smul_eq_mul] using hscale

/-- The lifted pair interaction is smooth away from the diagonal, provided the lifted
baseline is smooth away from zero. This explicitly composes the kernel regularity with the
circle difference map. -/
theorem perturbedInteraction_smooth_off_diagonal (B : BaselineKernel) (β η : ℝ)
    (hB : ContDiffOn ℝ ∞ (fun t : ℝ => B.g (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)}) :
    ContDiffOn ℝ ∞
      (fun p : Fin 2 → ℝ =>
        perturbedInteraction B β η (torusPoint (p 0)) (torusPoint (p 1)))
      {p : Fin 2 → ℝ | torusPoint (p 0) ≠ torusPoint (p 1)} := by
  let q : (Fin 2 → ℝ) → ℝ := fun p => p 0 - p 1
  have hq : ContDiff ℝ ∞ q := by fun_prop
  have hsub (p : Fin 2 → ℝ) :
      torusPoint (p 0 - p 1) = torusPoint (p 0) - torusPoint (p 1) := by
    simpa [torusPoint, DGPS.Examples.PositiveH1.Nonlinear.lift1] using
      DGPS.Examples.PositiveH1.Nonlinear.lift1_sub (p 0) (p 1)
  have hmap : Set.MapsTo q
      {p : Fin 2 → ℝ | torusPoint (p 0) ≠ torusPoint (p 1)}
      {t : ℝ | torusPoint t ≠ (0 : Circle)} := by
    intro p hp
    change torusPoint (p 0 - p 1) ≠ 0
    rw [hsub]
    exact sub_ne_zero.mpr hp
  have hcomp :=
    (perturbedKernel_smooth_off_collision B β η hB).comp hq.contDiffOn hmap
  apply hcomp.congr
  intro p hp
  change perturbedKernel B β η (torusPoint (p 0 - p 1)) =
    perturbedKernel B β η (torusPoint (p 0 - p 1))
  rfl

/-- For each fixed second particle, the pair interaction diverges as the first approaches
the diagonal point through distinct points. -/
theorem perturbedInteraction_tendsto_diagonal (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) (y : Circle) :
    Tendsto (fun x : Circle => perturbedInteraction B β η x y) (𝓝[≠] y) atTop := by
  have hshift : Tendsto (fun x : Circle => x - y) (𝓝[≠] y) (𝓝[≠] (0 : Circle)) := by
    have hcont : Tendsto (fun x : Circle => x - y) (𝓝[≠] y) (𝓝 (0 : Circle)) := by
      have hc : Continuous (fun x : Circle => x - y) := by fun_prop
      simpa using (hc.tendsto y).mono_left nhdsWithin_le_nhds
    have hwithin : ∀ᶠ x in 𝓝[≠] y, (x - y) ∈ ({0}ᶜ : Set Circle) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_ne_zero.mpr hx
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hcont hwithin
  change Tendsto (fun x : Circle => perturbedKernel B β η (x - y)) (𝓝[≠] y) atTop
  exact (perturbedKernel_tendsto_collision B hβ hη).comp hshift

/-- Strict nonzero Fourier positivity of the singular perturbation, with no additional
Fourier hypothesis beyond the `BaselineKernel` fields. -/
theorem perturbedKernel_has_pos_nonzero_fourier (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) :
    HasPosNonzeroFourier (perturbedKernel B β η) := by
  intro n hn
  have hb := B.fourier_nonneg n hn
  have hs := barrier_has_pos_nonzero_fourier n hn
  have hbc : coeff1 B.g n = ((coeff1 B.g n).re : ℂ) := by
    apply Complex.ext <;> simp [hb.1]
  have hsc : coeff1 barrier n = ((coeff1 barrier n).re : ℂ) := by
    apply Complex.ext <;> simp [hs.1]
  rw [perturbedKernel_coeff1, hbc, hsc]
  have hcoeff : (β : ℂ) *
      (((coeff1 B.g n).re : ℂ) + (η : ℂ) * ((coeff1 barrier n).re : ℂ)) =
        ((β * ((coeff1 B.g n).re + η * (coeff1 barrier n).re) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcoeff]
  have hreal : 0 < β * ((coeff1 B.g n).re + η * (coeff1 barrier n).re) :=
    mul_pos hβ (add_pos_of_nonneg_of_pos hb.2 (mul_pos hη hs.2))
  constructor
  · simp
  · exact hreal

/-- The perturbed kernel is admissible, including integrability, a pointwise lower bound,
and nonnegative Fourier coefficients. -/
theorem perturbedKernel_admissible (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) : AdmissibleKernel (perturbedKernel B β η) := by
  rcases B.bounded_g with ⟨G, hG, hbound⟩
  refine ⟨perturbedKernel_measurable B β η,
    (perturbedKernel_memLp B β η).integrable (by norm_num), ?_, ?_, ?_, ?_⟩
  · refine ⟨-(β * G), fun x => ?_⟩
    have hbase : -G ≤ B.g x := (abs_le.mp (hbound x)).1
    have hrep : 0 ≤ η * barrier x := mul_nonneg hη.le (barrier_nonneg x)
    have hsum : -G ≤ B.g x + η * barrier x := by linarith
    calc
      -(β * G) = β * (-G) := by ring
      _ ≤ β * (B.g x + η * barrier x) := mul_le_mul_of_nonneg_left hsum hβ.le
  · intro x
    simp [perturbedKernel, B.even_g, barrier_even]
  · simp [perturbedKernel, B.zero_g, barrier_zero]
  · intro n hn
    exact (perturbedKernel_has_pos_nonzero_fourier B hβ hη n hn).imp_right le_of_lt

/-- Actual mean-field rate conclusions for the perturbed kernel, obtained from the baseline
predicate and positive parameters alone. -/
theorem perturbedKernel_meanfield_rates (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) :
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤ singularScalarPLRate (perturbedKernel B β η) ∧
      singularSpeciesPLRate (perturbedKernel B β η) = ENNReal.ofReal (4 * Real.pi ^ 2) := by
  have hfourier : HasNonnegNonzeroFourier (perturbedKernel B β η) := by
    intro n hn
    have h := perturbedKernel_has_pos_nonzero_fourier B hβ hη n hn
    exact ⟨h.1, h.2.le⟩
  exact ⟨scalar_PL_rate_lower (perturbedKernel B β η)
      (perturbedKernel_memLp B β η) hfourier,
    species_PL_rate_exact (perturbedKernel B β η)
      (perturbedKernel_memLp B β η) hfourier⟩

/-- The generic sharp scalar and species PL rates for a nonnegative-Fourier kernel. -/
theorem singular_meanfield_rates (k : Circle → ℝ)
    (hk : MemLp k 2 (haar 1)) (hfourier : HasNonnegNonzeroFourier k) :
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤ singularScalarPLRate k ∧
      singularSpeciesPLRate k = ENNReal.ofReal (4 * Real.pi ^ 2) := by
  exact ⟨scalar_PL_rate_lower k hk hfourier,
    species_PL_rate_exact k hk hfourier⟩

/-- Simultaneous perturbative smallness in any fixed finite Lp and any fixed Hs below the
half-derivative endpoint, with the complete frozen T3 range s<1/2. -/
theorem barrier_perturbative_smallness {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤)
    {s : ℝ} (hs : s < 1 / 2) :
    Tendsto (fun η : ℝ => eLpNorm (fun x => η * barrier x) p (haar 1))
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun η : ℝ => circleHsNorm s (fun x => η * barrier x))
        (𝓝[>] 0) (𝓝 0) :=
  ⟨barrier_smul_tendsto_Lp hp hpfin, barrier_smul_tendsto_Hs hs⟩

/-- Frozen generic T1 properties for the perturbed kernel and its pair interaction. The
off-collision smoothness clause is conditional, since `BaselineKernel` does not carry a
smoothness field. -/
def SingularCounterexampleProperties (B : BaselineKernel) (β η : ℝ) (N : ℕ) : Prop :=
  let k := perturbedKernel B β η
  let W := perturbedInteraction B β η
  AdmissibleKernel k ∧
  HasPosNonzeroFourier k ∧
  Tendsto k (𝓝[≠] (0 : Circle)) atTop ∧
  Measurable (Function.uncurry W) ∧
  (∃ C : ℝ, ∀ x y, -C ≤ W x y) ∧
  (∀ x y, W x y = W y x) ∧
  (∀ x, W x x = 0) ∧
  (ContDiffOn ℝ ∞ (fun t : ℝ => B.g (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)} →
    ContDiffOn ℝ ∞ (fun t : ℝ => k (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)}) ∧
  (ContDiffOn ℝ ∞ (fun t : ℝ => B.g (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)} →
    ContDiffOn ℝ ∞
      (fun p : Fin 2 → ℝ =>
        W (torusPoint (p 0)) (torusPoint (p 1)))
      {p : Fin 2 → ℝ | torusPoint (p 0) ≠ torusPoint (p 1)}) ∧
  (∀ y : Circle, Tendsto (fun x : Circle => W x y) (𝓝[≠] y) atTop) ∧
  SharpLSI.lamAll (fun _ : Circle => (0 : ℝ)) W N = 0 ∧
  SharpLSI.lamSym (fun _ : Circle => (0 : ℝ)) W N = 0 ∧
  SharpLSI.rAll (fun _ : Circle => (0 : ℝ)) W N = 0 ∧
  SharpLSI.rSym (fun _ : Circle => (0 : ℝ)) W N = 0 ∧
  ENNReal.ofReal (4 * Real.pi ^ 2) ≤ singularScalarPLRate k ∧
  singularSpeciesPLRate k = ENNReal.ofReal (4 * Real.pi ^ 2)

/-- The four frozen finite-particle rates vanish for every fixed `N ≥ 2`. -/
theorem singular_particle_zero_rates {N : ℕ} (hN : 2 ≤ N)
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    SharpLSI.lamAll (fun _ : Circle => (0 : ℝ)) (perturbedInteraction B β η) N = 0 ∧
    SharpLSI.lamSym (fun _ : Circle => (0 : ℝ)) (perturbedInteraction B β η) N = 0 ∧
    SharpLSI.rAll (fun _ : Circle => (0 : ℝ)) (perturbedInteraction B β η) N = 0 ∧
    SharpLSI.rSym (fun _ : Circle => (0 : ℝ)) (perturbedInteraction B β η) N = 0 := by
  exact ⟨particleTest_lamAll_zero hN B hβ hη,
    particleTest_lamSym_zero hN B hβ hη,
    particleTest_rAll_zero hN B hβ hη,
    particleTest_rSym_zero hN B hβ hη⟩

/-- Generic singular perturbation headline: kernel, particle-rate, and sharp mean-field
conclusions for every admissible baseline and every positive pair of parameters. -/
theorem singular_counterexample_generic (B : BaselineKernel) {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) {N : ℕ} (hN : 2 ≤ N) :
    SingularCounterexampleProperties B β η N := by
  unfold SingularCounterexampleProperties
  rcases perturbedInteraction_basic_properties B hβ hη with
    ⟨hWmeas, hWlower, hWsym, hWdiag, hktendsto⟩
  rcases perturbedKernel_meanfield_rates B hβ hη with ⟨hscalar, hspecies⟩
  rcases singular_particle_zero_rates hN B hβ hη with
    ⟨hlamAll, hlamSym, hrAll, hrSym⟩
  exact ⟨perturbedKernel_admissible B hβ hη,
    perturbedKernel_has_pos_nonzero_fourier B hβ hη,
    hktendsto, hWmeas, hWlower, hWsym, hWdiag,
    fun hB => perturbedKernel_smooth_off_collision B β η hB,
    fun hB => perturbedInteraction_smooth_off_diagonal B β η hB,
    fun y => perturbedInteraction_tendsto_diagonal B hβ hη y,
    hlamAll, hlamSym, hrAll, hrSym, hscalar, hspecies⟩

/-- The repulsive cosine specialization also has unconditional off-diagonal smoothness of
the kernel and lifted pair interaction, since its baseline is smooth periodic. -/
theorem singular_counterexample_cosine {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    {N : ℕ} (hN : 2 ≤ N) :
    SingularCounterexampleProperties cosineBaseline β η N ∧
    ContDiffOn ℝ ∞ (fun t : ℝ => perturbedKernel cosineBaseline β η (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)} ∧
    ContDiffOn ℝ ∞
      (fun p : Fin 2 → ℝ =>
        perturbedInteraction cosineBaseline β η (torusPoint (p 0)) (torusPoint (p 1)))
      {p : Fin 2 → ℝ | torusPoint (p 0) ≠ torusPoint (p 1)} := by
  have hbaseline : ContDiff ℝ ∞ (cosineBaselineKernel ∘ torusLift) :=
    cosineBaselineKernel_smooth_periodic
  have hlift : ContDiff ℝ ∞ (fun t : ℝ => cosineBaselineKernel (torusPoint t)) := by
    have hdiag : ContDiff ℝ ∞ (fun t : ℝ => fun _ : Fin 1 => t) := by fun_prop
    have hcomp := hbaseline.comp hdiag
    have heq : (cosineBaselineKernel ∘ torusLift) ∘
        (fun t : ℝ => fun _ : Fin 1 => t) =
        fun t => cosineBaselineKernel (torusPoint t) := by
      funext t
      change cosineBaselineKernel (torusLift (fun _ : Fin 1 => t)) = _
      rw [show torusLift (fun _ : Fin 1 => t) = torusPoint t by
        simp [torusPoint, DGPS.torusLift]]
    rw [← heq]
    exact hcomp
  have hB : ContDiffOn ℝ ∞ (fun t : ℝ => cosineBaseline.g (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)} := by
    change ContDiffOn ℝ ∞ (fun t : ℝ => cosineBaselineKernel (torusPoint t)) _
    exact hlift.contDiffOn
  refine ⟨singular_counterexample_generic cosineBaseline hβ hη hN,
    perturbedKernel_smooth_off_collision cosineBaseline β η hB,
    perturbedInteraction_smooth_off_diagonal cosineBaseline β η hB⟩

/-- The Green perturbation has strictly positive nonzero Fourier coefficients. -/
theorem greenPerturbedKernel_has_pos_nonzero_fourier {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) :
    HasPosNonzeroFourier (perturbedKernel greenBaseline β η) :=
  perturbedKernel_has_pos_nonzero_fourier greenBaseline hβ hη

/-- The Green perturbation diverges at collision through nonzero circle points. -/
theorem greenPerturbedKernel_tendsto_collision {β η : ℝ}
    (hβ : 0 < β) (hη : 0 < η) :
    Tendsto (perturbedKernel greenBaseline β η) (𝓝[≠] (0 : Circle)) atTop :=
  perturbedKernel_tendsto_collision greenBaseline hβ hη

/-- On every compact set disjoint from the collision point, the perturbed Green kernel is
bounded in absolute value. -/
theorem greenPerturbedKernel_bounded_on_compact_away
    {K : Set Circle} (hK : IsCompact K) (h0 : (0 : Circle) ∉ K)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |perturbedKernel greenBaseline β η x| ≤ C := by
  obtain ⟨δ, hδ, hδK⟩ := compact_away_zero_distance K hK h0
  obtain ⟨C, hC, hbar⟩ := barrier_bound_away_zero hδ
  refine ⟨β * (1 / 8 + η * C), by positivity, fun x hx => ?_⟩
  have hbarx := hbar x (hδK x hx)
  have hinner : |greenKernel x + η * barrier x| ≤ 1 / 8 + η * C := by
    calc
      |greenKernel x + η * barrier x| ≤ |greenKernel x| + |η * barrier x| := abs_add_le _ _
      _ ≤ 1 / 8 + η * C := by
        refine add_le_add (greenKernel_abs_le x) ?_
        calc
          |η * barrier x| = η * barrier x := abs_of_nonneg (mul_nonneg hη.le (barrier_nonneg x))
          _ ≤ η * C := mul_le_mul_of_nonneg_left hbarx hη.le
  change |β * (greenKernel x + η * barrier x)| ≤ β * (1 / 8 + η * C)
  rw [abs_mul, abs_of_pos hβ]
  exact mul_le_mul_of_nonneg_left hinner hβ.le

/-- The full periodic Green specialization of the generic singular counterexample. It includes
the fixed-particle and sharp mean-field conclusions, off-diagonal smoothness, the baseline
Lipschitz bound, local boundedness away from collision, and divergence at collision. -/
theorem singular_counterexample_green {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    {N : ℕ} (hN : 2 ≤ N) :
    SingularCounterexampleProperties greenBaseline β η N ∧
    TorusLipschitzWith (1 / 2) greenKernel ∧
    ContDiffOn ℝ ∞ (fun t : ℝ => perturbedKernel greenBaseline β η (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)} ∧
    ContDiffOn ℝ ∞
      (fun p : Fin 2 → ℝ =>
        perturbedInteraction greenBaseline β η (torusPoint (p 0)) (torusPoint (p 1)))
      {p : Fin 2 → ℝ | torusPoint (p 0) ≠ torusPoint (p 1)} ∧
    (∀ K : Set Circle, IsCompact K → (0 : Circle) ∉ K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |perturbedKernel greenBaseline β η x| ≤ C) := by
  have hB : ContDiffOn ℝ ∞ (fun t : ℝ => greenBaseline.g (torusPoint t))
      {t : ℝ | torusPoint t ≠ (0 : Circle)} := by
    change ContDiffOn ℝ ∞ (fun t : ℝ => greenKernel (torusPoint t)) _
    exact greenKernel_smooth_off_collision
  refine ⟨singular_counterexample_generic greenBaseline hβ hη hN,
    greenKernel_lipschitz,
    perturbedKernel_smooth_off_collision greenBaseline β η hB,
    perturbedInteraction_smooth_off_diagonal greenBaseline β η hB,
    fun K hK h0 => greenPerturbedKernel_bounded_on_compact_away hK h0 hβ hη⟩

end DGPS.SingularCounterexample
