import DGPS.Examples.RoughBoundary.Bottleneck
import DGPS.Examples.RoughBoundary.BottleneckCoverRUF042
import DGPS.Examples.RoughBoundary.BottleneckFeatureRUF043

set_option maxHeartbeats 2000000

open MeasureTheory
open scoped ENNReal

namespace DGPS.Examples.RoughBoundary.Bottleneck

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.FreeEnergy
open DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Particle
open DGPS.Examples.RoughBoundary.Semicontinuity
open DGPS.Examples.RoughBoundary.Landscape

/-! ### RUF044 helper copies

The tilt identity of RUF041 is stated for the selected parameter `L` only (an existential). Its
proof is valid for every `L > 0`; the private helpers of `Bottleneck.lean` are copied here (renamed
with the RUF044 suffix) so that the identity and the finite-cover estimate hold for the parameter
`L` of RUF043. -/

lemma product_exp_integral_RUF044 {L : ℝ} (ε : ℝ) (N : ℕ+) (t : E2) :
    ∫ x, Real.exp (∑ i, inner ℝ t (Ufeat L ε (x i))) ∂particleHaar 1 N =
      (∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1) ^ Fintype.card (Fin N) := by
  change ∫ x : Fin N → Torus 1,
      Real.exp (∑ i, inner ℝ t (Ufeat L ε (x i)))
      ∂(Measure.pi fun _ : Fin N => haar 1) = _
  calc
    _ = ∫ x, ∏ i, Real.exp (inner ℝ t (Ufeat L ε (x i)))
        ∂(Measure.pi fun _ : Fin N => haar 1) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => Real.exp_sum _ _
    _ = ∏ i, ∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1 :=
          integral_fintype_prod_eq_prod (fun _ y => Real.exp (inner ℝ t (Ufeat L ε y)))
    _ = _ := by simp

lemma product_measure_eq_of_rectangles_RUF044 {N : ℕ+}
    (μ : Measure (Torus 1)) [SigmaFinite μ]
    {ν : Measure (ParticleSpace 1 N)}
    (h : ∀ s : Fin N → Set (Torus 1), (∀ i, MeasurableSet (s i)) →
      ν (Set.pi Set.univ s) = ∏ i, μ (s i)) :
    Measure.pi (fun _ : Fin N => μ) = ν := by
  apply Measure.pi_eq
  exact h

lemma product_gibbs_tilt_RUF044 {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (N : ℕ+) (t : E2) :
    (Measure.pi fun _ : Fin N => gibbsMeasure L ε t) =
      (particleHaar 1 N).tilted
        (fun x => ∑ i, inner ℝ t (Ufeat L ε (x i))) ∧
    ∫ x, Real.exp (∑ i, inner ℝ t (Ufeat L ε (x i))) ∂particleHaar 1 N =
      (∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1) ^ Fintype.card (Fin N) := by
  let f : Torus 1 → ℝ := fun y => inner ℝ t (Ufeat L ε y)
  let Z : ℝ := ∫ y, Real.exp (f y) ∂haar 1
  let F : ParticleSpace 1 N → ℝ := fun x => ∑ i, f (x i)
  let D : ℝ := ∫ x, Real.exp (F x) ∂particleHaar 1 N
  have hInt : Integrable (fun y => Real.exp (f y)) (haar 1) := by
    exact integrable_exp_tilt hL ε t
  have hD : D = Z ^ Fintype.card (Fin N) := by
    simpa [D, Z, F, f] using product_exp_integral_RUF044 (L := L) ε N t
  have hdenfun (x : ParticleSpace 1 N) :
      Real.exp (F x) / D = ∏ i, Real.exp (f (x i)) / Z := by
    rw [hD]
    calc
      Real.exp (F x) / Z ^ Fintype.card (Fin N) =
          (∏ i, Real.exp (f (x i))) / (∏ i : Fin N, Z) := by
            simp [F, Real.exp_sum, Finset.prod_const]
      _ = ∏ i, Real.exp (f (x i)) / Z := by rw [Finset.prod_div_distrib]
  have hrect (s : Fin N → Set (Torus 1)) (hs : ∀ i, MeasurableSet (s i)) :
      ∫ x in Set.pi Set.univ s, Real.exp (F x) / D ∂particleHaar 1 N =
        ∏ i, ∫ y in s i, Real.exp (f y) / Z ∂haar 1 := by
    have hset : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
    have hfun :
        (fun x : ParticleSpace 1 N =>
          Set.indicator (Set.pi Set.univ s) (fun x => Real.exp (F x) / D) x) =
        (fun x => ∏ i, Set.indicator (s i) (fun y => Real.exp (f y) / Z) (x i)) := by
      funext x
      by_cases hx : x ∈ Set.pi Set.univ s
      · have hi : ∀ i, x i ∈ s i := by simpa using hx
        simp [Set.indicator, hx, hi, hdenfun]
      · have hi : ∃ i, x i ∉ s i := by
          by_contra h
          push Not at h
          apply hx
          simpa using h
        obtain ⟨i, hi⟩ := hi
        have hz : ∏ j : Fin N, Set.indicator (s j) (fun y => Real.exp (f y) / Z) (x j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
        rw [hz]
        simp [Set.indicator, hx]
    calc
      _ = ∫ x, Set.indicator (Set.pi Set.univ s)
          (fun x => Real.exp (F x) / D) x ∂particleHaar 1 N := by
            rw [← integral_indicator hset]
      _ = ∫ x, ∏ i, Set.indicator (s i) (fun y => Real.exp (f y) / Z) (x i)
          ∂(Measure.pi fun _ : Fin N => haar 1) := by
            rw [particleHaar]
            exact integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun hfun x)
      _ = ∏ i, ∫ y, Set.indicator (s i) (fun y => Real.exp (f y) / Z) y ∂haar 1 :=
            integral_fintype_prod_eq_prod (fun i y =>
              Set.indicator (s i) (fun y => Real.exp (f y) / Z) y)
      _ = _ := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [integral_indicator (hs i)]
  have hProb : IsProbabilityMeasure (gibbsMeasure L ε t) := by
    change IsProbabilityMeasure ((haar 1).tilted f)
    exact isProbabilityMeasure_tilted hInt
  have hSigma : SigmaFinite (gibbsMeasure L ε t) := by
    have hFinite : IsFiniteMeasure (gibbsMeasure L ε t) :=
      ⟨by rw [hProb.measure_univ]; exact ENNReal.one_lt_top⟩
    exact @IsFiniteMeasure.toSigmaFinite (Torus 1) _ (gibbsMeasure L ε t) hFinite
  have hTiltApply (s : Set (Torus 1)) :
      gibbsMeasure L ε t s =
        ENNReal.ofReal (∫ y in s, Real.exp (f y) / Z ∂haar 1) := by
    change (haar 1).tilted (fun y => f y) s = _
    rw [MeasureTheory.tilted_apply_eq_ofReal_integral]
  have hmass (s : Fin N → Set (Torus 1)) (hs : ∀ i, MeasurableSet (s i)) :
      (particleHaar 1 N).tilted (fun x => F x) (Set.pi Set.univ s) =
        ∏ i, gibbsMeasure L ε t (s i) := by
    have hnonneg (i : Fin N) :
        0 ≤ ∫ y in s i, Real.exp (f y) / Z ∂haar 1 := by
      apply integral_nonneg
      intro y
      positivity
    have hprod :
        ENNReal.ofReal (∏ i, ∫ y in s i, Real.exp (f y) / Z ∂haar 1) =
          ∏ i, ENNReal.ofReal (∫ y in s i, Real.exp (f y) / Z ∂haar 1) :=
      ENNReal.ofReal_prod_of_nonneg (fun i hi => hnonneg i)
    calc
      (particleHaar 1 N).tilted (fun x => F x) (Set.pi Set.univ s) =
          ENNReal.ofReal (∫ x in Set.pi Set.univ s, Real.exp (F x) / D ∂particleHaar 1 N) := by
            rw [MeasureTheory.tilted_apply_eq_ofReal_integral]
      _ = ENNReal.ofReal (∏ i, ∫ y in s i, Real.exp (f y) / Z ∂haar 1) := by
            apply congrArg ENNReal.ofReal
            simpa [D] using hrect s hs
      _ = ∏ i, ENNReal.ofReal (∫ y in s i, Real.exp (f y) / Z ∂haar 1) := hprod
      _ = ∏ i, gibbsMeasure L ε t (s i) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact (hTiltApply (s i)).symm
  constructor
  · exact @product_measure_eq_of_rectangles_RUF044 N
      (gibbsMeasure L ε t) hSigma
      ((particleHaar 1 N).tilted (fun x => F x))
      (fun s hs => hmass s hs)
  · simpa [D, Z, F, f] using product_exp_integral_RUF044 (L := L) ε N t


/-- RUF041 tilt identity for an arbitrary feature parameter `L > 0` (copy of the proof of
`exact_exponential_tilt_identity`, which is the existential case). -/
lemma tilt_identity_RUF044 {L : ℝ} (hL : 0 < L) :
    ∀ N : ℕ+,
    ∀ z : E2,
      (Measure.pi (fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • z)) =
        (particleHaar 1 N).tilted
          (fun x => ∑ i, inner ℝ (kappa • z) (Ufeat L (1 / L) (x i)))) ∧
      ((particleHaar 1 N).withDensity (fun x =>
          ENNReal.ofReal (Real.exp (roughB L (1 / L) N x))) =
        (Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • z)).withDensity
          (fun x => ENNReal.ofReal (Real.exp
            ((N : ℝ) *
              (kappa / 2 *
                ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - z‖ ^ 2 -
                  featurePotential kappa0 (Ufeat L (1 / L)) (kappa • z)))))) ∧
      particleLaw (modelData hL (1 / L)) N =
        (particleHaar 1 N).withDensity (fun x =>
          ENNReal.ofReal
            ((∫ y, Real.exp (roughB L (1 / L) N y) ∂particleHaar 1 N)⁻¹ *
              Real.exp (roughB L (1 / L) N x))) := by
  intro N z
  rcases rough_particle_hamiltonian_and_oscillation hL (1 / L) N with
    ⟨_, _, _, hLaw, _, _, _⟩
  have hProd := product_gibbs_tilt_RUF044 hL (1 / L) N (kappa • z)
  refine ⟨hProd.1, ?_, hLaw⟩
  let f : Torus 1 → ℝ := fun y => inner ℝ (kappa • z) (Ufeat L (1 / L) y)
  let F : ParticleSpace 1 N → ℝ := fun x => ∑ i, f (x i)
  let Z : ℝ := ∫ y, Real.exp (f y) ∂haar 1
  let D : ℝ := ∫ x, Real.exp (F x) ∂particleHaar 1 N
  let mean : ParticleSpace 1 N → E2 := fun x => (N : ℝ)⁻¹ • featureSum L (1 / L) N x
  let w : ParticleSpace 1 N → ℝ := fun x =>
    (N : ℝ) *
      (kappa / 2 * ‖mean x - z‖ ^ 2 -
        featurePotential kappa0 (Ufeat L (1 / L)) (kappa • z))
  have hInt : Integrable (fun y => Real.exp (f y)) (haar 1) := by
    simpa [f] using integrable_exp_tilt hL (1 / L) (kappa • z)
  have hZ : 0 < Z := by exact integral_exp_pos (by simpa [Z] using hInt)
  have hD : D = Z ^ Fintype.card (Fin N) := by
    simpa [D, Z, F, f] using hProd.2
  have hDpos : 0 < D := by rw [hD]; positivity
  have hDexp : D = Real.exp (Real.log D) := (Real.exp_log hDpos).symm
  let Λ : ℝ := featureLogPartition (Ufeat L (1 / L)) (kappa • z)
  have hlogD : Real.log D = (N : ℝ) * Λ := by
    rw [hD, Real.log_pow]
    simp [Λ, featureLogPartition, Z, Fintype.card_fin, f]
  have hQ :
      featurePotential kappa0 (Ufeat L (1 / L)) (kappa • z) =
        kappa / 2 * ‖z‖ ^ 2 - Λ := by
    dsimp [Λ, featurePotential, featureLogPartition]
    rw [← kappa_eq, norm_smul, Real.norm_eq_abs, abs_of_pos kappa_pos]
    field_simp [kappa_pos.ne']
  have hsum (x : ParticleSpace 1 N) :
      F x = kappa * inner ℝ z (featureSum L (1 / L) N x) := by
    change (∑ i, inner ℝ (kappa • z) (Ufeat L (1 / L) (x i))) = _
    rw [← inner_sum, real_inner_smul_left]
    simp [featureSum]
  have hN : 0 < (N : ℝ) := by exact_mod_cast N.pos
  have hmeanNorm (x : ParticleSpace 1 N) :
      ‖mean x‖ ^ 2 = ‖featureSum L (1 / L) N x‖ ^ 2 / (N : ℝ) ^ 2 := by
    dsimp [mean]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hN)]
    field_simp
  have hmeanInner (x : ParticleSpace 1 N) :
      inner ℝ (mean x) z =
        inner ℝ z (featureSum L (1 / L) N x) / (N : ℝ) := by
    dsimp [mean]
    rw [real_inner_smul_left, real_inner_comm]
    ring
  have hsub (x : ParticleSpace 1 N) :
      ‖mean x - z‖ ^ 2 =
        ‖mean x‖ ^ 2 + ‖z‖ ^ 2 - 2 * inner ℝ (mean x) z := by
    rw [norm_sub_sq_real]
    ring
  have hExponent (x : ParticleSpace 1 N) :
      w x + (F x - Real.log D) = roughB L (1 / L) N x := by
    unfold w
    rw [hsub x, hmeanNorm x, hmeanInner x, hsum x, hQ, hlogD]
    unfold roughB
    field_simp [hN.ne']
    ring
  have hReal (x : ParticleSpace 1 N) :
      Real.exp (w x) * (Real.exp (F x) / D) =
        Real.exp (roughB L (1 / L) N x) := by
    calc
      _ = Real.exp (w x) * Real.exp (F x - Real.log D) := by
        congr 1
        calc
          Real.exp (F x) / D = Real.exp (F x) / Real.exp (Real.log D) := by
            exact congrArg (fun q : ℝ => Real.exp (F x) / q) hDexp
          _ = Real.exp (F x - Real.log D) := by rw [← Real.exp_sub]
      _ = Real.exp (w x + (F x - Real.log D)) := by rw [← Real.exp_add]
      _ = _ := by rw [hExponent x]
  have hU : Continuous (Ufeat L (1 / L)) := continuous_Ufeat hL (1 / L)
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_const.inner hU
  have hF : Continuous F := by
    dsimp [F]
    exact continuous_finsetSum Finset.univ (fun i _ => hf.comp (continuous_apply i))
  have hB : Continuous (roughB L (1 / L) N) := by
    have hEq : roughB L (1 / L) N = fun x =>
        kappa * (N : ℝ) / 2 - particleHamiltonian (modelData hL (1 / L)) N x := by
      funext x
      rw [hamiltonian_eq hL (1 / L) N x]
      ring
    rw [hEq]
    exact continuous_const.sub (DGPS.Particle.particleHamiltonian_continuous _ N)
  have hwEq : w = fun x => roughB L (1 / L) N x - F x + Real.log D := by
    funext x
    linarith [hExponent x]
  have hw : Continuous w := by
    rw [hwEq]
    fun_prop
  let ρ : ParticleSpace 1 N → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.exp (F x) / D)
  let σ : ParticleSpace 1 N → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.exp (w x))
  have hρ : Measurable ρ := by dsimp [ρ]; fun_prop
  have hσ : Measurable σ := by dsimp [σ]; fun_prop
  have hDensity (x : ParticleSpace 1 N) :
      ENNReal.ofReal (Real.exp (roughB L (1 / L) N x)) = ρ x * σ x := by
    dsimp [ρ, σ]
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_nonneg _) hDpos.le)]
    apply congrArg ENNReal.ofReal
    calc
      Real.exp (roughB L (1 / L) N x) =
          Real.exp (w x) * (Real.exp (F x) / D) := (hReal x).symm
      _ = _ := by ring
  change (particleHaar 1 N).withDensity
      (fun x => ENNReal.ofReal (Real.exp (roughB L (1 / L) N x))) =
    ((Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • z)).withDensity
      (fun x => ENNReal.ofReal (Real.exp (w x))))
  rw [hProd.1, Measure.tilted, ← withDensity_mul (particleHaar 1 N) hρ hσ]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall hDensity

/-- Finite-cover upper estimate for an arbitrary feature parameter `L > 0` (copy of the proof of
RUF042 `finite_cover_upper_probability_estimate`, with the tilt identity applied at `L`). -/
lemma finite_cover_any_L_RUF044 {L : ℝ} (hL : 0 < L) :
    ∀ K : Set E2, IsCompact K → ∀ aK : ℝ,
      (∀ z ∈ K, aK ≤ featurePotential kappa0 (Ufeat L (1 / L)) (kappa • z)) →
      ∀ δ : ℝ, 0 < δ → ∀ (J : ℕ) (c : Fin J → E2),
        (∀ j, c j ∈ K) → K ⊆ ⋃ j, Metric.ball (c j) δ →
        ∀ N : ℕ+,
          particleLaw (modelData hL (1 / L)) N
              {x | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ K} ≤
            ENNReal.ofReal (J * Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) := by
  have hTilt := tilt_identity_RUF044 hL
  intro K _hK aK hQ δ _hδ J c hc hcover N
  have hk : (0 : ℝ) ≤ kappa := by unfold kappa; norm_num
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hLaw := (hTilt N 0).2.2
  have hZ1 : (1 : ℝ) ≤ ∫ y, Real.exp (roughB L (1 / L) N y) ∂particleHaar 1 N :=
    one_le_normalizer_RUF042 hL N
  have hZinv : (∫ y, Real.exp (roughB L (1 / L) N y) ∂particleHaar 1 N)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hZ1
  have hM : Continuous (fun x : ParticleSpace 1 N => (N : ℝ)⁻¹ • featureSum L (1 / L) N x) := by
    have hU : Continuous (Ufeat L (1 / L)) := continuous_Ufeat hL (1 / L)
    unfold featureSum
    fun_prop
  -- one cover ball: the probability of its event is at most the exponential constant
  have hball : ∀ j : Fin J,
      particleLaw (modelData hL (1 / L)) N
          {x | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ Metric.ball (c j) δ} ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) := by
    intro j
    have _hprob : ∀ _i : Fin N, IsProbabilityMeasure (gibbsMeasure L (1 / L) (kappa • c j)) :=
      fun _ => isProbabilityMeasure_gibbs hL (1 / L) (kappa • c j)
    set S : Set (ParticleSpace 1 N) :=
      {x | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ Metric.ball (c j) δ} with hSdef
    have hS : MeasurableSet S := hM.measurable measurableSet_ball
    have hEq := congrArg (fun m : Measure (ParticleSpace 1 N) => m S) (hTilt N (c j)).2.1
    rw [withDensity_apply _ hS, withDensity_apply _ hS] at hEq
    -- pointwise: the tilt multiplier on the event is at most the displayed exponential
    have hpt : ∀ x ∈ S, ENNReal.ofReal (Real.exp ((N : ℝ) * (kappa / 2 *
        ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ ^ 2 -
          featurePotential kappa0 (Ufeat L (1 / L)) (kappa • c j)))) ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) := by
      intro x hx
      have hd : ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ < δ := mem_ball_iff_norm.1 hx
      have hd2 : ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ ^ 2 ≤ δ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hd.le 2
      have hQj : aK ≤ featurePotential kappa0 (Ufeat L (1 / L)) (kappa • c j) := hQ (c j) (hc j)
      have hin : kappa / 2 * ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ ^ 2 -
          featurePotential kappa0 (Ufeat L (1 / L)) (kappa • c j) ≤
            -(aK - kappa * δ ^ 2 / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hd2 (show (0 : ℝ) ≤ kappa / 2 by linarith)]
      have hexp := mul_le_mul_of_nonneg_left hin hNpos.le
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      calc _ ≤ (N : ℝ) * (-(aK - kappa * δ ^ 2 / 2)) := hexp
        _ = -(N : ℝ) * (aK - kappa * δ ^ 2 / 2) := by ring
    have h1 : ∫⁻ x in S, ENNReal.ofReal ((∫ y, Real.exp (roughB L (1 / L) N y) ∂particleHaar 1 N)⁻¹ *
        Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N ≤
        ∫⁻ x in S, ENNReal.ofReal (Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal
        (mul_le_of_le_one_left (Real.exp_pos _).le hZinv)
    have h3 : ∫⁻ x in S, ENNReal.ofReal (Real.exp ((N : ℝ) * (kappa / 2 *
        ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ ^ 2 -
          featurePotential kappa0 (Ufeat L (1 / L)) (kappa • c j)))) ∂
          (Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) ≤
        ∫⁻ _x in S, ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2)))
          ∂(Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) :=
      setLIntegral_mono' hS hpt
    have h4 := setLIntegral_const (μ := Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j))
      S (ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))))
    have h5 : ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) *
        (Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) S ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) :=
      mul_le_of_le_one_right zero_le prob_le_one
    rw [hLaw, withDensity_apply _ hS]
    calc ∫⁻ x in S, ENNReal.ofReal ((∫ y, Real.exp (roughB L (1 / L) N y) ∂particleHaar 1 N)⁻¹ *
            Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N
        ≤ ∫⁻ x in S, ENNReal.ofReal (Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N := h1
      _ = ∫⁻ x in S, ENNReal.ofReal (Real.exp ((N : ℝ) * (kappa / 2 *
            ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x - c j‖ ^ 2 -
              featurePotential kappa0 (Ufeat L (1 / L)) (kappa • c j)))) ∂
              (Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) := hEq
      _ ≤ ∫⁻ _x in S, ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2)))
            ∂(Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) := h3
      _ = ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) *
            (Measure.pi fun _ : Fin N => gibbsMeasure L (1 / L) (kappa • c j)) S := h4
      _ ≤ _ := h5
  -- the event is covered by the `J` cover events
  have hsub : {x : ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ K} ⊆
      ⋃ j : Fin J,
        {x : ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ Metric.ball (c j) δ} := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcover hx)
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  calc particleLaw (modelData hL (1 / L)) N {x | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ K}
      ≤ particleLaw (modelData hL (1 / L)) N
          (⋃ j : Fin J,
            {x : ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ Metric.ball (c j) δ}) :=
        measure_mono hsub
    _ ≤ ∑ j : Fin J, particleLaw (modelData hL (1 / L)) N
          {x : ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈ Metric.ball (c j) δ} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin J, ENNReal.ofReal (Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) :=
        Finset.sum_le_sum fun j _ => hball j
    _ = ENNReal.ofReal (J * Real.exp (-(N : ℝ) * (aK - kappa * δ ^ 2 / 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg J), ENNReal.ofReal_natCast]

/-- A compact set with a point admits a finite `δ`-net with centres in the set and at least one
centre. -/
lemma exists_finite_net_RUF044 {K : Set E2} (hK : IsCompact K) (hne : K.Nonempty) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ J : ℕ, 0 < J ∧ ∃ c : Fin J → E2, (∀ j, c j ∈ K) ∧ K ⊆ ⋃ j, Metric.ball (c j) δ := by
  obtain ⟨t, htK, htfin, hcov⟩ := finite_cover_balls_of_compact hK hδ
  have hmem : ∀ y, y ∈ htfin.toFinset ↔ y ∈ t := fun y => htfin.mem_toFinset
  refine ⟨htfin.toFinset.card, ?_, fun j => (htfin.toFinset.equivFin.symm j).1,
    fun j => htK ((hmem _).1 (htfin.toFinset.equivFin.symm j).2), ?_⟩
  · obtain ⟨x0, hx0⟩ := hne
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.1 (hcov hx0)
    exact Finset.card_pos.2 ⟨y, (hmem y).2 hy⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
    refine Set.mem_iUnion.2 ⟨htfin.toFinset.equivFin ⟨y, (hmem y).2 hy⟩, ?_⟩
    simpa using hxy

lemma compactBall_RUF044 (zs : E2) (r : ℝ) : IsCompact (compactBall_RUF043 zs r) := by
  have h : compactBall_RUF043 zs r = Metric.closedBall zs (9 * r / 4) := by
    ext z
    simp [compactBall_RUF043, Metric.mem_closedBall, dist_eq_norm]
  rw [h]
  exact isCompact_closedBall _ _

lemma compactAnnulus_RUF044 (zs : E2) (r : ℝ) : IsCompact (compactAnnulus_RUF043 zs r) := by
  refine IsCompact.of_isClosed_subset (compactBall_RUF044 zs r) ?_ ?_
  · have h1 : IsClosed {z : E2 | 3 * r / 4 ≤ ‖z - zs‖} :=
      isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {z : E2 | ‖z - zs‖ ≤ 9 * r / 4} :=
      isClosed_le (by fun_prop) continuous_const
    exact h1.inter h2
  · intro z hz
    simp only [compactAnnulus_RUF043, compactBall_RUF043, Set.mem_ofPred_eq] at hz ⊢
    exact hz.2

/-! ### Main theorem -/

/-- RUF044, basin support and annular exponential upper bounds.

Setting: the RUF043 data for the feature parameter `L > 0` with `ε = 1/L` (the parameter of
RUF041/RUF042), with the same hypotheses as RUF043. For the fixed smooth statistic `Φ` and
radius `R` of RUF043, with `z_* = remoteCentre`, `Δ = Q(z_*)`, `K_B`, `K_S` the compact sets, and
`b = min_{K_S} Q - Δ > 0` (attained), there are positive integers `J_B`, `J_S` with
`P_N(Y_N ∈ B) ≤ J_B e^{-NΔ/2}` and `P_N(Y_N ∈ S) ≤ J_S e^{-N(Δ+b/2)}` for all `N`. -/
theorem basin_support_and_annular_exponential_upper_bounds {L : ℝ} (hL : 0 < L)
    (hcert : RoughLandscapeCertificate (Ufeat L (1 / L))) (tstar : E2) (r₀ lam : ℝ)
    (hr₀ : 0 < r₀) (hlam : 0 < lam)
    (hcrit : fderiv ℝ (featurePotential kappa0 (Ufeat L (1 / L))) tstar = 0)
    (h0 : (0 : E2) ∉ Metric.closedBall tstar r₀)
    (hH : ∀ x ∈ Metric.closedBall tstar r₀, ∀ v : E2,
      lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (featurePotential kappa0 (Ufeat L (1 / L)))) x v v) :
    ∃ R : ℝ, 0 < R ∧ ∃ η : ℝ, 0 < η ∧ η < (R / 4) / 4 ∧ ∃ Φ : Torus 1 → E2,
      (∀ N : ℕ+, ∀ x : ParticleSpace 1 N,
        ‖smoothMean_RUF043 Φ N x - roughMean_RUF043 L (1 / L) N x‖ ≤ η) ∧
      0 < remoteLevel_RUF043 L (1 / L) tstar ∧
      ∃ b : ℝ, 0 < b ∧
        (∀ z ∈ compactAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4),
          remoteLevel_RUF043 L (1 / L) tstar + b ≤ remotePotential_RUF043 L (1 / L) z) ∧
        (∃ z ∈ compactAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4),
          remotePotential_RUF043 L (1 / L) z = remoteLevel_RUF043 L (1 / L) tstar + b) ∧
        ∃ JB JS : ℕ, 0 < JB ∧ 0 < JS ∧ ∀ N : ℕ+,
          particleLaw (modelData hL (1 / L)) N
              {x | smoothMean_RUF043 Φ N x ∈
                Metric.ball (remoteCentre_RUF043 tstar) (2 * (R / 4))} ≤
            ENNReal.ofReal (JB * Real.exp (-(N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar / 2)) ∧
          particleLaw (modelData hL (1 / L)) N
              {x | smoothMean_RUF043 Φ N x ∈
                transitionAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4)} ≤
            ENNReal.ofReal (JS * Real.exp (-(N : ℝ) *
              (remoteLevel_RUF043 L (1 / L) tstar + b / 2))) := by
  obtain ⟨R, hR, hΔpos, hQR, -, -, η, hη, hηr, Φ, -, -, χ, -, -, -, -, -, -, hApprox,
    hBinc, hSinc, hKB, b, hb, hKS, zmin, hzmin, hzeq⟩ :=
    fixed_smooth_bottleneck_feature_and_compatible_neighborhoods hL (1 / L) hcert tstar r₀ lam
      hr₀ hlam hcrit h0 hH
  set zs : E2 := remoteCentre_RUF043 tstar with hzs
  set Δ : ℝ := remoteLevel_RUF043 L (1 / L) tstar with hΔ
  have hκ : 0 < kappa := kappa_pos
  have hKBc : IsCompact (compactBall_RUF043 zs (R / 4)) := compactBall_RUF044 zs (R / 4)
  have hKSc : IsCompact (compactAnnulus_RUF043 zs (R / 4)) := compactAnnulus_RUF044 zs (R / 4)
  have hKBne : (compactBall_RUF043 zs (R / 4)).Nonempty := by
    refine ⟨zs, ?_⟩
    show ‖zs - zs‖ ≤ 9 * (R / 4) / 4
    rw [sub_self, norm_zero]
    positivity
  have hδBpos : 0 < Real.sqrt (Δ / kappa) := Real.sqrt_pos.2 (div_pos hΔpos hκ)
  have hδSpos : 0 < Real.sqrt (b / kappa) := Real.sqrt_pos.2 (div_pos hb hκ)
  have hδB2 : kappa * Real.sqrt (Δ / kappa) ^ 2 / 2 = Δ / 2 := by
    rw [Real.sq_sqrt (div_pos hΔpos hκ).le]
    field_simp
  have hδS2 : kappa * Real.sqrt (b / kappa) ^ 2 / 2 = b / 2 := by
    rw [Real.sq_sqrt (div_pos hb hκ).le]
    field_simp
  obtain ⟨JB, hJB, cB, hcB, hcovB⟩ :=
    exists_finite_net_RUF044 hKBc hKBne hδBpos
  obtain ⟨JS, hJS, cS, hcS, hcovS⟩ :=
    exists_finite_net_RUF044 hKSc ⟨zmin, hzmin⟩ hδSpos
  refine ⟨R, hR, η, hη, hηr, Φ, hApprox, hΔpos, b, hb, hKS, ⟨zmin, hzmin, hzeq⟩, JB, JS, hJB,
    hJS, ?_⟩
  intro N
  constructor
  · have hsubB : {x : ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
        Metric.ball zs (2 * (R / 4))} ⊆
        {x : ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈
          compactBall_RUF043 zs (R / 4)} := by
      intro x hx
      have hx' : smoothMean_RUF043 Φ N x ∈ Metric.ball zs (2 * (R / 4)) := hx
      exact hBinc N x (mem_ball_iff_norm.1 hx')
    have hBound := finite_cover_any_L_RUF044 hL (compactBall_RUF043 zs (R / 4)) hKBc Δ
      (fun z hz => hKB z hz) (Real.sqrt (Δ / kappa)) hδBpos JB cB hcB hcovB N
    have hexp : -(N : ℝ) * (Δ - kappa * Real.sqrt (Δ / kappa) ^ 2 / 2) =
        -(N : ℝ) * Δ / 2 := by
      rw [hδB2]
      ring
    rw [hexp] at hBound
    exact (measure_mono hsubB).trans hBound
  · have hsubS : {x : ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
        transitionAnnulus_RUF043 zs (R / 4)} ⊆
        {x : ParticleSpace 1 N | (N : ℝ)⁻¹ • featureSum L (1 / L) N x ∈
          compactAnnulus_RUF043 zs (R / 4)} := by
      intro x hx
      have hx' : smoothMean_RUF043 Φ N x ∈ transitionAnnulus_RUF043 zs (R / 4) := hx
      exact hSinc N x hx'
    have hBound := finite_cover_any_L_RUF044 hL (compactAnnulus_RUF043 zs (R / 4)) hKSc (Δ + b)
      (fun z hz => hKS z hz) (Real.sqrt (b / kappa)) hδSpos JS cS hcS hcovS N
    have hexp : -(N : ℝ) * (Δ + b - kappa * Real.sqrt (b / kappa) ^ 2 / 2) =
        -(N : ℝ) * (Δ + b / 2) := by
      rw [hδS2]
      ring
    rw [hexp] at hBound
    exact (measure_mono hsubS).trans hBound

end DGPS.Examples.RoughBoundary.Bottleneck
