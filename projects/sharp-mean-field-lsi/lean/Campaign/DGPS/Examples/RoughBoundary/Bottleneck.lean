import DGPS.Examples.RoughBoundary.FreeEnergy
import DGPS.Examples.RoughBoundary.Particle

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

private lemma product_exp_integral_RUF041 {L : ℝ} (ε : ℝ) (N : ℕ+) (t : E2) :
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

private lemma product_measure_eq_of_rectangles_RUF041 {N : ℕ+}
    (μ : Measure (Torus 1)) [SigmaFinite μ]
    {ν : Measure (ParticleSpace 1 N)}
    (h : ∀ s : Fin N → Set (Torus 1), (∀ i, MeasurableSet (s i)) →
      ν (Set.pi Set.univ s) = ∏ i, μ (s i)) :
    Measure.pi (fun _ : Fin N => μ) = ν := by
  apply Measure.pi_eq
  exact h

private lemma product_gibbs_tilt_RUF041 {L : ℝ} (hL : 0 < L) (ε : ℝ)
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
    simpa [D, Z, F, f] using product_exp_integral_RUF041 (L := L) ε N t
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
  · exact @product_measure_eq_of_rectangles_RUF041 N
      (gibbsMeasure L ε t) hSigma
      ((particleHaar 1 N).tilted (fun x => F x))
      (fun s hs => hmass s hs)
  · simpa [D, Z, F, f] using product_exp_integral_RUF041 (L := L) ε N t

/-- The exact change-of-measure identity at the selected rough-boundary parameter.
The first equality identifies the product of one-body Gibbs tilts with one product-space tilt.
The second is the unnormalized measure identity. The last equality records the actual normalized
particle law supplied by RUF037. -/
theorem exact_exponential_tilt_identity :
    ∃ L : ℝ, ∃ hL : 0 < L,
      FreeEnergyDecomposition L (1 / L) ∧
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
  obtain ⟨_, L₀, _, hL₀, _, _, L, hL₀L, _, hFree⟩ :=
    exact_free_energy_decomposition_and_unique_haar_minimizer
  have hL : 0 < L := by linarith
  refine ⟨L, hL, hFree, ?_⟩
  intro N z
  rcases rough_particle_hamiltonian_and_oscillation hL (1 / L) N with
    ⟨_, _, _, hLaw, _, _, _⟩
  have hProd := product_gibbs_tilt_RUF041 hL (1 / L) N (kappa • z)
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

end DGPS.Examples.RoughBoundary.Bottleneck

