import DGPS.Examples.PolynomialVaryingLimits

/-! Near-baseline scalar sublevels at fields tending to zero are captured by
the true Haar origin. This uses actual uniform compactness and actual origin
strictness; no localization, stability or positive limiting gap is assumed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.PositiveRankOne DGPS.Examples.PolynomialExactGap
open DGPS.Examples.ThreeSpeciesCircle DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem information_from_score (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1)
    {K E : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hL : ∀ x, |(polynomialRankOne h).dlogq x| ≤ E)
    (hP : ∀ x, |(polynomialRankOne h).dφ x| ≤ K) :
    DGPS.Analysis.circleFisherInformation ρ ≤
      2 * (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal +
        4 * E ^ 2 + 4 * eta ^ 2 * K ^ 2 *
          (∫ x, (polynomialRankOne h).φ x ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 := by
  let M := polynomialRankOne h
  let θ := eta * ∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))
  let S := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x + θ * (ρ.sqrt x * M.dφ x)
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hs : MemLp S 2 (haar 1) :=
    (((memLp_coord hw.memLp_grad 0).const_mul 2).sub
      (RankOneModel.memLp_mul_cont M.dlogq_cont ρ.memLp_sqrt)).add
        ((RankOneModel.memLp_mul_cont M.dφ_cont ρ.memLp_sqrt).const_mul θ)
  have hD : (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal =
      ∫ x, S x ^ 2 ∂haar 1 := by
    rw [polynomial_scalar_score_square, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hpt (x : Torus 1) : 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ≤
      2 * S x ^ 2 + (4 * E ^ 2 + 4 * θ ^ 2 * K ^ 2) * ρ.density x := by
    have hl := pow_le_pow_left₀ (abs_nonneg _) (hL x) 2
    have hp := pow_le_pow_left₀ (abs_nonneg _) (hP x) 2
    rw [sq_abs] at hl hp
    have h1 := mul_le_mul_of_nonneg_left hl (sq_nonneg (ρ.sqrt x))
    have h2 := mul_le_mul_of_nonneg_left hp (mul_nonneg (sq_nonneg θ) (sq_nonneg (ρ.sqrt x)))
    change 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ≤
      2 * S x ^ 2 + (4 * E ^ 2 + 4 * θ ^ 2 * K ^ 2) * ρ.sqrt x ^ 2
    dsimp only [S]
    nlinarith [sq_nonneg (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 -
      2 * ρ.sqrt x * M.dlogq x + 2 * θ * (ρ.sqrt x * M.dφ x)),
      sq_nonneg (ρ.sqrt x * M.dlogq x + θ * (ρ.sqrt x * M.dφ x))]
  have hi := integral_mono ((memLp_coord hw.memLp_grad 0).integrable_sq.const_mul 4)
    ((hs.integrable_sq.const_mul 2).add (ρ.integrable_density.const_mul _)) hpt
  change (∫ x, 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1) ≤
    ∫ x, 2 * S x ^ 2 + (4 * E ^ 2 + 4 * θ ^ 2 * K ^ 2) * ρ.density x ∂haar 1 at hi
  have hm : (∫ x, (4 * E ^ 2 + 4 * θ ^ 2 * K ^ 2) * ρ.density x ∂haar 1) =
      4 * E ^ 2 + 4 * θ ^ 2 * K ^ 2 := by rw [integral_const_mul, ρ.integral_density, mul_one]
  rw [integral_add (hs.integrable_sq.const_mul 2) (ρ.integrable_density.const_mul _), hm] at hi
  have hI : DGPS.Analysis.circleFisherInformation ρ =
      ∫ x, 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1 := by
    unfold DGPS.Analysis.circleFisherInformation
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      change 4 * ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 = 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2
      rw [RankOneModel.norm_sq_tangent])
  rw [hI, hD]
  have hi' : (∫ x, 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1) ≤
      2 * (∫ x, S x ^ 2 ∂haar 1) + 4 * E ^ 2 + 4 * θ ^ 2 * K ^ 2 := by
    simpa only [integral_const_mul, add_assoc] using hi
  dsimp only [θ] at hi'
  nlinarith

private theorem density_haar_root (ρ : AbsoluteDensity 1)
    (hρ : (densityMeasure ρ : Measure (Torus 1)) = haar 1) :
    ρ.sqrt =ᵐ[haar 1] fun _ => 1 := by
  let ρ0 := (polynomialRankOne 0).absQ
  have h0 : (densityMeasure ρ0 : Measure (Torus 1)) = haar 1 := by
    rw [(polynomialRankOne 0).densityMeasure_absQ]
    change (haar 1).withDensity (fun x => ENNReal.ofReal ((polynomialRankOne 0).q x)) = _
    simp_rw [polynomial_reference_origin]
    simp
  have he := (densityMeasure_eq_iff_STR02901 ρ ρ0).1 (hρ.trans h0.symm)
  filter_upwards [he, ρ.sqrt_nonneg] with x hx hp
  have hz : ρ0.sqrt x = 1 := by
    change Real.sqrt ((polynomialRankOne 0).q x) = 1
    rw [polynomial_reference_origin, Real.sqrt_one]
  change ρ.sqrt x ^ 2 = ρ0.sqrt x ^ 2 at hx
  rw [hz] at hx
  change 0 ≤ ρ.sqrt x at hp
  nlinarith

/-- Genuine reference capture for near-baseline original scalar competitors.
The original H1 norm is the sum of Haar L2 norms of sqrt(rho)-1 and its stored
weak gradient. The limit, all information bounds and both limits are derived. -/
theorem polynomial_scalar_origin_capture (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (Mq : ℝ) (hMq : 0 ≤ Mq) (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hQ : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) ≤ ENNReal.ofReal Mq)
    (hnear : ∀ t : ℝ, 0 < t → ∀ᶠ n in atTop,
      scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) ≤
        ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 + t)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n =>
        (eLpNorm (fun x => (ρ (φ n)).sqrt x - 1) 2 (haar 1)).toReal +
        (eLpNorm (weakGradient (ρ (φ n)).sqrt (ρ (φ n)).sqrt_mem) 2 (haar 1)).toReal) atTop (𝓝 0) := by
  obtain ⟨φ, ρL, η, R, hφ, hη, hae, hub, hRL, hH, _⟩ :=
    polynomial_varying_scalar_root_compactness h hh b Mq hMq ρ hG hQ
  let hs := fun n => h (φ n)
  let τ := fun n => ρ (φ n)
  let bs := fun n => b (φ n)
  let A0 := canonical_elementary_polynomial_model 0
  let b0 := lipschitz_absoluteDrift A0 (lipschitzData_canonical_model 0)
  have hhs : Tendsto hs atTop (𝓝 0) := hh.comp hφ.tendsto_atTop
  obtain ⟨hgap, hdiss⟩ := polynomial_varying_scalar_limits hs hhs bs τ ρL hη hae R hub
  let g : ℝ := scalarGap A0 ρL
  let d : ℝ := (scalarDissipation A0 b0 ρL).toReal
  have hg0 : 0 ≤ g := NNReal.coe_nonneg _
  have ha : 0 < DGPS.Circle.AngularNormalization.a0 := by unfold DGPS.Circle.AngularNormalization.a0; positivity
  have hdenlim : Tendsto (fun n => 2 * (scalarGap (canonical_elementary_polynomial_model (hs n)) (τ n) : ℝ≥0∞)) atTop
      (𝓝 (2 * (scalarGap A0 ρL : ℝ≥0∞))) :=
    ENNReal.Tendsto.const_mul hgap (Or.inr (by norm_num))
  have hupper (t : ℝ) (ht : 0 < t) : d ≤ 2 * (DGPS.Circle.AngularNormalization.a0 + t) * g := by
    have hq := hφ.tendsto_atTop.eventually (hnear t ht)
    have he : ∀ᶠ n in atTop, scalarDissipation (canonical_elementary_polynomial_model (hs n)) (bs n) (τ n) ≤
        ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 + t) *
          (2 * (scalarGap (canonical_elementary_polynomial_model (hs n)) (τ n) : ℝ≥0∞)) := by
      filter_upwards [hq] with n hn
      have hn0 : 2 * (scalarGap (canonical_elementary_polynomial_model (hs n)) (τ n) : ℝ≥0∞) ≠ 0 :=
        mul_ne_zero (by norm_num) (by exact_mod_cast (hG (φ n)).ne')
      have hnt : 2 * (scalarGap (canonical_elementary_polynomial_model (hs n)) (τ n) : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
      exact (ENNReal.div_le_iff hn0 hnt).1 hn
    have htend := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 + t))
      hdenlim (Or.inr ENNReal.ofReal_ne_top)
    have hlim := hdiss.trans ((liminf_le_liminf he).trans_eq htend.liminf_eq)
    have hfin : ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 + t) *
        (2 * (scalarGap A0 ρL : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
    have hr := ENNReal.toReal_mono hfin hlim
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul,
      ENNReal.toReal_ofNat, ENNReal.coe_toReal] at hr
    change d ≤ _ at hr
    dsimp only [g]
    nlinarith
  have hd0 : d ≤ 2 * DGPS.Circle.AngularNormalization.a0 * g := by
    by_contra hn
    have hstrict : 0 < d - 2 * DGPS.Circle.AngularNormalization.a0 * g := by linarith
    let t := (d - 2 * DGPS.Circle.AngularNormalization.a0 * g) / (4 * (g + 1))
    have ht : 0 < t := div_pos hstrict (by positivity)
    have he : t * (4 * (g + 1)) = d - 2 * DGPS.Circle.AngularNormalization.a0 * g :=
      div_mul_cancel₀ _ (by positivity)
    have hu := hupper t ht
    nlinarith [mul_nonneg ht.le hg0]
  have hgzero : scalarGap A0 ρL = 0 := by
    by_contra hn
    have ht := polynomial_origin_scalar_strict b0 ρL (pos_iff_ne_zero.2 hn)
    change 2 * DGPS.Circle.AngularNormalization.a0 * g < d at ht
    linarith
  have hgReal : g = 0 := by dsimp only [g]; rw [hgzero]; rfl
  have hD0 : scalarDissipation A0 b0 ρL = 0 := by
    obtain ⟨_, hfin, _⟩ := polynomial_origin_scalar_identities b0 ρL
    have hnn : 0 ≤ d := ENNReal.toReal_nonneg
    have hr : (scalarDissipation A0 b0 ρL).toReal = 0 := by change d = 0; rw [hgReal] at hd0; linarith
    exact (ENNReal.toReal_eq_zero_iff _).1 hr |>.resolve_right hfin
  have hH0 : DGPS.Analysis.circleEntropy ρL = 0 := by
    have hg := (polynomial_origin_scalar_identities b0 ρL).1
    have hηpos := eta_pos
    rw [hgzero] at hg
    simp only [NNReal.coe_zero] at hg
    have hHnn := circleEntropy_nonneg ρL
    nlinarith [sq_nonneg (∫ x, (polynomialRankOne 0).φ x ∂(densityMeasure ρL : Measure (Torus 1)))]
  have hρL : (densityMeasure ρL : Measure (Torus 1)) = haar 1 := by
    apply relativeEntropy_zero_iff.1
    have he : (relativeEntropy (densityMeasure ρL : Measure (Torus 1)) (haar 1)).toReal = 0 := by
      rw [← circleEntropy_eq_relativeEntropy, hH0]
    exact ((ENNReal.toReal_eq_zero_iff _).1 he).resolve_right (absoluteDensity_entropy_finite ρL).2.2.1
  have hroot := density_haar_root ρL hρL
  have hgap0 : Tendsto (fun n => (scalarGap (canonical_elementary_polynomial_model (hs n)) (τ n) : ℝ)) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => (scalarGap (canonical_elementary_polynomial_model (hs n)) (τ n) : ℝ))
        atTop (𝓝 (scalarGap A0 ρL : ℝ)) := by
      simpa only [Function.comp_def, ENNReal.coe_toReal] using
        (ENNReal.tendsto_toReal ENNReal.coe_ne_top).comp hgap
    simpa only [hgzero, NNReal.coe_zero] using ht
  have hDseq : Tendsto (fun n => scalarDissipation (canonical_elementary_polynomial_model (hs n)) (bs n) (τ n)) atTop (𝓝 0) := by
    have hprod := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Mq) hdenlim (Or.inr ENNReal.ofReal_ne_top)
    have hup (n : ℕ) : scalarDissipation (canonical_elementary_polynomial_model (hs n)) (bs n) (τ n) ≤
        ENNReal.ofReal Mq * (2 * (scalarGap (canonical_elementary_polynomial_model (hs n)) (τ n) : ℝ≥0∞)) :=
      (ENNReal.div_le_iff (mul_ne_zero (by norm_num) (by exact_mod_cast (hG (φ n)).ne'))
        (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)).1 (hQ (φ n))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le) hup
    simpa only [hgzero, ENNReal.coe_zero, mul_zero] using hprod
  have hDreal : Tendsto (fun n => (scalarDissipation (canonical_elementary_polynomial_model (hs n)) (bs n) (τ n)).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hDseq
  let m := fun n => ∫ x, (polynomialRankOne (hs n)).φ x ∂(densityMeasure (τ n) : Measure (Torus 1))
  have hm2 : Tendsto (fun n => m n ^ 2) atTop (𝓝 0) := by
    have hηpos := eta_pos
    have hbound (n : ℕ) : m n ^ 2 ≤
        (scalarGap (canonical_elementary_polynomial_model (hs n)) (τ n) : ℝ) / (eta / 2) := by
      have hi := (positive_rank_one_scalar_case (polynomialRankOne (hs n))
        (polynomialRankOneDrift (hs n) (bs n)) (τ n)).1
      rw [polynomialRankOne_speciesGap, speciesGap_single] at hi
      apply (le_div_iff₀ (by positivity : 0 < eta / 2)).2
      change m n ^ 2 * (eta / 2) ≤ _
      have hnn : 0 ≤ (relativeEntropy (densityMeasure (τ n) : Measure (Torus 1))
          (polynomialRankOne (hs n)).ref.measure).toReal := ENNReal.toReal_nonneg
      change (scalarGap (canonical_elementary_polynomial_model (hs n)) (τ n) : ℝ) =
        (relativeEntropy (densityMeasure (τ n) : Measure (Torus 1))
          (polynomialRankOne (hs n)).ref.measure).toReal + eta / 2 * m n ^ 2 at hi
      nlinarith
    exact squeeze_zero (fun _ => sq_nonneg _) hbound (by simpa using hgap0.div_const (eta / 2))
  obtain ⟨K, δ, hK, hδ, _, hdata⟩ := polynomial_uniform_data_bound
  obtain ⟨ε, hε, herr⟩ := polynomial_uniform_data_at_origin
  have hεs := hε.comp hhs
  have hsmall : ∀ᶠ n in atTop, |hs n| ≤ δ := by
    have ht : Tendsto (fun n => |hs n|) atTop (𝓝 0) := by simpa using hhs.abs
    exact (ht.eventually (gt_mem_nhds hδ)).mono fun _ hn => hn.le
  have hIb : ∀ᶠ n in atTop, DGPS.Analysis.circleFisherInformation (τ n) ≤
      2 * (scalarDissipation (canonical_elementary_polynomial_model (hs n)) (bs n) (τ n)).toReal +
        4 * ε (hs n) ^ 2 + 4 * eta ^ 2 * K ^ 2 * m n ^ 2 := by
    filter_upwards [hsmall] with n hn
    have he (x : Torus 1) : |(polynomialRankOne (hs n)).dlogq x| ≤ ε (hs n) := by
      have ht := herr (hs n) x
      linarith [abs_nonneg ((polynomialRankOne (hs n)).φ x - (polynomialRankOne 0).φ x),
        abs_nonneg ((polynomialRankOne (hs n)).Aq x - (polynomialRankOne 0).Aq x),
        abs_nonneg (Real.log ((polynomialRankOne (hs n)).q x)),
        abs_nonneg ((polynomialRankOne (hs n)).dφ x - (polynomialRankOne 0).dφ x)]
    have hEnn : 0 ≤ ε (hs n) := (abs_nonneg _).trans (he 0)
    exact information_from_score (hs n) (bs n) (τ n) hK.le hEnn he (fun x => (hdata (hs n) hn x).2.2.2.2)
  have hIseq : Tendsto (fun n => DGPS.Analysis.circleFisherInformation (τ n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (show Tendsto (fun n =>
      2 * (scalarDissipation (canonical_elementary_polynomial_model (hs n)) (bs n) (τ n)).toReal +
        4 * ε (hs n) ^ 2 + 4 * eta ^ 2 * K ^ 2 * m n ^ 2) atTop (𝓝 0) from by
      simpa using ((hDreal.const_mul 2).add ((hεs.pow 2).const_mul 4)).add
        (hm2.const_mul (4 * eta ^ 2 * K ^ 2)))
    exact hIb.mono fun n hn => by simpa only [Real.norm_eq_abs, abs_of_nonneg (circleFisherInformation_nonneg (τ n))] using hn
  have hRint : Tendsto (fun n => ∫ x, ((τ n).sqrt x - 1) ^ 2 ∂haar 1) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun n => ?_) (by simpa using hη.pow 2)
    have hi := ((τ n).memLp_sqrt.sub (memLp_const (1 : ℝ))).integrable_sq
    calc _ ≤ ∫ _x, η n ^ 2 ∂haar 1 := integral_mono_ae hi (integrable_const _) (by
          filter_upwards [hae n, hroot] with x hx hz
          rw [hz] at hx
          exact sq_le_sq.mpr (hx.trans (le_abs_self _)))
      _ = η n ^ 2 := by simp
  have hRnorm : Tendsto (fun n => (eLpNorm (fun x => (τ n).sqrt x - 1) 2 (haar 1)).toReal) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => Real.sqrt (∫ x, ((τ n).sqrt x - 1) ^ 2 ∂haar 1)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero] using hRint.sqrt
    convert ht using 1
    funext n
    change (eLpNorm ((τ n).sqrt - (fun _ : Torus 1 => (1 : ℝ))) 2 (haar 1)).toReal =
      Real.sqrt (∫ x, (((τ n).sqrt - (fun _ : Torus 1 => (1 : ℝ))) x) ^ 2 ∂haar 1)
    exact toReal_eLpNorm_two ((τ n).memLp_sqrt.sub (memLp_const (1 : ℝ)))
  have hGrad : Tendsto (fun n => (eLpNorm (weakGradient (τ n).sqrt (τ n).sqrt_mem) 2 (haar 1)).toReal) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => Real.sqrt (DGPS.Analysis.circleFisherInformation (τ n) / 4))
        atTop (𝓝 0) := by
      simpa only [zero_div, Real.sqrt_zero] using (hIseq.div_const 4).sqrt
    convert ht using 1
    funext n
    rw [toReal_eLpNorm_two_vec (isWeakGradient_weakGradient (τ n).sqrt_mem).memLp_grad]
    congr 1
    unfold DGPS.Analysis.circleFisherInformation
    ring
  exact ⟨φ, hφ, by simpa only [zero_add, τ] using hRnorm.add hGrad⟩

end DGPS.Examples.PolynomialSpecies
