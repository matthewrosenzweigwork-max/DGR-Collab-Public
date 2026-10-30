import DGPS.Examples.PolynomialScore
import DGPS.Examples.PolynomialMinimizerCapture
import DGPS.Examples.PolynomialEulerCorrectionLimits

/-! Actual continuous root/score capture for every original-domain minimizer
sequence. The score bound comes from the genuine weak equation, its mean and
one-dimensional embedding; score convergence is not supplied as a premise. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.PositiveRankOne DGPS.Examples.ThreeSpeciesCircle
open DGPS.Circle.AngularNormalization DGPS.Circle.VonMisesSmallField

namespace DGPS.Examples.PolynomialSpecies

private theorem score_bound (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h) ρ)
    (hmin : scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b)
    (v S : Torus 1 → ℝ) (hv : Continuous v) (hS : Continuous S)
    (hvae : ρ.sqrt =ᵐ[haar 1] v)
    (hSae : (fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * (polynomialRankOne h).dlogq x) =ᵐ[haar 1] S)
    (U L B : ℝ) (hU : 0 ≤ U) (hL : 0 ≤ L) (hL1 : L ≤ 1) (hB : 0 ≤ B)
    (hvB : ∀ x, |v x| ≤ U) (hσB : ∀ x, |(polynomialRankOne h).dlogq x| ≤ L)
    (hβ : ∀ x, |v x * polynomialEulerCorrection h (scalarRate (canonical_elementary_polynomial_model h) b).toReal ρ x / 2 -
      (scalarRate (canonical_elementary_polynomial_model h) b).toReal *
        (v x * (Real.log (v x ^ 2) - Real.log ((polynomialRankOne h).q x))) -
      polynomialEulerMultiplier h (scalarRate (canonical_elementary_polynomial_model h) b).toReal ρ * v x / 2| ≤ B) :
    ∀ x, |S x| ≤ 2 * (U * L + B) := by
  let M := polynomialRankOne h
  let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
  let β := fun x => v x * polynomialEulerCorrection h r ρ x / 2 -
    r * (v x * (Real.log (v x ^ 2) - Real.log (M.q x))) - polynomialEulerMultiplier h r ρ * v x / 2
  let AT := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * M.dlogq x
  let g := fun x => -(AT x * M.dlogq x) / 2 + v x * polynomialEulerCorrection h r ρ x / 2 -
    r * (v x * (Real.log (v x ^ 2) - Real.log (M.q x))) - polynomialEulerMultiplier h r ρ * v x / 2
  have hAT : IsWeakGradient AT (vec1 g) :=
    polynomial_scalarMinimizer_score_weakGradient h b ρ hG hmin v hv hvae
  obtain ⟨Ac, hAc, hAae, _, hmean⟩ := circle_H1_holder_half hAT
  have hAS : Ac = S := Measure.eq_of_ae_eq (hAae.trans hSae) hAc hS
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hAc.abs.continuousOn
  let T := |Ac x0|
  have hT : 0 ≤ T := abs_nonneg _
  have hTb (x : Torus 1) : |Ac x| ≤ T := hx0 (Set.mem_univ x)
  have hgB : ∀ᵐ x ∂haar 1, ‖vec1 g x‖ ≤ T * L / 2 + B := by
    filter_upwards [hAae] with x hx
    rw [norm_vec1]
    have he : g x = -(AT x * M.dlogq x) / 2 + β x := by dsimp only [g, β]; ring
    rw [he]
    have hprod : |-(AT x * M.dlogq x) / 2| ≤ T * L / 2 := by
      rw [← hx, abs_div, abs_neg, abs_mul, abs_two]
      have hi := mul_le_mul (hTb x) (hσB x) (abs_nonneg _) hT
      linarith
    exact (abs_add_le _ _).trans (add_le_add hprod (hβ x))
  have hnorm : (eLpNorm (vec1 g) 2 (haar 1)).toReal ≤ T * L / 2 + B := by
    have he := eLpNorm_le_of_ae_bound (p := 2) hAT.memLp_grad.aestronglyMeasurable hgB
    simp only [measure_univ, ENNReal.one_rpow, one_mul] at he
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
    rwa [ENNReal.toReal_ofReal (by positivity : 0 ≤ T * L / 2 + B)] at ht
  have hmeanB : |∫ x, AT x ∂haar 1| ≤ U * L := by
    have hw := isWeakGradient_weakGradient ρ.sqrt_mem
    have iv : Integrable (fun x => v x * M.dlogq x) (haar 1) :=
      (hv.mul M.dlogq_cont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have he : (∫ x, AT x ∂haar 1) = -(∫ x, v x * M.dlogq x ∂haar 1) := by
      dsimp only [AT]
      rw [integral_sub (((memLp_coord hw.memLp_grad 0).integrable one_le_two).const_mul 2) iv,
        integral_const_mul, bs_integral_grad hw]
      ring
    have hi := norm_integral_le_of_norm_le_const (μ := haar 1)
      (f := fun x => v x * M.dlogq x) (C := U * L) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hvB x) (hσB x) (abs_nonneg _) hU)
    rw [he, abs_neg]
    simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using hi
  have hi : T ≤ U * L + (T * L / 2 + B) := by
    have hosc := (hmean x0).trans hnorm
    have ht := abs_add_le (Ac x0 - ∫ x, AT x ∂haar 1) (∫ x, AT x ∂haar 1)
    rw [sub_add_cancel] at ht
    dsimp only [T]
    linarith
  have hTbnd : T ≤ 2 * (U * L + B) := by
    have he := mul_le_mul_of_nonneg_left hL1 hT
    nlinarith
  intro x
  rw [← hAS]
  exact (hTb x).trans hTbnd

/-- Every actual full-domain minimizer sequence has the same strictly
increasing subsequence of actual continuous root/score representatives with
root uniformly tending to one and score uniformly tending to zero. All
information, root, rate, feedback and score controls are derived internally. -/
theorem polynomial_scalarMinimizer_root_score_capture (h : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hmin : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) =
      scalarRate (canonical_elementary_polynomial_model (h n)) (b n)) :
    ∃ φ : ℕ → ℕ, ∃ v S : ℕ → Torus 1 → ℝ, ∃ θ : ℕ → ℝ,
      StrictMono φ ∧ Tendsto θ atTop (𝓝 0) ∧
      (∀ n, Continuous (v n) ∧ Continuous (S n) ∧ (ρ (φ n)).sqrt =ᵐ[haar 1] v n ∧
        (∀ t : ℝ, HasDerivAt (fun s => v n (pt s))
          ((S n (pt t) + v n (pt t) * (polynomialRankOne (h (φ n))).dlogq (pt t)) / 2) t) ∧
        (∀ t : ℝ, HasDerivAt (fun s => S n (pt s))
          (let hs := h (φ n); let rs := (scalarRate (canonical_elementary_polynomial_model hs) (b (φ n))).toReal;
          -(S n (pt t) * (polynomialRankOne hs).dlogq (pt t)) / 2 +
            v n (pt t) * polynomialEulerCorrection hs rs (ρ (φ n)) (pt t) / 2 -
              rs * (v n (pt t) * (Real.log (v n (pt t) ^ 2) - Real.log ((polynomialRankOne hs).q (pt t)))) -
                polynomialEulerMultiplier hs rs (ρ (φ n)) * v n (pt t) / 2) t)) ∧
      (∀ n x, |v n x - 1| ≤ θ n) ∧ USmall (fun n t => S n (pt t)) := by
  classical
  choose V W hVc hWc hrep hnon hgrad hVd hWd using
    fun n => polynomial_scalarMinimizer_classicalScore (h n) (b n) (ρ n) (hG n) (hmin n)
  obtain ⟨φ, hφ, hcapture⟩ := polynomial_scalarMinimizer_origin_capture h hh b ρ hG hmin
  let hs := fun n => h (φ n)
  let bs := fun n => b (φ n)
  let τ := fun n => ρ (φ n)
  let v := fun n => V (φ n)
  let S := fun n => W (φ n)
  let M := fun n => polynomialRankOne (hs n)
  let r := fun n => (scalarRate (canonical_elementary_polynomial_model (hs n)) (bs n)).toReal
  have hhs : Tendsto hs atTop (𝓝 0) := hh.comp hφ.tendsto_atTop
  have hv : ∀ n, Continuous (v n) := fun n => hVc (φ n)
  have hS : ∀ n, Continuous (S n) := fun n => hWc (φ n)
  have hae : ∀ n, (τ n).sqrt =ᵐ[haar 1] v n := fun n => hrep (φ n)
  have hw := fun n => isWeakGradient_weakGradient (τ n).sqrt_mem
  have hroot : Tendsto (fun n => (eLpNorm (fun x => (τ n).sqrt x - 1) 2 (haar 1)).toReal) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hcapture
    exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  have hroot' : Tendsto (fun n => eLpNorm (fun x => (τ n).sqrt x - 1) 2 (haar 1)) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_iff (fun n => ((τ n).memLp_sqrt.sub (memLp_const (1 : ℝ))).eLpNorm_ne_top)
      ENNReal.zero_ne_top).1 (by simpa only [Pi.sub_def, ENNReal.toReal_zero] using hroot)
  have hgrad0 : Tendsto (fun n => (eLpNorm (weakGradient (τ n).sqrt (τ n).sqrt_mem) 2 (haar 1)).toReal)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hcapture
    exact le_add_of_nonneg_left ENNReal.toReal_nonneg
  have hgrad' : Tendsto (fun n => eLpNorm (fun x => weakGradient (τ n).sqrt (τ n).sqrt_mem x -
      (0 : Tangent 1)) 2 (haar 1)) atTop (𝓝 0) := by
    simpa only [sub_zero] using
      (ENNReal.tendsto_toReal_iff (fun n => (hw n).memLp_grad.eLpNorm_ne_top) ENNReal.zero_ne_top).1
        (by simpa using hgrad0)
  have hU : TendstoUniformly v (fun _ : Torus 1 => (1 : ℝ)) atTop :=
    circle_H1_tendstoUniformly hw (isWeakGradient_const (d := 1) 1) hv
      (fun n => (hae n).symm) continuous_const (EventuallyEq.refl _ _) hroot' hgrad'
  let θ := fun n => ⨆ x, |v n x - 1|
  have hbdd (n : ℕ) : BddAbove (Set.range fun x => |v n x - 1|) :=
    (isCompact_range (((hv n).sub continuous_const).abs)).bddAbove
  have hθb (n : ℕ) (x : Torus 1) : |v n x - 1| ≤ θ n := le_ciSup (hbdd n) x
  have hθ0 (n : ℕ) : 0 ≤ θ n := (abs_nonneg _).trans (hθb n 0)
  have hθ : Tendsto θ atTop (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hθ0 n), fun a ha => ?_⟩
    filter_upwards [(Metric.tendstoUniformly_iff.1 hU) (a / 2) (half_pos ha)] with n hn
    have hi : θ n ≤ a / 2 := ciSup_le fun x => by
      have hx := hn x
      rw [Real.dist_eq, abs_sub_comm] at hx
      exact hx.le
    linarith
  have hrootθ : ∀ n, ∀ᵐ x ∂haar 1, |(τ n).sqrt x - 1| ≤ θ n := fun n =>
    (hae n).mono fun x hx => by rw [hx]; exact hθb n x
  have hV0 : USmall (fun n t => v n (pt t) - 1) := USmall.of_abs_le hθ fun n t => hθb n (pt t)
  have hvB : ∀ᶠ n in atTop, ∀ x, |v n x| ≤ 2 := by
    filter_upwards [hθ.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn x
    have hi := abs_add_le (v n x - 1) 1
    rw [sub_add_cancel, abs_one] at hi
    linarith [hθb n x]
  obtain ⟨δR, hδR, hupper⟩ := polynomial_scalarRate_eventual_upper 1 (by norm_num)
  have hr : ∀ᶠ n in atTop, |r n| ≤ a0 + 1 := by
    have ht : Tendsto (fun n => |hs n|) atTop (𝓝 0) := by simpa using hhs.abs
    filter_upwards [ht.eventually (gt_mem_nhds hδR)] with n hn
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal (by unfold a0; positivity) (hupper (hs n) hn (bs n))
  obtain ⟨hXi, _, hLambda⟩ := polynomial_varying_euler_corrections_small hs hhs τ θ hθ hrootθ r (a0 + 1) hr
  obtain ⟨εq, hεq, hdata⟩ := polynomial_uniform_data_at_origin
  have hlogB (n : ℕ) (x : Torus 1) : |Real.log ((M n).q x)| ≤ εq (hs n) := by
    have he := hdata (hs n) x
    nlinarith [abs_nonneg ((M n).φ x - (polynomialRankOne 0).φ x),
      abs_nonneg ((M n).Aq x - (polynomialRankOne 0).Aq x), abs_nonneg ((M n).dlogq x),
      abs_nonneg ((M n).dφ x - (polynomialRankOne 0).dφ x)]
  have hσB (n : ℕ) (x : Torus 1) : |(M n).dlogq x| ≤ εq (hs n) := by
    have he := hdata (hs n) x
    nlinarith [abs_nonneg ((M n).φ x - (polynomialRankOne 0).φ x),
      abs_nonneg ((M n).Aq x - (polynomialRankOne 0).Aq x), abs_nonneg (Real.log ((M n).q x)),
      abs_nonneg ((M n).dφ x - (polynomialRankOne 0).dφ x)]
  have hσ0 : USmall (fun n t => (M n).dlogq (pt t)) :=
    USmall.of_abs_le (hεq.comp hhs) (fun n t => hσB n (pt t))
  have hlog0 : USmall (fun n t => Real.log ((M n).q (pt t))) :=
    USmall.of_abs_le (hεq.comp hhs) (fun n t => hlogB n (pt t))
  have hvb : ∀ᶠ n in atTop, ∀ t : ℝ, |v n (pt t)| ≤ 2 := hvB.mono fun n hn t => hn (pt t)
  have hlogsq : USmall (fun n t => Real.log (v n (pt t) ^ 2)) := by
    refine hV0.of_le 4 ?_
    filter_upwards [hV0 (1 / 2) (by norm_num)] with n hn t
    exact abs_log_sq_le (hn t)
  have hForce : USmall (fun n t => v n (pt t) *
      (Real.log (v n (pt t) ^ 2) - Real.log ((M n).q (pt t)))) := by
    exact USmall.congr (fun n t => by ring) ((hlogsq.sub hlog0).mul_bdd 2 hvb)
  let β := fun n x => v n x * polynomialEulerCorrection (hs n) (r n) (τ n) x / 2 -
    r n * (v n x * (Real.log (v n x ^ 2) - Real.log ((M n).q x))) -
      polynomialEulerMultiplier (hs n) (r n) (τ n) * v n x / 2
  have hβ : USmall (fun n t => β n (pt t)) := by
    have hrb : ∀ᶠ n in atTop, ∀ _ : ℝ, |r n| ≤ a0 + 1 := hr.mono fun n hn _ => hn
    have he := (((hXi.mul_bdd 2 hvb).const_mul (1 / 2)).sub
      (hForce.mul_bdd (a0 + 1) hrb)).sub ((hLambda.mul_bdd 2 hvb).const_mul (1 / 2))
    exact USmall.congr (fun n t => by dsimp only [β]; ring) he
  have hraw (n : ℕ) : (fun x => 2 * weakGradient (τ n).sqrt (τ n).sqrt_mem x 0 -
      v n x * (M n).dlogq x) =ᵐ[haar 1] S n := by
    filter_upwards [hgrad (φ n)] with x hx
    have he := congrArg (fun z : Tangent 1 => z 0) hx
    simp only [vec1_apply] at he
    change 2 * weakGradient (τ n).sqrt (τ n).sqrt_mem x 0 - v n x * (M n).dlogq x = S n x
    change weakGradient (τ n).sqrt (τ n).sqrt_mem x 0 = (S n x + v n x * (M n).dlogq x) / 2 at he
    linarith
  have hScore : USmall (fun n t => S n (pt t)) := by
    intro e he
    let L := min 1 (e / 16)
    have hL : 0 < L := lt_min one_pos (by positivity)
    filter_upwards [hvB, hσ0 L hL, hβ (e / 4) (by positivity)] with n hvn hσn hβn t
    have hσx : ∀ x : Torus 1, |(M n).dlogq x| ≤ L := by
      intro x
      obtain ⟨s, rfl⟩ := ex010_exists_pt x
      exact hσn s
    have hβx : ∀ x : Torus 1, |β n x| ≤ e / 4 := by
      intro x
      obtain ⟨s, rfl⟩ := ex010_exists_pt x
      exact hβn s
    have hbnd := score_bound (hs n) (bs n) (τ n) (hG (φ n)) (hmin (φ n))
      (v n) (S n) (hv n) (hS n) (hae n) (hraw n) 2 L (e / 4)
      (by norm_num) hL.le (min_le_left _ _) (by positivity) hvn hσx hβx (pt t)
    have hLe : L ≤ e / 16 := min_le_right _ _
    linarith
  refine ⟨φ, v, S, θ, hφ, hθ, fun n => ?_, hθb, hScore⟩
  exact ⟨hv n, hS n, hae n, hVd (φ n), hWd (φ n)⟩

end DGPS.Examples.PolynomialSpecies
