import DGPS.Examples.ThreeSpeciesCircle.InteractingScoreMetricControl
import DGPS.Examples.ThreeSpeciesCircle.InteractingFeedbackBounds
import DGPS.Examples.ThreeSpeciesCircle.InteractingLogNonlinearityControl

/-! Quantitative comparison of the actual physical score right-hand sides.
The constants precede the competitor, coupling and bounded rate. All fields
are continuous representatives; their relation to the original weak gradients
is only an AE equality, and all integrals below are genuine finite integrals. -/

noncomputable section
open MeasureTheory Filter Topology Set

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem score_rhs_five_sq (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d), sq_nonneg (a-e),
    sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (b-e), sq_nonneg (c-d),
    sq_nonneg (c-e), sq_nonneg (d-e)]

/-- Actual RHS comparison on any fixed positive interval. No Euler equation,
minimizer, smoothness, convergence, or desired RHS bound is assumed. In an
application the two AE score representatives are supplied by their genuine
weak-gradient constructions. -/
theorem ordinaryRoot_scoreRhs_integral_bound (h a R m M : ℝ)
    (hR : 0 ≤ R) (hm : 0 < m) (hmM : m ≤ M) (σ : AbsoluteDensity 1)
    {u : Torus 1 → ℝ} (hu : Continuous u) (hσu : σ.sqrt =ᵐ[haar 1] u)
    (hub : ∀ x, u x ∈ Icc m M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ρ : AbsoluteDensity 1) (v S S0 : Torus 1 → ℝ),
      Continuous v → Continuous S → Continuous S0 →
      ρ.sqrt =ᵐ[haar 1] v → (∀ x, v x ∈ Icc m M) →
      S =ᵐ[haar 1] (fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * sigT h x) →
      S0 =ᵐ[haar 1] (fun x => 2 * weakGradient σ.sqrt σ.sqrt_mem x 0 - u x * sigT h x) →
      ∀ r : ℝ, |r| ≤ R → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      (∫ x, ((-(S x * sigT h x) / 2 +
          v x * elementaryEulerCorrection h ε r ρ x / 2 -
          r * interactingLogNonlinearity h x (v x) -
          elementaryEulerMultiplier h ε r ρ * v x / 2) -
        (-(S0 x * sigT h x) / 2 - a * interactingLogNonlinearity h x (u x))) ^ 2
        ∂haar 1) ≤
          K * (ordinaryRootH1Deviation σ ρ u ^ 2 + (r-a) ^ 2 + ε ^ 2) := by
  obtain ⟨F, hF, hfeedback⟩ := elementaryEulerCorrection_uniform_bound h R hR
  obtain ⟨L, hL, hLip, _⟩ := interactingLogNonlinearity_uniform_control h m M hm hmM
  let T := 6 * Real.pi * |h|
  let B := 8 + 2 * T ^ 2
  let Ru := fun x => interactingLogNonlinearity h x (u x)
  have hRu : Continuous Ru := hu.mul
    (((hu.pow 2).log (fun x => pow_ne_zero 2 (hm.trans_le (hub x).1).ne')).sub
      (isSmoothPeriodic_ellT h).continuous_torus)
  let Z := ∫ x, Ru x ^ 2 ∂haar 1
  have hZ : 0 ≤ Z := integral_nonneg fun _ => sq_nonneg _
  let K := 1 + 5 * (T ^ 2 * B + R ^ 2 * L ^ 2 + Z + 2 * F ^ 2)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro ρ v S S0 hv hS hS0 hρv hvb hSe hS0e r hr ε hε he
  obtain ⟨hXi, hlam⟩ := hfeedback ρ r hr ε hε he
  let Rv := fun x => interactingLogNonlinearity h x (v x)
  let Xi := elementaryEulerCorrection h ε r ρ
  let lam := elementaryEulerMultiplier h ε r ρ
  let D := ordinaryRootH1Deviation σ ρ u
  have hRv : Continuous Rv := hv.mul
    (((hv.pow 2).log (fun x => pow_ne_zero 2 (hm.trans_le (hvb x).1).ne')).sub
      (isSmoothPeriodic_ellT h).continuous_torus)
  have hXic : Continuous Xi := (isSmooth_elementaryEulerCorrection h ε r ρ).continuous_torus
  have iS : Integrable (fun x => (S x-S0 x)^2) (haar 1) :=
    ((hS.sub hS0).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have iv : Integrable (fun x => v x^2) (haar 1) :=
    (hv.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have idv : Integrable (fun x => (v x-u x)^2) (haar 1) :=
    ((hv.sub hu).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have iRu : Integrable (fun x => Ru x^2) (haar 1) :=
    (hRu.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hscore : (∫ x, (S x-S0 x)^2 ∂haar 1) ≤ B * D^2 := by
    calc
      _ = ∫ x, ((2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * sigT h x) -
          (2 * weakGradient σ.sqrt σ.sqrt_mem x 0 - u x * sigT h x))^2 ∂haar 1 := by
        apply integral_congr_ae
        filter_upwards [hSe, hS0e] with x hx hy
        rw [hx, hy]
      _ ≤ _ := ordinaryRoot_scoreDifference_integral_bound h σ ρ hu hv hσu hρv
  have hdist : (∫ x, (v x-u x)^2 ∂haar 1) ≤ D^2 := by
    calc
      _ ≤ ∫ _ : Torus 1, D^2 ∂haar 1 := by
        apply integral_mono idv (integrable_const _)
        intro x
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (by
            dsimp only [D, ordinaryRootH1Deviation]; positivity)).2
              (ordinaryRoot_continuous_deviation_bound σ ρ hu hv hσu hρv x)
      _ = _ := by simp
  have hmass : (∫ x, v x^2 ∂haar 1) = 1 := by
    calc
      _ = ∫ x, ρ.sqrt x^2 ∂haar 1 := integral_congr_ae (hρv.mono fun x hx => by change v x^2 = ρ.sqrt x^2; rw [hx])
      _ = 1 := ρ.mass_one
  let f := fun x => (-(S x * sigT h x) / 2 + v x * Xi x / 2 - r * Rv x - lam * v x / 2) -
    (-(S0 x * sigT h x) / 2 - a * Ru x)
  have hfcont : Continuous f := by
    dsimp only [f]
    exact (((((hS.mul (continuous_sigT h)).neg.div_const 2).add
      ((hv.mul hXic).div_const 2)).sub (continuous_const.mul hRv)).sub
      ((continuous_const.mul hv).div_const 2)).sub
        (((hS0.mul (continuous_sigT h)).neg.div_const 2).sub
          (continuous_const.mul hRu))
  have ifin : Integrable (fun x => f x^2) (haar 1) :=
    (hfcont.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let q := fun x => T^2*(S x-S0 x)^2 + F^2*ε^2*v x^2 +
    R^2*L^2*(v x-u x)^2 + (r-a)^2*Ru x^2 + F^2*ε^2*v x^2
  have iq : Integrable q (haar 1) :=
    ((((iS.const_mul (T^2)).add (iv.const_mul (F^2*ε^2))).add
      (idv.const_mul (R^2*L^2))).add (iRu.const_mul ((r-a)^2))).add
        (iv.const_mul (F^2*ε^2))
  have hp (x : Torus 1) : f x^2 ≤ 5*q x := by
    have hs : (sigT h x)^2 ≤ T^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2
        (abs_sigT_le h x)
    have hx : Xi x^2 ≤ F^2*ε^2 := by
      simpa only [sq_abs, mul_pow] using
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hF.le hε)).2 (hXi x)
    have hl : lam^2 ≤ F^2*ε^2 := by
      simpa only [sq_abs, mul_pow] using
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hF.le hε)).2 hlam
    have hr2 : r^2 ≤ R^2 := by simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) hR).2 hr
    have hlog : (Rv x-Ru x)^2 ≤ L^2*(v x-u x)^2 := by
      simpa only [sq_abs, mul_pow] using
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hL.le (abs_nonneg _))).2
          (hLip x (v x) (u x) (hvb x) (hub x))
    have h0 : (-(sigT h x*(S x-S0 x))/2)^2 ≤ T^2*(S x-S0 x)^2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hs (sq_nonneg (S x-S0 x)),
        sq_nonneg (sigT h x*(S x-S0 x))]
    have h1 : (v x*Xi x/2)^2 ≤ F^2*ε^2*v x^2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hx (sq_nonneg (v x)), sq_nonneg (v x*Xi x)]
    have h2 : (-r*(Rv x-Ru x))^2 ≤ R^2*L^2*(v x-u x)^2 := by
      have ht := mul_le_mul hr2 hlog (sq_nonneg _) (sq_nonneg R)
      nlinarith only [ht]
    have h4 : (-lam*v x/2)^2 ≤ F^2*ε^2*v x^2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hl (sq_nonneg (v x)), sq_nonneg (lam*v x)]
    have hf : f x = -(sigT h x*(S x-S0 x))/2 + v x*Xi x/2 +
        -r*(Rv x-Ru x) + -(r-a)*Ru x + -lam*v x/2 := by dsimp only [f]; ring
    rw [hf]
    have hh := score_rhs_five_sq (-(sigT h x*(S x-S0 x))/2) (v x*Xi x/2)
      (-r*(Rv x-Ru x)) (-(r-a)*Ru x) (-lam*v x/2)
    have h3 : (-(r-a)*Ru x)^2 ≤ (r-a)^2*Ru x^2 := by
      simp only [mul_pow, neg_sq]; exact le_rfl
    exact hh.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) h4)
      (by norm_num))
  have hint := integral_mono ifin (iq.const_mul 5) hp
  have hiq : (∫ x, q x ∂haar 1) =
      T^2*(∫ x, (S x-S0 x)^2 ∂haar 1) + F^2*ε^2 +
        R^2*L^2*(∫ x, (v x-u x)^2 ∂haar 1) + (r-a)^2*Z + F^2*ε^2 := by
    dsimp only [q]
    have ha := integral_add
      ((((iS.const_mul (T^2)).add (iv.const_mul (F^2*ε^2))).add
        (idv.const_mul (R^2*L^2))).add (iRu.const_mul ((r-a)^2)))
      (iv.const_mul (F^2*ε^2))
    have hb := integral_add (((iS.const_mul (T^2)).add (iv.const_mul (F^2*ε^2))).add
        (idv.const_mul (R^2*L^2))) (iRu.const_mul ((r-a)^2))
    have hc := integral_add ((iS.const_mul (T^2)).add (iv.const_mul (F^2*ε^2)))
        (idv.const_mul (R^2*L^2))
    have he := integral_add (iS.const_mul (T^2)) (iv.const_mul (F^2*ε^2))
    simp only [Pi.add_apply] at ha hb hc he
    rw [ha, hb, hc, he]
    simp only [integral_const_mul, hmass, mul_one, Z]
  rw [integral_const_mul, hiq] at hint
  have hs := mul_le_mul_of_nonneg_left hscore (sq_nonneg T)
  have hd := mul_le_mul_of_nonneg_left hdist (mul_nonneg (sq_nonneg R) (sq_nonneg L))
  change (∫ x, f x^2 ∂haar 1) ≤ K*(D^2+(r-a)^2+ε^2)
  have hcoef : 0 ≤ T^2*B + R^2*L^2 + Z + 2*F^2 := by positivity
  have hrem : 0 ≤ (T^2*B + R^2*L^2 + Z + 2*F^2)*(D^2+(r-a)^2+ε^2) -
      (T^2*B*D^2 + R^2*L^2*D^2 + Z*(r-a)^2 + 2*F^2*ε^2) := by
    have hD0 := sq_nonneg D
    have hr0 := sq_nonneg (r-a)
    have he0 := sq_nonneg ε
    nlinarith only [mul_nonneg (by positivity : 0 ≤ T^2*B) hr0,
      mul_nonneg (by positivity : 0 ≤ T^2*B) he0,
      mul_nonneg (by positivity : 0 ≤ R^2*L^2) hr0,
      mul_nonneg (by positivity : 0 ≤ R^2*L^2) he0,
      mul_nonneg hZ hD0, mul_nonneg hZ he0,
      mul_nonneg (sq_nonneg F) hD0, mul_nonneg (sq_nonneg F) hr0]
  dsimp only [K]
  nlinarith only [hint, hs, hd, hrem, sq_nonneg D, sq_nonneg (r-a), sq_nonneg ε]

end DGPS.Examples.ThreeSpeciesCircle
