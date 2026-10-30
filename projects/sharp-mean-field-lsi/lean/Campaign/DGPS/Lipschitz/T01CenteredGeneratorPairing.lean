import DGPS.Lipschitz.T01CenteredGeneratorLimit
import DGPS.Lipschitz.T01CenteredForceGenerator
import DGPS.Lipschitz.T01CenteredGeneratorErrorBound
import DGPS.Lipschitz.T01MobilityWeightedError
import DGPS.Lipschitz.T01FluctuationFourthMoment

/-!
# Actual bounded-particle centered generator pairings

The finite-rank approximation is taken after the particle limit. All three errors are
controlled on the same actual reference and spectral witness. The joint-law premise is
bounded-continuous convergence, and the force premise is the proved residual energy threshold.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

namespace DGPS.Lipschitz
open DGPS.Particle KernelApproximation SharpLSI SharpLSI.FL

private theorem pairing_tendsto_of_approx {x : ℕ → ℝ} {u : ℕ → ℕ → ℝ}
    {αR : ℕ → ℝ} {α : ℝ}
    (hu : ∀ R, Tendsto (u R) atTop (𝓝 (αR R)))
    (hα : Tendsto αR atTop (𝓝 α))
    (herr : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R ≥ R₀,
      ∀ᶠ k in atTop, |x k - u R k| ≤ ε) : Tendsto x atTop (𝓝 α) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h3 : 0 < ε / 3 := by positivity
  obtain ⟨R₀, hR₀⟩ := herr (ε / 3) h3
  obtain ⟨R, hR, hαR⟩ := ((eventually_ge_atTop R₀).and
    (Metric.tendsto_nhds.1 hα (ε / 3) h3)).exists
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((hR₀ R hR).and
    (Metric.tendsto_nhds.1 (hu R) (ε / 3) h3))
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨he, huR⟩ := hK k hk
  rw [Real.dist_eq] at hαR huR ⊢
  calc |x k - α| = |(x k - u R k) + (u R k - αR R) + (αR R - α)| := by congr 1; ring
    _ ≤ |x k - u R k| + |u R k - αR R| + |αR R - α| := abs_add_three _ _ _
    _ < ε := by linarith

private theorem finite_force_threshold {n : ℕ} (v : Fin n → ℕ → ℕ → ℝ)
    (hv : ∀ i ε, 0 < ε → ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ᶠ k in atTop, v i R k ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ᶠ k in atTop, ∑ i, v i R k ≤ ε := by
  intro ε hε
  have he : 0 < ε / ((n : ℝ) + 1) := by positivity
  choose R₀ hR₀ using fun i => hv i (ε / ((n : ℝ) + 1)) he
  refine ⟨Finset.univ.sup R₀, fun R hR => ?_⟩
  have hev : ∀ i, ∀ᶠ k in atTop, v i R k ≤ ε / ((n : ℝ) + 1) := fun i =>
    hR₀ i R ((Finset.le_sup (f := R₀) (Finset.mem_univ i)).trans hR)
  filter_upwards [Filter.eventually_all.2 hev] with k hk
  calc ∑ i, v i R k ≤ ∑ _i : Fin n, ε / ((n : ℝ) + 1) :=
      Finset.sum_le_sum fun i hi => hk i
    _ = (n : ℝ) * (ε / ((n : ℝ) + 1)) := by simp
    _ ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (show (0 : ℝ) < (n : ℝ) + 1 by positivity)]
      nlinarith

private theorem bounded_four {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (H : Ω → ℝ) (hm : AEStronglyMeasurable H P)
    {K : ℝ} (hb : ∀ x, |H x| ≤ K) : MemLp H 4 P ∧ ∫ x, H x ^ 4 ∂P ≤ K ^ 4 := by
  refine ⟨MemLp.of_bound hm K (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x), ?_⟩
  calc ∫ x, H x ^ 4 ∂P ≤ ∫ _x, K ^ 4 ∂P :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
        (integrable_const _) (Eventually.of_forall fun x => by
          simpa only [Even.pow_abs (by decide : Even (4 : ℕ))] using
            pow_le_pow_left₀ (abs_nonneg (H x)) (hb x) 4)
    _ = K ^ 4 := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual bounded particle cylinder-generator pairings converge on the retained spectral witness.
The residual-force premise is the genuine upstream force-energy threshold, not a pairing limit. -/
theorem t01_centered_generator_pairing_tendsto {d : ℕ}
    (A : InteractionData d) (S : Spec d) (aux : Aux S) (D : KData d)
    (hD : D.K = centeredKernel A S.mu)
    (hfix : (frozenGibbs A (specProbability_LIP016 S)).measure = S.mu)
    (he : IsRefEigenbasis S.mu S.v S.lam)
    (hφ : ∀ j, ContDiff ℝ 1 (S.v j ∘ liftT))
    (hH : IsCoerciveDensityHessian A (specProbability_LIP016 S))
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht : ∀ R, 0 ≤ t R)
    (htlim : Tendsto t atTop (𝓝 0)) (hm : StrictMono m)
    (F : FiniteRankApprox A.W S.mu S.v)
    (ha : ∀ R i j, F.a R i j = positiveKernelCoefficient S D (t R) (m R) i j)
    {p Cρ : ℝ} (hp : 1 < p) (hCρ : 0 ≤ Cρ)
    (hρ : ∀ N : ℕ+, ∫ X, centeredParticleDensity A (specProbability_LIP016 S) N X ^ p
      ∂Measure.pi (fun _ : Fin N => S.mu) ≤ Cρ)
    (gU : (N : ℕ+) → ParticleSpace d N → Fin N → Tangent d)
    (hU : ∀ N, IsParticleHaarWeakGradient N
      (centeredParticlePotential A (specProbability_LIP016 S) N) (gU N))
    (hForce : ∀ η : ℝ, 0 < η → ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ᶠ N : ℕ+ in atTop,
      (∫⁻ X, ENNReal.ofReal (gradSqC (fun Y =>
        centeredParticlePotential A (specProbability_LIP016 S) N Y - URN F R N Y) X)
        ∂particleLaw A N) ≤ ENNReal.ofReal η)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ (t01CovarianceMatrix S A))
    {Y : ℕ → (ℕ → ℝ) → ℝ}
    (hY : ∀ i, IsRowVariable (Tmat A.W S.mu S.v) γ i (Y i))
    {fInf : (ℕ → ℝ) → ℝ} (hfInf : MemLp fInf 2 γ)
    (Ns : ℕ → ℕ+) (hNs : Tendsto (fun k => (Ns k : ℕ)) atTop atTop)
    (f : (k : ℕ) → ParticleSpace d (Ns k) → ℝ)
    (hfm : ∀ k, AEStronglyMeasurable (f k) (particleLaw A (Ns k)))
    {B : ℝ} (hB : 0 ≤ B) (hfb : ∀ k X, |f k X| ≤ B)
    (hlaw : ∀ J (g : ℝ × (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun k => ∫ X, g (f k X, fun i => fluct S.v (Ns k) i X)
        ∂particleLaw A (Ns k)) atTop (𝓝 (∫ z, g (fInf z, fun i => z i) ∂γ)))
    (c : Cyl)
    (hDrift : ∀ N (i : Fin c.J), BddMeas (fun X =>
      dualD N (fun j : Fin c.J => S.v (j.val + 1)) (gU N) i X)) :
    Tendsto (fun k => ∫ X, f k X * dualGen (Ns k)
      (fun i : Fin c.J => S.lam (i.val + 1)) (fun i : Fin c.J => S.v (i.val + 1))
        c.φ (gU (Ns k)) X ∂particleLaw A (Ns k)) atTop
      (𝓝 (∫ z, fInf z * (-(c.gen (lamShift S.lam) Y z)) ∂γ)) := by
  classical
  let μ := specProbability_LIP016 S
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hac : S.mu ≪ haar d := Analysis.CompactResolvent.wMeasure_ac_haar
  have heC : ∀ j, S.v j =ᵐ[haar d] S.v j := fun _ => EventuallyEq.rfl
  have hfL : ∀ k, MemLp (f k) 2 (particleLaw A (Ns k)) := fun k =>
    MemLp.of_bound (hfm k) B (Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hfb k X)
  have hfsq : ∀ k X, f k X ^ 2 ≤ B ^ 2 := fun k X => by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f k X)) (hfb k X) 2
  have hf2 : ∀ k, ∫ X, f k X ^ 2 ∂particleLaw A (Ns k) ≤ B ^ 2 := fun k => by
    calc ∫ X, f k X ^ 2 ∂particleLaw A (Ns k) ≤ ∫ _X, B ^ 2 ∂particleLaw A (Ns k) :=
        integral_mono_of_nonneg (Eventually.of_forall fun X => sq_nonneg _)
          (integrable_const _) (Eventually.of_forall (hfsq k))
      _ = B ^ 2 := by simp
  have hfour := fun q => t01_particleLaw_fluct_fourth_moment A μ hfix hac he hφ heC hp hCρ hρ q
  choose K4 hK40 hK4 using hfour
  have hZ4 : ∀ J, ∃ K : ℝ, ∀ k (i : Fin J),
      Integrable (fun X => fluct S.v (Ns k) i X ^ 4) (particleLaw A (Ns k)) ∧
        ∫ X, fluct S.v (Ns k) i X ^ 4 ∂particleLaw A (Ns k) ≤ K := by
    intro J
    refine ⟨∑ i : Fin J, K4 i, fun k i => ⟨(hK4 i (Ns k)).1, (hK4 i (Ns k)).2.trans ?_⟩⟩
    exact Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin J => K4 j)
      (fun j _ => hK40 j) (Finset.mem_univ i)
  let J' : ℕ → ℕ := fun R => max c.J ((F.s R).sup id + 1)
  have hJ : ∀ R, c.J ≤ J' R := fun R => le_max_left _ _
  have hsJ : ∀ R q, q ∈ F.s R → q < J' R := fun R q hq =>
    (Nat.lt_succ_of_le (Finset.le_sup (f := id) hq)).trans_le (le_max_right _ _)
  let u (R k : ℕ) : ℝ := ∫ X, f k X * crossH S.lam c (F.s R) (F.a R) (hJ R)
    (fun i : Fin (J' R) => fluct S.v (Ns k) i X) ∂particleLaw A (Ns k)
  let αR (R : ℕ) : ℝ := ∫ z, fInf z * crossH S.lam c (F.s R) (F.a R) (hJ R)
    (fun i : Fin (J' R) => z i) ∂γ
  have hu : ∀ R, Tendsto (u R) atTop (𝓝 (αR R)) := fun R =>
    t01_bounded_crossH_pairing_limit A S.v (fun j => (S.vc j).measurable) Ns f hfm hB hfb
      hγ hfInf hlaw hZ4 S.lam c (F.s R) (F.a R) (hJ R)
  obtain ⟨σ, hσ, hσH⟩ := hH
  have hα := t01_actual_gaussian_crossH_tendsto S aux A D hD hσ hσH t m ht htlim hm F ha
    hγ hY hfInf c hJ hsJ
  have hψK : ∀ i : Fin c.J, ∃ K : ℝ, 0 ≤ K ∧ ∀ w, |cylD c i w| ≤ K := fun i =>
    exists_bound_of_compact (contDiff_cylD c i).continuous (hasCompactSupport_cylD c i)
  choose Kψ hKψ0 hKψ using hψK
  have hDK : ∀ i : Fin c.J, ∃ K : ℝ, 0 ≤ K ∧ ∀ w (j : Fin c.J),
      |fderiv ℝ (cylD c i) w (Pi.single j 1)| ≤ K := fun i =>
    exists_bound_fderiv_of (contDiff_cylD c i) (hasCompactSupport_cylD c i)
  choose KD hKD0 hKD using hDK
  have hmob3 : ∀ i j : Fin c.J, Tendsto (fun k => ∫ X,
      |f k X * fderiv ℝ (cylD c i) (zC S.v (Ns k) c.J X) (Pi.single j 1) *
        (mobA S.v (Ns k) X j i - if j.val = i.val then S.lam (j.val + 1) else 0)|
          ∂particleLaw A (Ns k)) atTop (𝓝 0) := by
    intro i j
    exact t01_mobility_weighted_error A μ hfix hac he hφ heC hp hCρ hρ Ns hNs hfm
      (fun k => ⟨hfL k, hf2 k⟩)
      (fun k => bounded_four (particleLaw A (Ns k)) _
        ((((contDiff_cylD c i).continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable.comp
          (measurable_zC hφ (Ns k) c.J)).aestronglyMeasurable (fun X => hKD i _ j)) j i
  have hmob5 : ∀ (i : Fin c.J) (p q : ℕ), Tendsto (fun k => ∫ X,
      |f k X * (cylD c i (zC S.v (Ns k) c.J X) * fluct S.v (Ns k) q X) *
        (mobA S.v (Ns k) X p i - if p = i.val then S.lam (p + 1) else 0)|
          ∂particleLaw A (Ns k)) atTop (𝓝 0) := by
    intro i p q
    apply t01_mobility_weighted_error A μ hfix hac he hφ heC hp hCρ hρ Ns hNs hfm
      (fun k => ⟨hfL k, hf2 k⟩) (K := Kψ i ^ 4 * K4 q) _ p i
    intro k
    let ψ : ParticleSpace d (Ns k) → ℝ := fun X => cylD c i (zC S.v (Ns k) c.J X)
    let Z : ParticleSpace d (Ns k) → ℝ := fun X => fluct S.v (Ns k) q X
    have hψm : Measurable ψ := (contDiff_cylD c i).continuous.measurable.comp
      (measurable_zC hφ (Ns k) c.J)
    have hZL := t01_particleLaw_fluct_memLp_four A hφ (Ns k) q
    have hHL : MemLp (fun X => ψ X * Z X) 4 (particleLaw A (Ns k)) :=
      hZL.of_le_mul (hψm.aestronglyMeasurable.mul hZL.aestronglyMeasurable)
        (Eventually.of_forall fun X => by
          simp only [norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hKψ i _) (abs_nonneg _))
    refine ⟨hHL, ?_⟩
    calc ∫ X, (ψ X * Z X) ^ 4 ∂particleLaw A (Ns k)
        ≤ ∫ X, Kψ i ^ 4 * Z X ^ 4 ∂particleLaw A (Ns k) :=
          integral_mono_of_nonneg (Eventually.of_forall fun X => by positivity)
            ((hK4 q (Ns k)).1.const_mul _) (Eventually.of_forall fun X => by
              change (ψ X * Z X) ^ 4 ≤ Kψ i ^ 4 * Z X ^ 4
              rw [mul_pow]
              exact mul_le_mul_of_nonneg_right
                (by simpa only [Even.pow_abs (by decide : Even (4 : ℕ))] using
                  pow_le_pow_left₀ (abs_nonneg (ψ X)) (hKψ i _) 4) (by positivity))
      _ ≤ Kψ i ^ 4 * K4 q := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hK4 q (Ns k)).2 (by positivity)
  let E3 (k : ℕ) : ℝ := ∑ i : Fin c.J, ∑ j : Fin c.J, ∫ X,
    |f k X * fderiv ℝ (cylD c i) (zC S.v (Ns k) c.J X) (Pi.single j 1) *
      (mobA S.v (Ns k) X j i - if j.val = i.val then S.lam (j.val + 1) else 0)|
      ∂particleLaw A (Ns k)
  let E4 (i : Fin c.J) (R k : ℕ) : ℝ := ∫ X,
    |f k X * cylD c i (zC S.v (Ns k) c.J X) *
      (dualD (Ns k) (fun j : Fin c.J => S.v (j.val + 1)) (gU (Ns k)) i X -
        ∑ p ∈ F.s R, ∑ q ∈ F.s R,
          F.a R p q * fluct S.v (Ns k) q X * mobA S.v (Ns k) X p i)| ∂particleLaw A (Ns k)
  let E5 (R k : ℕ) : ℝ := ∑ i : Fin c.J, ∑ p ∈ F.s R, ∑ q ∈ F.s R, |F.a R p q| * ∫ X,
    |f k X * (cylD c i (zC S.v (Ns k) c.J X) * fluct S.v (Ns k) q X) *
      (mobA S.v (Ns k) X p i - if p = i.val then S.lam (p + 1) else 0)| ∂particleLaw A (Ns k)
  have hE3 : Tendsto E3 atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
      (fun i hi => tendsto_finsetSum Finset.univ (fun j hj => hmob3 i j))
  have hE5 : ∀ R, Tendsto (E5 R) atTop (𝓝 0) := by
    intro R
    simpa only [mul_zero, Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
      (fun i hi => tendsto_finsetSum (F.s R) (fun p hp => tendsto_finsetSum (F.s R)
        (fun q hq => (hmob5 i p q).const_mul |F.a R p q|)))
  have hE4 : ∀ i : Fin c.J, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ,
      ∀ R ≥ R₀, ∀ᶠ k in atTop, E4 i R k ≤ ε := by
    intro i
    simpa only [E4, dualD] using t01_centered_force_pairing_threshold A μ hfix hφ F gU hU hForce
      hNs f (fun k X => cylD c i (zC S.v (Ns k) c.J X)) hfL hf2 (hKψ0 i)
      (fun k X => hKψ i _) i.val
      (fun R k => by
        simpa only [dualD] using t01_centered_force_pairing_integrable A (Ns k) S.v c
          (F.s R) (F.a R) (gU (Ns k)) hφ (hDrift (Ns k)) (f k) (hfL k) i)
  have hE4sum := finite_force_threshold E4 hE4
  apply pairing_tendsto_of_approx hu hα
  intro ε hε
  have h3 : 0 < ε / 3 := by positivity
  obtain ⟨R₀, hR₀⟩ := hE4sum (ε / 3) h3
  refine ⟨R₀, fun R hR => ?_⟩
  filter_upwards [hR₀ R hR, hE3.eventually (gt_mem_nhds h3),
    (hE5 R).eventually (gt_mem_nhds h3)] with k hk4 hk3 hk5
  have herr := t01_centered_cross_err_le A (Ns k) S.v S.lam c (F.s R) (F.a R)
    (hJ R) (hsJ R) (gU (Ns k)) hφ (hDrift (Ns k)) (f k) (hfL k)
  change _ ≤ E3 k + (∑ i, E4 i R k) + E5 R k at herr
  exact herr.trans (by linarith)

end DGPS.Lipschitz
