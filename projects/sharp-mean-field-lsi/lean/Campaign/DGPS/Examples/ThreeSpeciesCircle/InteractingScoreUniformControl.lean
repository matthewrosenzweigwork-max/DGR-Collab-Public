import DGPS.Examples.ThreeSpeciesCircle.InteractingScoreRhsControl

/-! Genuine uniform score convergence from the actual physical weak score
systems and original-H1 root convergence. The RHS convergence is proved here
from the actual field estimates, rather than supplied as a premise. -/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Physical right-hand side, with all feedbacks computed from the actual law. -/
def elementaryPhysicalScoreRhs (h ε r : ℝ) (ρ : AbsoluteDensity 1)
    (v S : Torus 1 → ℝ) : Torus 1 → ℝ := fun x =>
  -(S x*sigT h x)/2 + v x*elementaryEulerCorrection h ε r ρ x/2 -
    r*interactingLogNonlinearity h x (v x) - elementaryEulerMultiplier h ε r ρ*v x/2

/-- At a fixed ordinary root, original-H1 convergence, rate convergence and
vanishing coupling imply uniform convergence of the genuine continuous score
representatives. The actual weak equations are factual inputs; no score/RHS
convergence, uniform score bound, or higher norm convergence is assumed. -/
theorem ordinaryRoot_score_tendstoUniformly (h a R m M : ℝ)
    (hR : 0 ≤ R) (hm : 0 < m) (hmM : m ≤ M) (σ : AbsoluteDensity 1)
    (ρ : ℕ → AbsoluteDensity 1) {u S0 : Torus 1 → ℝ}
    {v S : ℕ → Torus 1 → ℝ} {r ε : ℕ → ℝ}
    (hu : Continuous u) (hS0 : Continuous S0)
    (hv : ∀ n, Continuous (v n)) (hS : ∀ n, Continuous (S n))
    (hσu : σ.sqrt =ᵐ[haar 1] u) (hρv : ∀ n, (ρ n).sqrt =ᵐ[haar 1] v n)
    (hub : ∀ x, u x ∈ Icc m M) (hvb : ∀ n x, v n x ∈ Icc m M)
    (hS0e : S0 =ᵐ[haar 1] (fun x => 2*weakGradient σ.sqrt σ.sqrt_mem x 0-u x*sigT h x))
    (hSe : ∀ n, S n =ᵐ[haar 1]
      (fun x => 2*weakGradient (ρ n).sqrt (ρ n).sqrt_mem x 0-v n x*sigT h x))
    (hS0w : IsWeakGradient S0 (vec1 fun x =>
      -(S0 x*sigT h x)/2-a*interactingLogNonlinearity h x (u x)))
    (hSw : ∀ n, IsWeakGradient (S n)
      (vec1 (elementaryPhysicalScoreRhs h (ε n) (r n) (ρ n) (v n) (S n))))
    (hrb : ∀ n, |r n| ≤ R) (hεb : ∀ n, 0 ≤ ε n ∧ ε n ≤ 1)
    (hd : Tendsto (fun n => ordinaryRootH1Deviation σ (ρ n) u) atTop (𝓝 0))
    (hr : Tendsto r atTop (𝓝 a)) (hε : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformly S S0 atTop := by
  let g0 := fun x => -(S0 x*sigT h x)/2-a*interactingLogNonlinearity h x (u x)
  let g := fun n => elementaryPhysicalScoreRhs h (ε n) (r n) (ρ n) (v n) (S n)
  have hsint : Tendsto (fun n => ∫ x, (S n x-S0 x)^2 ∂haar 1) atTop (𝓝 0) := by
    have hbound (n : ℕ) : (∫ x, (S n x-S0 x)^2 ∂haar 1) ≤
        (8+2*(6*Real.pi*|h|)^2)*ordinaryRootH1Deviation σ (ρ n) u^2 := by
      calc
        _ = ∫ x, ((2*weakGradient (ρ n).sqrt (ρ n).sqrt_mem x 0-v n x*sigT h x)-
            (2*weakGradient σ.sqrt σ.sqrt_mem x 0-u x*sigT h x))^2 ∂haar 1 := by
          apply integral_congr_ae
          filter_upwards [hSe n, hS0e] with x hx hy
          rw [hx, hy]
        _ ≤ _ := ordinaryRoot_scoreDifference_integral_bound h σ (ρ n) hu (hv n) hσu (hρv n)
    apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) hbound
    simpa using (hd.pow 2).const_mul (8+2*(6*Real.pi*|h|)^2)
  have hgint : Tendsto (fun n => ∫ x, (g n x-g0 x)^2 ∂haar 1) atTop (𝓝 0) := by
    obtain ⟨K, hK, hbound⟩ := ordinaryRoot_scoreRhs_integral_bound h a R m M hR hm hmM σ hu hσu hub
    have hb (n : ℕ) : (∫ x, (g n x-g0 x)^2 ∂haar 1) ≤
        K*(ordinaryRootH1Deviation σ (ρ n) u^2+(r n-a)^2+(ε n)^2) :=
      hbound (ρ n) (v n) (S n) S0 (hv n) (hS n) hS0 (hρv n) (hvb n)
        (hSe n) hS0e (r n) (hrb n) (ε n) (hεb n).1 (hεb n).2
    apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) hb
    have hd2 := hd.pow 2
    have hr2 := (hr.sub_const a).pow 2
    have he2 := hε.pow 2
    simpa using ((hd2.add hr2).add he2).const_mul K
  have hsLp : Tendsto (fun n => eLpNorm (fun x => S n x-S0 x) 2 (haar 1)) atTop (𝓝 0) := by
    have hmS (n : ℕ) : MemLp (fun x => S n x-S0 x) 2 (haar 1) := by
      exact (memLp_congr_ae (show (fun x => S n x-S0 x) =ᵐ[haar 1] S n-S0 from
        Filter.Eventually.of_forall fun x => rfl)).mpr ((hSw n).memLp.sub hS0w.memLp)
    refine tendsto_eLpNorm_of_toReal (fun n => (hmS n).eLpNorm_ne_top) ?_
    have heq (n : ℕ) := toReal_eLpNorm_two (hmS n)
    simp_rw [heq]
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hsint
  have hgLp : Tendsto (fun n => eLpNorm (fun x => g n x-g0 x) 2 (haar 1)) atTop (𝓝 0) := by
    have hmG (n : ℕ) : MemLp (fun x => g n x-g0 x) 2 (haar 1) := by
      have hz := (memLp_coord (hSw n).memLp_grad 0).sub (memLp_coord hS0w.memLp_grad 0)
      apply (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).mpr hz
      simp only [Pi.sub_apply, vec1_apply, g, g0]
    refine tendsto_eLpNorm_of_toReal (fun n => (hmG n).eLpNorm_ne_top) ?_
    have heq (n : ℕ) := toReal_eLpNorm_two (hmG n)
    simp_rw [heq]
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hgint
  exact circle_tendstoUniformly_of_coord hSw hS0w hS
    (fun _ => ae_eq_refl _) hS0 (ae_eq_refl _) hsLp
    (by simpa only [vec1_apply] using hgLp)

end DGPS.Examples.ThreeSpeciesCircle
