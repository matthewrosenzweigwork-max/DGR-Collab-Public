import DGPS.Examples.ThreeSpeciesCircle.InteractingMinimizerPoincareGap
import DGPS.Lipschitz.WeakChainRule
import DGPS.Variational.SpeciesGap
import DGPS.Variational.WeightedScoreInformation

/-! Genuine finite fixed-barycenter splits in the original weighted weak-H1
domain. Continuous representatives are selected using one-dimensional embedding;
they are not smoothness assumptions on the tangent. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A native weighted weak-H1 tangent at a positive continuous absolute law has
a continuous Haar-H1 representative with the SAME chosen weak gradient. -/
theorem nativeTangent_continuous_rep (σ : AbsoluteDensity 1)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hup : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (f : WeakH1Test (densityMeasure σ)) :
    ∃ g : Torus 1 → ℝ, Continuous g ∧ g =ᵐ[haar 1] f.fn ∧
      g =ᵐ[(densityMeasure σ : Measure (Torus 1))] f.fn ∧ IsWeakGradient g f.grad := by
  obtain ⟨P, hPμ, _⟩ := ordinaryRoot_boundedReference σ u hu hup hurep
  have hPprob : (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) =
      densityMeasure σ := ProbabilityMeasure.toMeasure_injective hPμ
  have hw : IsMeasureWeakGradient
      (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) f.fn f.grad := by
    rw [hPprob]
    exact f.isWeak
  have hhaar : IsWeakGradient f.fn f.grad :=
    (isWeightedWeakGradient_iff P).1 ((isMeasureWeakGradient_iff P).1 hw)
  obtain ⟨g, hgc, hgae, _, _⟩ := exists_continuous_rep_one hhaar
  have hac : (densityMeasure σ : Measure (Torus 1)) ≪ haar 1 :=
    withDensity_absolutelyContinuous _ _
  exact ⟨g, hgc, hgae, hac.ae_le hgae,
    hhaar.congr_ae hgae.symm (EventuallyEq.refl _ _)⟩

/-- Representation adapter for EVERY genuine finite native weighted-H1 tangent
family. The a.e. weighted cancellation becomes pointwise only after selecting
continuous representatives; no new condition is imposed on the original tests. -/
theorem nativeTangentFamily_continuous_reps (σ : AbsoluteDensity 1)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hup : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (q : ℕ+) (θ : Fin q → ℝ)
    (f : Fin q → WeakH1Test (densityMeasure σ))
    (hm : ∀ s, ∫ x, (f s).fn x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (hcancel : ∀ᵐ x ∂(densityMeasure σ : Measure (Torus 1)), ∑ s, θ s * (f s).fn x = 0) :
    ∃ g : Fin q → Torus 1 → ℝ,
      (∀ s, Continuous (g s)) ∧ (∀ s, g s =ᵐ[haar 1] (f s).fn) ∧
      (∀ s, g s =ᵐ[(densityMeasure σ : Measure (Torus 1))] (f s).fn) ∧
      (∀ s, IsWeakGradient (g s) (f s).grad) ∧
      (∀ s, ∫ x, g s x ∂(densityMeasure σ : Measure (Torus 1)) = 0) ∧
      (∀ x, ∑ s, θ s * g s x = 0) := by
  choose g hgc hgae hgμ hweak using fun s => nativeTangent_continuous_rep σ u hu hup hurep (f s)
  have hmean (s : Fin q) : ∫ x, g s x ∂(densityMeasure σ : Measure (Torus 1)) = 0 :=
    (integral_congr_ae (hgμ s)).trans (hm s)
  obtain ⟨P, hPμ, _⟩ := ordinaryRoot_boundedReference σ u hu hup hurep
  have hac : haar 1 ≪ (densityMeasure σ : Measure (Torus 1)) := by
    rw [← hPμ]
    exact P.haar_ac_measure
  have hsumAE : (fun x => ∑ s, θ s * g s x) =ᵐ[haar 1] 0 := by
    filter_upwards [hac.ae_le hcancel, ae_all_iff.mpr hgae] with x hx he
    change (∑ s, θ s * g s x) = 0
    simpa only [he] using hx
  have hsumc : Continuous (fun x => ∑ s, θ s * g s x) :=
    continuous_finsetSum _ fun s _ => (hgc s).const_mul (θ s)
  have he := MeasureTheory.Measure.eq_of_ae_eq hsumAE hsumc continuous_const
  exact ⟨g, hgc, hgae, hgμ, hweak, hmean, fun x => congrFun he x⟩

/-- The square root of a positive continuous H1 function has the genuine weak
chain-rule gradient; no differentiability of the spatial function is assumed. -/
theorem continuousH1_sqrt_gradient {f : Torus 1 → ℝ} {G : Torus 1 → Tangent 1}
    (hf : IsWeakGradient f G) (hc : Continuous f) (hp : ∀ x, 0 < f x) :
    IsWeakGradient (fun x => Real.sqrt (f x))
      (fun x => (2 * Real.sqrt (f x))⁻¹ • G x) := by
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  let c := f x0
  have hc0 : 0 < c := hp x0
  have hshift := hf.add (isWeakGradient_const (d := 1) (-c))
  have hn : ∀ᵐ x ∂haar 1, 0 ≤ f x + -c :=
    Eventually.of_forall fun x => by
      have hmin : f x0 ≤ f x := hx0 (Set.mem_univ x)
      dsimp only [c]
      linarith only [hmin]
  have hs := DGPS.Lipschitz.WeakChainRule.isWeakGradient_sqrt_add hc0 hshift hn
  refine hs.congr_ae (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · congr 1
    ring
  · simp only [Pi.add_apply, Pi.zero_apply, add_zero]
    congr 2
    ring

/-- The actual relative density `(1+t*g)*sigma` for an original continuous H1
tangent. Its stored square root retains the original base representative. -/
def relativeH1SplitDensity (σ : AbsoluteDensity 1) (g : Torus 1 → ℝ)
    (G : Torus 1 → Tangent 1) (hg : IsWeakGradient g G) (hgc : Continuous g)
    (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hp : ∀ x, 0 < 1 + t * g x) : AbsoluteDensity 1 where
  sqrt := fun x => Real.sqrt (1 + t * g x) * σ.sqrt x
  sqrt_mem := by
    have hlin := (isWeakGradient_const (d := 1) 1).add (hg.smul t)
    have hroot := continuousH1_sqrt_gradient hlin
      (continuous_const.add (continuous_const.mul hgc)) hp
    exact ⟨_, hroot.mul_one_dim (isWeakGradient_weakGradient σ.sqrt_mem)⟩
  sqrt_nonneg := σ.sqrt_nonneg.mono fun x hx => mul_nonneg (Real.sqrt_nonneg _) hx
  mass_one := by
    have hi : Integrable (fun x => σ.density x * g x) (haar 1) := by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hgc.continuousOn
      exact σ.integrable_density.mul_bdd hgc.aestronglyMeasurable
        (Eventually.of_forall fun x => hC x (Set.mem_univ x))
    have hzero : ∫ x, σ.density x * g x ∂haar 1 = 0 := by
      rw [← Structural.budget_integral_densityMeasure]
      exact hm
    have he : (fun x => (Real.sqrt (1 + t * g x) * σ.sqrt x) ^ 2) =
        fun x => σ.density x + t * (σ.density x * g x) := by
      funext x
      rw [mul_pow, Real.sq_sqrt (hp x).le]
      unfold AbsoluteDensity.density
      ring
    rw [he, integral_add σ.integrable_density (hi.const_mul t), integral_const_mul,
      σ.integral_density, hzero, mul_zero, add_zero]

theorem relativeH1SplitDensity_density (σ : AbsoluteDensity 1) (g : Torus 1 → ℝ)
    (G : Torus 1 → Tangent 1) (hg : IsWeakGradient g G) (hgc : Continuous g)
    (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hp : ∀ x, 0 < 1 + t * g x) (x : Torus 1) :
    (relativeH1SplitDensity σ g G hg hgc hm t hp).density x =
      σ.density x * (1 + t * g x) := by
  change (Real.sqrt (1 + t * g x) * σ.sqrt x) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt (hp x).le]
  unfold AbsoluteDensity.density
  ring

/-- The split of a positive continuous H1 law has a continuous H1 square-root
representative bounded below by a positive number. It need not be smooth. -/
theorem relativeH1SplitDensity_positive_rep (σ : AbsoluteDensity 1)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hup : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (g : Torus 1 → ℝ)
    (G : Torus 1 → Tangent 1) (hg : IsWeakGradient g G) (hgc : Continuous g)
    (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hp : ∀ x, 0 < 1 + t * g x) :
    ∃ v : Torus 1 → ℝ, Continuous v ∧
      (relativeH1SplitDensity σ g G hg hgc hm t hp).sqrt =ᵐ[haar 1] v ∧
      MemH1 v ∧ ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ v x := by
  let v : Torus 1 → ℝ := fun x => Real.sqrt (1 + t * g x) * u x
  have hvc : Continuous v :=
    ((continuous_const.add (continuous_const.mul hgc)).sqrt).mul hu
  have hvp : ∀ x, 0 < v x := fun x => mul_pos (Real.sqrt_pos.2 (hp x)) (hup x)
  have hvrep : (relativeH1SplitDensity σ g G hg hgc hm t hp).sqrt =ᵐ[haar 1] v :=
    hurep.mono fun x hx => by change Real.sqrt _ * σ.sqrt x = Real.sqrt _ * u x; rw [hx]
  have hvm : MemH1 v :=
    mem_H1Haar_congr_ae (relativeH1SplitDensity σ g G hg hgc hm t hp).sqrt_mem hvrep
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hvc.continuousOn
  exact ⟨v, hvc, hvrep, hvm, v x0, hvp x0, fun x => hx0 (Set.mem_univ x)⟩

/-- Every count and every positive normalized weight vector is retained. -/
def finiteH1Split (σ : AbsoluteDensity 1) (q : ℕ+) (θ : Fin q → ℝ)
    (hθ : ∀ s, 0 < θ s) (hθsum : ∑ s, θ s = 1)
    (g : Fin q → Torus 1 → ℝ) (G : Fin q → Torus 1 → Tangent 1)
    (hg : ∀ s, IsWeakGradient (g s) (G s)) (hgc : ∀ s, Continuous (g s))
    (hm : ∀ s, ∫ x, g s x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hp : ∀ s x, 0 < 1 + t * g s x) : SpeciesFamily 1 :=
  SpeciesFamily.ofData q θ hθ hθsum fun s =>
    relativeH1SplitDensity σ (g s) (G s) (hg s) (hgc s) (hm s) t (hp s)

/-- Finite continuous H1 tangent families admit both signs on a common
neighborhood selected after the family, with no weight lower bound. -/
theorem finiteH1Split_eventually_positive (q : ℕ+) (g : Fin q → Torus 1 → ℝ)
    (hc : ∀ s, Continuous (g s)) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ s x, 0 < 1 + t * g s x := by
  have he (s : Fin q) : ∀ᶠ t : ℝ in 𝓝 0, ∀ x, 0 < 1 + t * g s x := by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (hc s).continuousOn
    have ht : Tendsto (fun t : ℝ => |t| * B) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const B
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht x
    have hb : |g s x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x (Set.mem_univ x)
    have hsmall : |t * g s x| < 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_lt ht
    linarith [(abs_lt.mp hsmall).1]
  exact eventually_all.mpr he

/-- Weighted pointwise cancellation gives the true original barycenter density. -/
theorem finiteH1Split_barycenter_density (σ : AbsoluteDensity 1) (q : ℕ+)
    (θ : Fin q → ℝ) (hθ : ∀ s, 0 < θ s) (hθsum : ∑ s, θ s = 1)
    (g : Fin q → Torus 1 → ℝ) (G : Fin q → Torus 1 → Tangent 1)
    (hg : ∀ s, IsWeakGradient (g s) (G s)) (hgc : ∀ s, Continuous (g s))
    (hm : ∀ s, ∫ x, g s x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (hcancel : ∀ x, ∑ s, θ s * g s x = 0)
    (t : ℝ) (hp : ∀ s x, 0 < 1 + t * g s x) (x : Torus 1) :
    (barycenter (finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp)).density x = σ.density x := by
  rw [SpeciesFamily.barycenter_density_eq_sum]
  change (∑ s : Fin q, θ s *
    (relativeH1SplitDensity σ (g s) (G s) (hg s) (hgc s) (hm s) t (hp s)).density x) = _
  simp_rw [relativeH1SplitDensity_density]
  have he (s : Fin q) : θ s * (σ.density x * (1 + t * g s x)) =
      σ.density x * θ s + (σ.density x * t) * (θ s * g s x) := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hθsum, hcancel]
  ring

/-- The barycenter is the actual base probability; chosen null-set root values
are not silently identified. -/
theorem finiteH1Split_barycenter (σ : AbsoluteDensity 1) (q : ℕ+)
    (θ : Fin q → ℝ) (hθ : ∀ s, 0 < θ s) (hθsum : ∑ s, θ s = 1)
    (g : Fin q → Torus 1 → ℝ) (G : Fin q → Torus 1 → Tangent 1)
    (hg : ∀ s, IsWeakGradient (g s) (G s)) (hgc : ∀ s, Continuous (g s))
    (hm : ∀ s, ∫ x, g s x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (hcancel : ∀ x, ∑ s, θ s * g s x = 0)
    (t : ℝ) (hp : ∀ s x, 0 < 1 + t * g s x) :
    densityMeasure (barycenter (finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp)) =
      densityMeasure σ := by
  apply Subtype.ext
  apply withDensity_congr_ae
  exact Eventually.of_forall fun x => congrArg ENNReal.ofReal
    (finiteH1Split_barycenter_density σ q θ hθ hθsum g G hg hgc hm hcancel t hp x)

/-- Equality of actual barycenter probabilities identifies every genuine drift
only almost everywhere, through weak-gradient uniqueness. -/
theorem finiteH1Split_force (A : InteractionData 1) (b : AbsoluteDrift A)
    (σ : AbsoluteDensity 1) (q : ℕ+) (θ : Fin q → ℝ)
    (hθ : ∀ s, 0 < θ s) (hθsum : ∑ s, θ s = 1)
    (g : Fin q → Torus 1 → ℝ) (G : Fin q → Torus 1 → Tangent 1)
    (hg : ∀ s, IsWeakGradient (g s) (G s)) (hgc : ∀ s, Continuous (g s))
    (hm : ∀ s, ∫ x, g s x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (hcancel : ∀ x, ∑ s, θ s * g s x = 0)
    (t : ℝ) (hp : ∀ s x, 0 < 1 + t * g s x) :
    b.force (barycenter (finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp)) =ᵐ[haar 1]
      b.force σ := by
  apply b.ae_eq_of_isWeakGradient
  have he : interactionPotential A
      (barycenter (finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp)) =
      interactionPotential A σ := by
    unfold interactionPotential
    rw [finiteH1Split_barycenter σ q θ hθ hθsum g G hg hgc hm hcancel t hp]
  rw [he]
  exact b.weak_gradient σ

end DGPS.Examples.ThreeSpeciesCircle
