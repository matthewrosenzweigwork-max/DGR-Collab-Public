import SharpSymmetricLSI.Paper.LyapSchmidt14

/-!
# Section 4.2 (lane s42; R14): the chart of the minimizer set near `μ`

* graph points `ρ_a = p(1 + kC a + ψ a) m` are minimizers with `hR ρ_a = kC a + ψ a` and
  coordinates `(∫ φᵢ dρ_a)ᵢ = a`;
* every minimizer `ν` near `μ` (weakly) satisfies `FC (coord ν, P(hR ν)) = 0`, hence lies on the
  graph (local uniqueness in the implicit function theorem);
* `a ↦ ρ_a` is a homeomorphism from a ball onto `{ν ∈ U : ν minimizer}`, `U` weakly open.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real Topology Metric BoundedContinuousFunction
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section chart
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)
include hyp hμ

/-- Two continuous densities with the same `densMeasure` coincide. -/
theorem eq_of_densMeasure_eq {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (h : densMeasure f = densMeasure g) : f = g := by
  unfold densMeasure at h
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (ENNReal.measurable_ofReal.comp hf.measurable).aemeasurable
    (ENNReal.measurable_ofReal.comp hg.measurable).aemeasurable).mp h
  have hae' : f =ᵐ[haar d] g := by
    filter_upwards [hae] with x hx
    have := congrArg ENNReal.toReal hx
    simpa [ENNReal.toReal_ofReal (hf0 x), ENNReal.toReal_ofReal (hg0 x)] using this
  exact (Continuous.ae_eq_iff_eq (μ := haar d) hf hg).mp hae'

theorem continuous_elDens_min : Continuous (elDens V W (μ : Measure (Torus d))) := by
  obtain ⟨cl, Cu, Lp, hcl, hbd⟩ := elDensity_bounds hyp
  exact (hbd (μ : Measure (Torus d)) inferInstance).2.continuous

/-- A gap-zero graph density is a minimizer, and its density ratio is `h`. -/
theorem graph_point_minimizer {h : CT d} (hpos : h ∈ posSet)
    (hh0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0)
    (hΨ : PsiC hyp (μ : Measure (Torus d)) h = 0)
    (hp : IsProbabilityMeasure (densMeasure fun x => elDens V W (μ : Measure (Torus d)) x *
      (1 + h x))) :
    IsMinimizer V W (⟨_, hp⟩ : ProbabilityMeasure (Torus d)) ∧
      hR hyp μ (⟨_, hp⟩ : ProbabilityMeasure (Torus d)) = h := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨h0, h1⟩ := graph_density_props hyp hμ hpos hh0
  have hrc : Continuous fun x => elDens V W μm x * (1 + h x) :=
    (continuous_elDens_min hyp hμ).mul (continuous_const.add h.continuous)
  have hkl := klDiv_densMeasure_ne_top_of_continuous hrc (fun x => (h0 x).le) h1
  have hgap := gap_graph hyp hμ hpos hh0
  rw [hΨ] at hgap
  have hg := gap_eq_coe hyp hkl
  rw [hgap] at hg
  have hr := EReal.coe_injective hg
  have hmin : IsMinimizer V W (⟨_, hp⟩ : ProbabilityMeasure (Torus d)) := by
    show freeEnergy V W (densMeasure fun x => elDens V W μm x * (1 + h x)) = Fstar V W
    rw [freeEnergy_eq _ hkl, Fstar_eq_coe hyp]
    congr 1
    linarith
  refine ⟨hmin, ?_⟩
  have h2 := minimizer_eq_graph hyp hμ hmin
  have h3 : (fun x => elDens V W μm x * (1 + hR hyp μ (⟨_, hp⟩ : ProbabilityMeasure (Torus d)) x)) =
      fun x => elDens V W μm x * (1 + h x) := by
    refine eq_of_densMeasure_eq hyp hμ
      ((continuous_elDens_min hyp hμ).mul (continuous_const.add (hR hyp μ _).continuous)) hrc
      (fun x => mul_nonneg ((elDensity_props hyp μm).2.1 x).le (hR_pos hyp hμ _ x).le)
      (fun x => (h0 x).le) ?_
    rw [← h2]; rfl
  ext x
  have h4 : elDens V W μm x * (1 + hR hyp μ (⟨_, hp⟩ : ProbabilityMeasure (Torus d)) x) =
      elDens V W μm x * (1 + h x) := congrFun h3 x
  have hp0 := (elDensity_props hyp μm).2.1 x
  have := mul_left_cancel₀ hp0.ne' h4
  linarith

include hφ

omit hμ in
theorem QCraw_kC (a : EuclideanSpace ℝ (Fin n)) : QCraw hyp hφ (kC hyp hφ a) = 0 := by
  rw [QCraw_apply, integral_kC hyp hφ]
  simp_rw [integral_kC_mul_phiC hyp hφ]
  ext x
  simp [kC_apply]

omit hμ in
/-- The coordinates `(∫ φᵢ dν)ᵢ`. -/
def coordE (ν : ProbabilityMeasure (Torus d)) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i => ∫ x, phiC hyp hφ i x ∂(ν : Measure (Torus d))

omit hμ in
theorem continuous_coordE : Continuous (coordE hyp hφ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp (continuous_pi fun i =>
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (mkOfCompact (phiC hyp hφ i)))

omit hμ in
theorem coordE_apply (ν : ProbabilityMeasure (Torus d)) (i : Fin n) :
    coordE hyp hφ ν i = ∫ x, phiC hyp hφ i x ∂(ν : Measure (Torus d)) := rfl

/-- On a minimizer, `hR ν = kC (coord ν) + P(hR ν)`. -/
theorem hR_decomp {ν : ProbabilityMeasure (Torus d)} (hν : IsMinimizer V W ν) :
    hR hyp μ ν = kC hyp hφ (coordE hyp hφ ν) + QCraw hyp hφ (hR hyp μ ν) := by
  ext x
  rw [ContinuousMap.add_apply, QCraw_apply, kC_apply]
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
    smul_eq_mul, mul_one, ContinuousMap.coe_sum, Finset.sum_apply, mean_hR hyp hμ ν,
    coordE_apply, coord_minimizer hyp hμ hφ hν]
  ring

end chart

end SharpLSI
