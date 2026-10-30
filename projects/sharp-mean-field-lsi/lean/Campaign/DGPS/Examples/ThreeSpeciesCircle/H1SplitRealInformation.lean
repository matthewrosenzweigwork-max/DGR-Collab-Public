import DGPS.Examples.ThreeSpeciesCircle.H1SplitSecondOrder

/-! Finiteness and real-valued information coefficients of the actual full-H1
split. No continuous-gradient assumption or infinite-toReal convention is used. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

theorem relativeSplit_information_integrable (μ : ProbabilityMeasure (Torus 1))
    (g : Torus 1 → ℝ) (hc : Continuous g) (G : Torus 1 → Tangent 1)
    (hG : MemLp G 2 (μ : Measure (Torus 1))) (t : ℝ)
    (hp : ∀ x, 0 < 1 + t * g x) :
    Integrable (fun x => ‖G x‖ ^ 2 / (1 + t * g x)) (μ : Measure (Torus 1)) := by
  have hinv : Continuous (fun x : Torus 1 => (1 + t * g x)⁻¹) := by
    have hd : Continuous (fun x : Torus 1 => (1 : ℝ) + t * g x) :=
      continuous_const.add (continuous_const.mul hc)
    have hh := hd.inv₀ (fun x => (hp x).ne')
    have heq : ((fun x : Torus 1 => (1 : ℝ) + t * g x)⁻¹) =
        (fun x => (1 + t * g x)⁻¹) := by funext x; rfl
    rw [heq] at hh
    exact hh
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hinv.continuousOn
  have hh := hG.norm.integrable_sq.mul_bdd hinv.aestronglyMeasurable
    (Eventually.of_forall fun x => hC x (Set.mem_univ x))
  simpa only [div_eq_mul_inv] using hh

/-- Actual weighted and Haar information integrals agree, with a finite real
coefficient proved from the genuine weighted-L2 gradient. -/
theorem relativeSplit_information_real (σ : AbsoluteDensity 1) (g : Torus 1 → ℝ)
    (G : Torus 1 → Tangent 1) (hg : IsWeakGradient g G) (hc : Continuous g)
    (hG : MemLp G 2 (densityMeasure σ : Measure (Torus 1))) (t : ℝ)
    (hp : ∀ x, 0 < 1 + t * g x) :
    (∫⁻ x, ENNReal.ofReal (t ^ 2 * σ.density x * ‖G x‖ ^ 2 / (1 + t * g x)) ∂haar 1) =
      ENNReal.ofReal (t ^ 2 * ∫ x, ‖G x‖ ^ 2 / (1 + t * g x)
        ∂(densityMeasure σ : Measure (Torus 1))) := by
  have hi := relativeSplit_information_integrable (densityMeasure σ) g hc G hG t hp
  have hnn (x : Torus 1) : 0 ≤ ‖G x‖ ^ 2 / (1 + t * g x) :=
    div_nonneg (sq_nonneg _) (hp x).le
  have hF : AEMeasurable (fun x => ENNReal.ofReal (‖G x‖ ^ 2 / (1 + t * g x))) (haar 1) := by
    have hn : AEMeasurable (fun x => ‖G x‖ ^ 2) (haar 1) :=
      (hg.memLp_grad.aestronglyMeasurable.norm.pow 2).aemeasurable
    have hd : AEMeasurable (fun x : Torus 1 => (1 : ℝ) + t * g x) (haar 1) :=
      (continuous_const.add (continuous_const.mul hc)).aemeasurable
    have hq := hn.div hd
    have heq : ((fun x : Torus 1 => ‖G x‖ ^ 2) / (fun x => 1 + t * g x)) =
        (fun x => ‖G x‖ ^ 2 / (1 + t * g x)) := by funext x; rfl
    rw [heq] at hq
    exact hq.ennreal_ofReal
  have hμ : (densityMeasure σ : Measure (Torus 1)) =
      (haar 1).withDensity (fun x => ENNReal.ofReal (σ.density x)) := rfl
  rw [ENNReal.ofReal_mul (sq_nonneg t),
    ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hnn),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    hμ,
    lintegral_withDensity_eq_lintegral_mul₀
      (σ.integrable_density.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      (hF.const_mul (ENNReal.ofReal (t ^ 2)))]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (t ^ 2 * σ.density x * ‖G x‖ ^ 2 / (1 + t * g x)) =
    ENNReal.ofReal (σ.density x) *
      (ENNReal.ofReal (t ^ 2) * ENNReal.ofReal (‖G x‖ ^ 2 / (1 + t * g x)))
  rw [← ENNReal.ofReal_mul (sq_nonneg t),
    ← ENNReal.ofReal_mul (σ.density_nonneg x)]
  congr 1
  ring

/-- Haar and native weighted H1 domains coincide at the actual positive
continuous base law; no alternate tangent domain is substituted. -/
theorem positiveRoot_gradient_memLp (σ : AbsoluteDensity 1)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hup : ∀ x, 0 < u x)
    (hrep : σ.sqrt =ᵐ[haar 1] u) {g : Torus 1 → ℝ} {G : Torus 1 → Tangent 1}
    (hg : IsWeakGradient g G) : MemLp G 2 (densityMeasure σ : Measure (Torus 1)) := by
  obtain ⟨P, hPμ, _⟩ := ordinaryRoot_boundedReference σ u hu hup hrep
  rw [← hPμ]
  exact P.memLp_measure_iff.2 hg.memLp_grad

section Finite
variable (σ : AbsoluteDensity 1) (q : ℕ+) (θ : Fin q → ℝ)
  (hθ : ∀ s, 0 < θ s) (hθsum : ∑ s, θ s = 1)
  (g : Fin q → Torus 1 → ℝ) (G : Fin q → Torus 1 → Tangent 1)
  (hg : ∀ s, IsWeakGradient (g s) (G s)) (hgc : ∀ s, Continuous (g s))
  (hm : ∀ s, ∫ x, g s x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
  (hcancel : ∀ x, ∑ s, θ s * g s x = 0)
  (hG : ∀ s, MemLp (G s) 2 (densityMeasure σ : Measure (Torus 1)))
  (t : ℝ) (hp : ∀ s x, 0 < 1 + t * g s x)

include hcancel hG

/-- Exact finite real split dissipation; base finiteness is material and is
established by the actual model identity before this theorem is used. -/
theorem finiteH1Split_dissipation_real (A : InteractionData 1) (b : AbsoluteDrift A)
    (hD : scalarDissipation A b σ ≠ ⊤) :
    speciesDissipation A b (finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp) ≠ ⊤ ∧
      (speciesDissipation A b (finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp)).toReal =
        (scalarDissipation A b σ).toReal + t ^ 2 *
          ∑ s, θ s * ∫ x, ‖G s x‖ ^ 2 / (1 + t * g s x)
            ∂(densityMeasure σ : Measure (Torus 1)) := by
  have he := finiteH1Split_dissipation σ q θ hθ hθsum g G hg hgc hm hcancel t hp A b
  simp_rw [relativeSplit_information_real σ _ _ (hg _) (hgc _) (hG _) t (hp _)] at he
  have hnonneg (s : Fin q) : 0 ≤ θ s * (t ^ 2 *
      ∫ x, ‖G s x‖ ^ 2 / (1 + t * g s x) ∂(densityMeasure σ : Measure (Torus 1))) :=
    mul_nonneg (hθ s).le (mul_nonneg (sq_nonneg t)
      (integral_nonneg fun x => div_nonneg (sq_nonneg _) (hp s x).le))
  have hsum : (∑ s, ENNReal.ofReal (θ s) * ENNReal.ofReal (t ^ 2 *
      ∫ x, ‖G s x‖ ^ 2 / (1 + t * g s x) ∂(densityMeasure σ : Measure (Torus 1)))) =
      ENNReal.ofReal (t ^ 2 * ∑ s, θ s *
        ∫ x, ‖G s x‖ ^ 2 / (1 + t * g s x) ∂(densityMeasure σ : Measure (Torus 1))) := by
    simp_rw [← ENNReal.ofReal_mul (hθ _).le]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hnonneg s), Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hsum] at he
  have hfin : speciesDissipation A b
      (finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp) ≠ ⊤ := by
    rw [he]
    exact ENNReal.add_ne_top.2 ⟨hD, ENNReal.ofReal_ne_top⟩
  refine ⟨hfin, ?_⟩
  rw [he, ENNReal.toReal_add hD ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg t)
      (Finset.sum_nonneg fun s _ => mul_nonneg (hθ s).le
        (integral_nonneg fun x => div_nonneg (sq_nonneg _) (hp s x).le)))]

end Finite
end DGPS.Examples.ThreeSpeciesCircle
