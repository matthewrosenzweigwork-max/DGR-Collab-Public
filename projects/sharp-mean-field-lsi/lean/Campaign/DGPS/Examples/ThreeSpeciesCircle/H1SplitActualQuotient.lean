import DGPS.Examples.ThreeSpeciesCircle.H1SplitQuotientAlgebra

/-! The actual finite-species quotient expansion from the genuine H1 split.
The remainder is computed from its concrete entropy/information quotient. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

section Finite
variable (σ : AbsoluteDensity 1) (q : ℕ+) (θ : Fin q → ℝ)
  (hθ : ∀ s, 0 < θ s) (hθsum : ∑ s, θ s = 1)
  (g : Fin q → Torus 1 → ℝ) (G : Fin q → Torus 1 → Tangent 1)
  (hg : ∀ s, IsWeakGradient (g s) (G s)) (hgc : ∀ s, Continuous (g s))
  (hm : ∀ s, ∫ x, g s x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
  (hcancel : ∀ x, ∑ s, θ s * g s x = 0)
  (hG : ∀ s, MemLp (G s) 2 (densityMeasure σ : Measure (Torus 1)))

include hcancel hG

/-- Exact second-order expansion of the ACTUAL species quotient. The strict
conclusion is conditional only in this reusable lemma; the actual minimizer
factory must supply positivity of its coefficient from the proved Poincare gap. -/
theorem finiteH1Split_actual_quotient_expansion (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε))
    (hbase : 0 < scalarGap (modelData h ε) σ)
    (hmin : scalarQuotient (modelData h ε) b σ = scalarRate (modelData h ε) b)
    (hcoef : 0 < (∑ s, θ s * ∫ x, ‖G s x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) -
      (scalarRate (modelData h ε) b).toReal *
        (∑ s, θ s * ∫ x, g s x ^ 2 ∂(densityMeasure σ : Measure (Torus 1)))) :
    let r := (scalarRate (modelData h ε) b).toReal
    let B := ∑ s, θ s * ∫ x, g s x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))
    let E := ∑ s, θ s * ∫ x, ‖G s x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))
    let c := (E - r * B) / (2 * (scalarGap (modelData h ε) σ : ℝ))
    0 < c ∧ ∃ t0 : ℝ, 0 < t0 ∧ ∃ rem : ℝ → ℝ,
      Tendsto (fun t => rem t / t ^ 2) (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 0) ∧
      ∀ t : ℝ, 0 < |t| → |t| < t0 →
        ∃ hp : ∀ s x, 0 < 1 + t * g s x,
          let F := finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp
          densityMeasure (barycenter F) = densityMeasure σ ∧
          0 < speciesGap (modelData h ε) F ∧
          speciesQuotient (modelData h ε) b F ≠ ⊤ ∧
          speciesQuotient (modelData h ε) b F = ENNReal.ofReal (r + c * t ^ 2 + rem t) ∧
          scalarRate (modelData h ε) b < speciesQuotient (modelData h ε) b F := by
  let r := (scalarRate (modelData h ε) b).toReal
  let Gb : ℝ := scalarGap (modelData h ε) σ
  let B := ∑ s, θ s * ∫ x, g s x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))
  let E := ∑ s, θ s * ∫ x, ‖G s x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))
  let H := fun t : ℝ => ∑ s, θ s *
    ∫ x, InformationTheory.klFun (1 + t * g s x) ∂(densityMeasure σ : Measure (Torus 1))
  let I := fun t : ℝ => ∑ s, θ s *
    ∫ x, ‖G s x‖ ^ 2 / (1 + t * g s x) ∂(densityMeasure σ : Measure (Torus 1))
  let Q := fun t : ℝ => (2 * r * Gb + t ^ 2 * I t) / (2 * (Gb + H t))
  let c := (E - r * B) / (2 * Gb)
  let rem := fun t : ℝ => Q t - r - c * t ^ 2
  have hGb : 0 < Gb := hbase
  have hc : 0 < c := div_pos hcoef (by positivity)
  have hHlim : Tendsto (fun t => H t / t ^ 2) (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 (B / 2)) := by
    have ht := tendsto_finsetSum Finset.univ fun s _ =>
      (relativeSplit_entropy_coefficient_tendsto (densityMeasure σ) (g s) (hgc s)).const_mul (θ s)
    convert ht using 1
    · funext t
      dsimp only [H]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      ring
    · dsimp only [B]
      rw [Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      ring
  have hIlim : Tendsto I (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 E) := by
    exact tendsto_finsetSum Finset.univ fun s _ =>
      ((relativeSplit_information_coefficient_tendsto (densityMeasure σ) (g s)
        (hgc s) (G s) (hG s)).mono_left nhdsWithin_le_nhds).const_mul (θ s)
  have hrem : Tendsto (fun t => rem t / t ^ 2) (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 0) :=
    splitQuotient_remainder hGb H I hHlim hIlim
  have hstrict := splitQuotient_eventually_strict hc Q hrem
  have hpositive := finiteH1Split_eventually_positive q g hgc
  have hev : ∀ᶠ t : ℝ in 𝓝[{t : ℝ | t ≠ 0}] 0,
      (∀ s x, 0 < 1 + t * g s x) ∧ r < Q t := by
    filter_upwards [hpositive.filter_mono nhdsWithin_le_nhds, hstrict] with t hp hs
    exact ⟨hp, hs⟩
  obtain ⟨t0, ht0, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  have hDfin := (elementaryModel_scalarDissipation_real h ε b σ).1
  have hrfin : scalarRate (modelData h ε) b ≠ ⊤ := by
    rw [← hmin]
    unfold scalarQuotient
    exact ENNReal.div_ne_top hDfin
      (mul_ne_zero (by norm_num) (by exact_mod_cast hbase.ne'))
  have hDb : (scalarDissipation (modelData h ε) b σ).toReal = 2 * r * Gb := by
    have ht := congrArg ENNReal.toReal hmin
    unfold scalarQuotient at ht
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal] at ht
    change (scalarDissipation (modelData h ε) b σ).toReal / (2 * Gb) = r at ht
    have he := (div_eq_iff (by positivity : 2 * Gb ≠ 0)).1 ht
    nlinarith
  change 0 < c ∧ _
  refine ⟨hc, t0, ht0, rem, hrem, fun t ht hsmall => ?_⟩
  have htn : t ≠ 0 := by intro he; simp [he] at ht
  have hbt : t ∈ Metric.ball (0 : ℝ) t0 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsmall
  obtain ⟨hp, hQt⟩ := hball ⟨hbt, htn⟩
  let F := finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp
  have hGap : (speciesGap (modelData h ε) F : ℝ) = Gb + H t :=
    finiteH1Split_gap σ q θ hθ hθsum g G hg hgc hm hcancel t hp (modelData h ε)
  have hHpos : 0 ≤ H t := Finset.sum_nonneg fun s _ =>
    mul_nonneg (hθ s).le (integral_nonneg fun x => InformationTheory.klFun_nonneg (hp s x).le)
  have hGpos : 0 < (speciesGap (modelData h ε) F : ℝ) := by rw [hGap]; linarith
  obtain ⟨hFDfin, hFD⟩ := finiteH1Split_dissipation_real σ q θ hθ hθsum g G hg hgc hm
    hcancel hG t hp (modelData h ε) b hDfin
  have hQeq : speciesQuotient (modelData h ε) b F = ENNReal.ofReal (Q t) := by
    have hden : 2 * (speciesGap (modelData h ε) F : ℝ≥0∞) =
        ENNReal.ofReal (2 * (Gb + H t)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← hGap, ENNReal.ofReal_coe_nnreal]
      norm_num
    unfold speciesQuotient
    rw [hden, ← ENNReal.ofReal_toReal hFDfin, hFD, hDb]
    exact (ENNReal.ofReal_div_of_pos (by positivity : 0 < 2 * (Gb + H t))).symm
  refine ⟨hp, finiteH1Split_barycenter σ q θ hθ hθsum g G hg hgc hm hcancel t hp,
    hGpos, ?_, ?_, ?_⟩
  · rw [hQeq]
    exact ENNReal.ofReal_ne_top
  · rw [hQeq]
    congr 1
    dsimp only [rem]
    ring
  · rw [hQeq, ← ENNReal.ofReal_toReal hrfin]
    exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hQt, ENNReal.toReal_nonneg.trans_lt hQt⟩

end Finite
end DGPS.Examples.ThreeSpeciesCircle
