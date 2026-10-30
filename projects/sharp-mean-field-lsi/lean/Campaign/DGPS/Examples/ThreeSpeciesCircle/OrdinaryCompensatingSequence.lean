import DGPS.Examples.ThreeSpeciesCircle.OrdinaryCompensatingData
import DGPS.Lipschitz.T01SymmetricFamilyRate

/-! Actual count-two compensating minimizing sequences, on the full weighted
H1 domain. The complementary law is (mu-t*sigma)/(1-t), not a reference mixture. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open DGPS.Lipschitz

namespace DGPS.Examples.ThreeSpeciesCircle

theorem ordinary_relative_compensating_sequence {h ε : ℝ}
    (hh : 0 < h) (hε : 0 < ε) (hεmax : ε < epsMax h)
    (b : AbsoluteDrift (modelData h ε))
    (g : Torus 1 → ℝ) (hg : g ∈ WeightedH1 (ordinaryReference h))
    (hg0 : ∀ x, 0 ≤ g x) (hmass : ∫ x, g x ^ 2 ∂(ordinaryReference h).measure = 1)
    (M : ℝ) (hgM : ∀ x, |g x| ≤ M)
    (hH : 0 < ordinaryEntropy h (t01RelativeAbsoluteDensity (ordinaryReference h)
      (ordinaryReference_lip h) g hg hg0 hmass)) :
    let σ := t01RelativeAbsoluteDensity (ordinaryReference h) (ordinaryReference_lip h) g hg hg0 hmass
    ∃ (w : ℕ → ℝ) (F : ℕ → SpeciesFamily 1) (hcount : ∀ n, (F n).count = 2),
      (∀ n, 0 < w n ∧ w n < 1) ∧ Tendsto w atTop (𝓝 0) ∧
      (∀ n, (F n).weight ⟨0, by rw [hcount n]; decide⟩ = w n ∧ (F n).weight ⟨1, by rw [hcount n]; decide⟩ = 1 - w n ∧
        densityMeasure ((F n).density ⟨0, by rw [hcount n]; decide⟩) = densityMeasure σ ∧
        ((F n).density ⟨1, by rw [hcount n]; decide⟩).density =ᵐ[haar 1]
          (fun x => (referenceDensity h x - w n * σ.density x) / (1 - w n)) ∧
        (densityMeasure (barycenter (F n)) : Measure (Torus 1)) = threefoldReference h ∧
        0 < speciesGap (modelData h ε) (F n) ∧ speciesQuotient (modelData h ε) b (F n) ≠ ⊤) ∧
      Tendsto (fun n => speciesQuotient (modelData h ε) b (F n)) atTop (𝓝 (str025_quot h σ)) := by
  let P := ordinaryReference h
  let σ := t01RelativeAbsoluteDensity P (ordinaryReference_lip h) g hg hg0 hmass
  let w := compensatingDilutionWeight M
  have hw := compensatingDilutionWeight_bounds M
  let η := fun n => compensatingH1Species P (ordinaryReference_lip h) g hg hmass M hgM
    (w n) (hw n).1 (hw n).2.1 (hw n).2.2
  let F := fun n => compensatingH1Binary P (ordinaryReference_lip h) g hg hg0 hmass M hgM
    (w n) (hw n).1 (hw n).2.1 (hw n).2.2
  let i := (ordinaryFisher h σ).toReal
  let H := (ordinaryEntropy h σ).toReal
  let a := fun n => (ordinaryFisher h (η n)).toReal
  let d := fun n => (ordinaryEntropy h (η n)).toReal
  let E := ∫ x, ‖weightedGradient P g hg x‖ ^ 2 ∂P.measure
  let C := 32 * M ^ 2 * E + 4 * (M ^ 2 + 1) ^ 2 + 1
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hHpos : 0 < H := ENNReal.toReal_pos hH.ne' (str025_entropy_ne_top h σ)
  have ha (n : ℕ) : 0 ≤ a n ∧ a n ≤ C * w n ^ 2 := by
    have hb := compensatingH1Species_fisher_bound P (ordinaryReference_lip h) g hg hmass M hgM
      (w n) (hw n).1 (hw n).2.1 (hw n).2.2
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    change a n ≤ _ at hr
    rw [ENNReal.toReal_ofReal (by positivity)] at hr
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    dsimp only [C]
    nlinarith [sq_nonneg (w n), sq_nonneg (M ^ 2 + 1)]
  have hd (n : ℕ) : 0 ≤ d n ∧ d n ≤ C * w n ^ 2 := by
    have hb := compensatingH1Species_entropy_bound P (ordinaryReference_lip h) g hg hmass M hgM
      (w n) (hw n).1 (hw n).2.1 (hw n).2.2
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    change d n ≤ _ at hr
    rw [ENNReal.toReal_ofReal (by positivity)] at hr
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    dsimp only [C]
    nlinarith [mul_nonneg (sq_nonneg M) hE, sq_nonneg (w n)]
  have hbar (n : ℕ) : (densityMeasure (barycenter (F n)) : Measure (Torus 1)) = threefoldReference h :=
    compensatingH1Binary_barycenter P (ordinaryReference_lip h) g hg hg0 hmass M hgM
      (w n) (hw n).1 (hw n).2.1 (hw n).2.2
  have hGap (n : ℕ) : (speciesGap (modelData h ε) (F n) : ℝ) =
      w n * H + (1 - w n) * d n := by
    have ht := elementaryModel_reference_barycenter_gap hh hε hεmax (F n) (hbar n)
    change _ = (∑ s : Fin 2, (if s.val = 0 then w n else 1 - w n) *
      (ordinaryEntropy h (if s.val = 0 then σ else η n)).toReal) at ht
    simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, one_ne_zero, ↓reduceIte] using ht
  have hD (n : ℕ) : speciesDissipation (modelData h ε) b (F n) ≠ ⊤ ∧
      (speciesDissipation (modelData h ε) b (F n)).toReal =
        w n * i + (1 - w n) * a n := by
    obtain ⟨hfin, ht⟩ := elementaryModel_reference_barycenter_dissipation hh ε b (F n) (hbar n)
    change _ = (∑ s : Fin 2, (if s.val = 0 then w n else 1 - w n) *
      (ordinaryFisher h (if s.val = 0 then σ else η n)).toReal) at ht
    exact ⟨hfin, by simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
      one_ne_zero, ↓reduceIte] using ht⟩
  have hGpos (n : ℕ) : 0 < (speciesGap (modelData h ε) (F n) : ℝ) := by
    rw [hGap]
    have ht : 0 ≤ 1 - w n := by have := (hw n).2.1; linarith
    exact (mul_pos (hw n).1 hHpos).trans_le
      (le_add_of_nonneg_right (mul_nonneg ht (hd n).1))
  have hQ (n : ℕ) : speciesQuotient (modelData h ε) b (F n) = ENNReal.ofReal
      ((w n * i + (1 - w n) * a n) / (2 * (w n * H + (1 - w n) * d n))) := by
    have hden : 2 * (speciesGap (modelData h ε) (F n) : ℝ≥0∞) =
        ENNReal.ofReal (2 * (w n * H + (1 - w n) * d n)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← hGap, ENNReal.ofReal_coe_nnreal]
      norm_num
    unfold speciesQuotient
    rw [hden, ← ENNReal.ofReal_toReal (hD n).1, (hD n).2]
    have hp : 0 < 2 * (w n * H + (1 - w n) * d n) := by
      have hn : 0 < w n * H + (1 - w n) * d n := by
        simpa only [hGap] using hGpos n
      positivity
    exact (ENNReal.ofReal_div_of_pos hp).symm
  have hlim := ENNReal.tendsto_ofReal
    (compensating_binary_real_limit (i := i) (C := C) hHpos w a d (fun n => (hw n).1)
      (compensatingDilutionWeight_tendsto M) ha hd)
  have hquot : str025_quot h σ = ENNReal.ofReal (i / (2 * H)) := by
    change ordinaryFisher h σ / (2 * ordinaryEntropy h σ) = _
    rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < 2 * H),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_toReal (str025_fisher_ne_top h σ),
      ENNReal.ofReal_toReal (str025_entropy_ne_top h σ)]
    norm_num
  refine ⟨w, F, (fun n => rfl), fun n => ⟨(hw n).1, by have := (hw n).2.1; linarith⟩,
    compensatingDilutionWeight_tendsto M, fun n => ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, ?_, hbar n, hGpos n, ?_⟩
    · exact Eventually.of_forall fun x => compensatingH1Species_density
        P (ordinaryReference_lip h) g hg hg0 hmass M hgM (w n)
        (hw n).1 (hw n).2.1 (hw n).2.2 x
    · rw [hQ]
      exact ENNReal.ofReal_ne_top
  · rw [hquot]
    exact hlim.congr fun n => (hQ n).symm

/-- Actual ordinary equality roots admit the specific compensating binary
minimizing sequences, chosen internally on the full H1 domain. -/
theorem ordinaryRoots_compensating_binary_sequence (D : OrdinaryRootGraphData)
    {h ε : ℝ} (hh : 0 < h) (hhd : h < D.radius)
    (hε : 0 < ε) (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) :
    ∃ σ : Fin 3 → AbsoluteDensity 1,
      (∀ j, 0 < ordinaryEntropy h (σ j)) ∧
      ∀ j : Fin 3, ∃ (w : ℕ → ℝ) (F : ℕ → SpeciesFamily 1) (hcount : ∀ n, (F n).count = 2),
        (∀ n, 0 < w n ∧ w n < 1) ∧ Tendsto w atTop (𝓝 0) ∧
        (∀ n, (F n).weight ⟨0, by rw [hcount n]; decide⟩ = w n ∧ (F n).weight ⟨1, by rw [hcount n]; decide⟩ = 1 - w n ∧
          densityMeasure ((F n).density ⟨0, by rw [hcount n]; decide⟩) = densityMeasure (σ j) ∧
          ((F n).density ⟨1, by rw [hcount n]; decide⟩).density =ᵐ[haar 1]
            (fun x => (referenceDensity h x - w n * (σ j).density x) / (1 - w n)) ∧
          (densityMeasure (barycenter (F n)) : Measure (Torus 1)) = threefoldReference h ∧
          0 < speciesGap (modelData h ε) (F n) ∧ speciesQuotient (modelData h ε) b (F n) ≠ ⊤) ∧
        Tendsto (fun n => speciesQuotient (modelData h ε) b (F n)) atTop
          (𝓝 (ordinaryLSRate (ordinaryReference h))) := by
  obtain ⟨σ, hpos, hquot, hdata⟩ := ordinaryRoots_compensating_data D hh hhd
  refine ⟨σ, hpos, fun j => ?_⟩
  obtain ⟨g, hg, hg0, hmass, M, _, _, hgM, hμ⟩ := hdata j
  let τ := t01RelativeAbsoluteDensity (ordinaryReference h) (ordinaryReference_lip h) g hg hg0 hmass
  have hH : 0 < ordinaryEntropy h τ := by unfold ordinaryEntropy; rw [hμ]; exact hpos j
  obtain ⟨w, F, hcount, hw, hwlim, hFn, hlim⟩ := ordinary_relative_compensating_sequence
    hh hε hεmax b g hg hg0 hmass M hgM hH
  have hquotτ : str025_quot h τ = ordinaryLSRate (ordinaryReference h) := by
    change ordinaryFisher h τ / (2 * ordinaryEntropy h τ) = _
    unfold ordinaryFisher ordinaryEntropy
    rw [hμ]
    exact hquot j
  have hlimRate : Tendsto (fun n => speciesQuotient (modelData h ε) b (F n))
      atTop (𝓝 (ordinaryLSRate (ordinaryReference h))) := by
    change Tendsto _ atTop (𝓝 (str025_quot h τ)) at hlim
    rwa [hquotτ] at hlim
  refine ⟨w, F, hcount, hw, hwlim, fun n => ?_, hlimRate⟩
  obtain ⟨hw0, hw1, hfirst, hsecond, hbar, hG, hQ⟩ := hFn n
  refine ⟨hw0, hw1, hfirst.trans hμ, ?_, hbar, hG, hQ⟩
  have hdens := t01_density_ae_eq_of_measure_eq hμ
  filter_upwards [hsecond, hdens] with x hx he
  rwa [he] at hx

/-- Actual public compensation-sequence factory; the ordinary graph is chosen
internally, with no smooth-competitor or analytic-provider premise. -/
theorem elementaryModel_compensating_binary_sequence :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ ε : ℝ, 0 < ε → ε < epsMax h → ∀ b : AbsoluteDrift (modelData h ε),
    ∃ σ : Fin 3 → AbsoluteDensity 1,
      (∀ j, 0 < ordinaryEntropy h (σ j)) ∧
      ∀ j : Fin 3, ∃ (w : ℕ → ℝ) (F : ℕ → SpeciesFamily 1) (hcount : ∀ n, (F n).count = 2),
        (∀ n, 0 < w n ∧ w n < 1) ∧ Tendsto w atTop (𝓝 0) ∧
        (∀ n, (F n).weight ⟨0, by rw [hcount n]; decide⟩ = w n ∧ (F n).weight ⟨1, by rw [hcount n]; decide⟩ = 1 - w n ∧
          densityMeasure ((F n).density ⟨0, by rw [hcount n]; decide⟩) = densityMeasure (σ j) ∧
          ((F n).density ⟨1, by rw [hcount n]; decide⟩).density =ᵐ[haar 1]
            (fun x => (referenceDensity h x - w n * (σ j).density x) / (1 - w n)) ∧
          (densityMeasure (barycenter (F n)) : Measure (Torus 1)) = threefoldReference h ∧
          0 < speciesGap (modelData h ε) (F n) ∧ speciesQuotient (modelData h ε) b (F n) ≠ ⊤) ∧
        Tendsto (fun n => speciesQuotient (modelData h ε) b (F n)) atTop
          (𝓝 (ordinaryLSRate (ordinaryReference h))) := by
  obtain ⟨D⟩ := exists_ordinaryRootGraphData
  exact ⟨D.radius, D.radius_pos, fun h hh hhd ε hε hεmax b =>
    ordinaryRoots_compensating_binary_sequence D hh hhd hε hεmax b⟩

end DGPS.Examples.ThreeSpeciesCircle
