import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesReduction
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryDeficitCompactness
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarLimits
import DGPS.Examples.ThreeSpeciesCircle.InteractingQuotientInformationBound
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Finite

/-! Compactness support for finite families with vanishing weights. The weights
have no uniform positive lower bound. A positive-gap limit is not asserted. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A disappearing weight carries no entropy when its weighted actual ordinary
Fisher information is uniformly bounded. All actual entropies and informations
are finite before `toReal` is used; no positive lower bound on weights is needed. -/
theorem ordinaryEntropy_vanishing_weight (h : ℝ) (θ : ℕ → ℝ)
    (ρ : ℕ → AbsoluteDensity 1) (hθ : ∀ n, 0 ≤ θ n)
    (ht : Tendsto θ atTop (𝓝 0)) {C : ℝ}
    (hI : ∀ n, θ n * (ordinaryFisher h (ρ n)).toReal ≤ C) :
    Tendsto (fun n => θ n * (ordinaryEntropy h (ρ n)).toReal) atTop (𝓝 0) := by
  have hfiniteI : ∀ n, ordinaryFisher h (ρ n) ≠ ⊤ := fun n => str025_fisher_ne_top h (ρ n)
  have hfiniteH : ∀ n, ordinaryEntropy h (ρ n) ≠ ⊤ := fun n => str025_entropy_ne_top h (ρ n)
  have hC : 0 ≤ C := (mul_nonneg (hθ 0) ENNReal.toReal_nonneg).trans (hI 0)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (mul_nonneg (hθ n) ENNReal.toReal_nonneg)
  · intro e he
    let η := e / (2 * (C + 1))
    have hη : 0 < η := by dsimp [η]; positivity
    have hηeq : η * (C + 1) = e / 2 := by
      dsimp [η]
      field_simp
      <;> ring
    have hηC : η * C < e / 2 := by nlinarith
    obtain ⟨B, hB, hbudget⟩ := ordinaryEntropy_information_bound h η hη
    have htB : Tendsto (fun n => θ n * B) atTop (𝓝 0) := by simpa using ht.mul_const B
    filter_upwards [(tendsto_order.mp htB).2 (e / 2) (half_pos he)] with n hn
    have hH := mul_le_mul_of_nonneg_left (hbudget (ρ n)) (hθ n)
    have hIn := mul_le_mul_of_nonneg_left (hI n) hη.le
    nlinarith

/-- The same disappearing-weight statement in the native ENNReal entropy type. -/
theorem ordinaryEntropy_vanishing_weight_ennreal (h : ℝ) (θ : ℕ → ℝ)
    (ρ : ℕ → AbsoluteDensity 1) (hθ : ∀ n, 0 ≤ θ n)
    (ht : Tendsto θ atTop (𝓝 0)) {C : ℝ}
    (hI : ∀ n, θ n * (ordinaryFisher h (ρ n)).toReal ≤ C) :
    Tendsto (fun n => ENNReal.ofReal (θ n) * ordinaryEntropy h (ρ n)) atTop (𝓝 0) := by
  have hlim := ENNReal.tendsto_ofReal (ordinaryEntropy_vanishing_weight h θ ρ hθ ht hI)
  simpa only [ENNReal.ofReal_zero, ENNReal.ofReal_mul (hθ _),
    ENNReal.ofReal_toReal (str025_entropy_ne_top h _)] using hlim

/-- Convert bounded actual ordinary information to the original Haar information
required by the existing one-dimensional square-root compactness theorem. -/
theorem circleFisher_le_two_ordinary_toReal (h : ℝ) (ρ : AbsoluteDensity 1) :
    DGPS.Analysis.circleFisherInformation ρ ≤
      2 * (ordinaryFisher h ρ).toReal + 2 * logGradBound h ^ 2 := by
  have h2fin : 2 * ordinaryFisher h ρ ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (str025_fisher_ne_top h ρ)
  have hRfin : 2 * ordinaryFisher h ρ + ENNReal.ofReal (2 * logGradBound h ^ 2) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h2fin, ENNReal.ofReal_ne_top⟩
  have hIm := ENNReal.toReal_mono hRfin (fisher_le_two_ordinary h ρ)
  rw [ENNReal.toReal_ofReal (circleFisherInformation_nonneg ρ),
    ENNReal.toReal_add h2fin ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by positivity)] at hIm
  exact hIm

/-- A positive limiting weight gives a true unweighted information bound on a tail.
The cutoff depends on the limiting weight, rather than a uniform weight constraint. -/
theorem ordinaryFisher_bound_of_positive_weight_limit (h : ℝ) (θ : ℕ → ℝ)
    (ρ : ℕ → AbsoluteDensity 1) {θL C : ℝ} (hθL : 0 < θL)
    (ht : Tendsto θ atTop (𝓝 θL))
    (hI : ∀ n, θ n * (ordinaryFisher h (ρ n)).toReal ≤ C) :
    ∃ N : ℕ, ∀ n ≥ N, (ordinaryFisher h (ρ n)).toReal ≤ 2 * C / θL := by
  have hlow : ∀ᶠ n in atTop, θL / 2 < θ n :=
    (tendsto_order.mp ht).1 (θL / 2) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlow
  refine ⟨N, fun n hn => ?_⟩
  apply (le_div_iff₀ hθL).mpr
  have hm := mul_le_mul_of_nonneg_right (hN n hn).le
    (show 0 ≤ (ordinaryFisher h (ρ n)).toReal from ENNReal.toReal_nonneg)
  nlinarith [hI n]

/-- An individual positive-limit label has an actual square-root compactness
subsequence. No assertion is made about labels whose limiting weights vanish. -/
theorem positive_weight_root_compactness (h : ℝ) (θ : ℕ → ℝ)
    (ρ : ℕ → AbsoluteDensity 1) {θL C : ℝ} (hθL : 0 < θL)
    (ht : Tendsto θ atTop (𝓝 θL))
    (hI : ∀ n, θ n * (ordinaryFisher h (ρ n)).toReal ≤ C) :
    ∃ (φ : ℕ → ℕ) (ρL : AbsoluteDensity 1) (ε : ℕ → ℝ) (R : ℝ),
      StrictMono φ ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x - ρL.sqrt x| ≤ ε n) ∧
      (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x| ≤ R) ∧ (∀ x, |ρL.sqrt x| ≤ R) ∧
      Tendsto (fun n => ordinaryEntropy h (ρ (φ n))) atTop (𝓝 (ordinaryEntropy h ρL)) ∧
      ordinaryFisher h ρL ≤ liminf (fun n => ordinaryFisher h (ρ (φ n))) atTop := by
  obtain ⟨N, hN⟩ := ordinaryFisher_bound_of_positive_weight_limit h θ ρ hθL ht hI
  let σ : ℕ → ℕ := fun n => n + N
  have hσ : StrictMono σ := fun i j hij => Nat.add_lt_add_right hij N
  have hB : ∀ n, DGPS.Analysis.circleFisherInformation (ρ (σ n)) ≤
      2 * (2 * C / θL) + 2 * logGradBound h ^ 2 := by
    intro n
    exact (circleFisher_le_two_ordinary_toReal h (ρ (σ n))).trans
      (by have hh := hN (σ n) (by dsimp [σ]; omega); linarith)
  obtain ⟨ψ, ρL, ε, R, hψ, hε, hae, hub, hLb, -⟩ :=
    exists_limit_of_bounded_fisher (fun n => ρ (σ n)) hB
  have hpt : ∀ᵐ x ∂haar 1,
      Tendsto (fun n => (ρ (σ (ψ n))).sqrt x) atTop (𝓝 (ρL.sqrt x)) := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs]
      exact hx n) hε
  exact ⟨σ ∘ ψ, ρL, ε, R, hσ.comp hψ, hε, hae, hub, hLb,
    tendsto_ordinaryEntropy h hub hpt,
    ordinaryFisher_le_liminf h (fun n => ρ (σ (ψ n))) ρL hε hae⟩

/-- Finitely many positive-limit labels have one common genuine root-compactness
subsequence. The individual limit weights may be arbitrarily small. -/
theorem finite_positive_weight_root_compactness {ι : Type*} [Fintype ι]
    (h : ℝ) (θ : ℕ → ι → ℝ) (ρ : ℕ → ι → AbsoluteDensity 1)
    (θL : ι → ℝ) (ht : ∀ i, Tendsto (fun n => θ n i) atTop (𝓝 (θL i))) {C : ℝ}
    (hI : ∀ n i, θ n i * (ordinaryFisher h (ρ n i)).toReal ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, 0 < θL i →
      ∃ (ρL : AbsoluteDensity 1) (ε : ℕ → ℝ) (R : ℝ),
        Tendsto ε atTop (𝓝 0) ∧
        (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n) i).sqrt x - ρL.sqrt x| ≤ ε n) ∧
        (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n) i).sqrt x| ≤ R) ∧ (∀ x, |ρL.sqrt x| ≤ R) ∧
        Tendsto (fun n => ordinaryEntropy h (ρ (φ n) i)) atTop (𝓝 (ordinaryEntropy h ρL)) ∧
        ordinaryFisher h ρL ≤ liminf (fun n => ordinaryFisher h (ρ (φ n) i)) atTop := by
  classical
  let P (φ : ℕ → ℕ) (i : ι) : Prop :=
    ∃ (ρL : AbsoluteDensity 1) (ε : ℕ → ℝ) (R : ℝ),
      Tendsto ε atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n) i).sqrt x - ρL.sqrt x| ≤ ε n) ∧
      (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n) i).sqrt x| ≤ R) ∧ (∀ x, |ρL.sqrt x| ≤ R)
  have hstable (φ ψ : ℕ → ℕ) (hψ : StrictMono ψ) (i : ι) : P φ i → P (φ ∘ ψ) i := by
    rintro ⟨ρL, ε, R, hε, hae, hub, hLb⟩
    exact ⟨ρL, ε ∘ ψ, R, hε.comp hψ.tendsto_atTop,
      fun n => hae (ψ n), fun n => hub (ψ n), hLb⟩
  have hextract (φ : ℕ → ℕ) (hφ : StrictMono φ) (i : ι) (hi : 0 < θL i) :
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P (φ ∘ ψ) i := by
    obtain ⟨ψ, ρL, ε, R, hψ, hε, hae, hub, hLb, -, -⟩ :=
      positive_weight_root_compactness h (fun n => θ (φ n) i) (fun n => ρ (φ n) i)
        hi ((ht i).comp hφ.tendsto_atTop) (fun n => hI (φ n) i)
    exact ⟨ψ, hψ, ρL, ε, R, hε, hae, hub, hLb⟩
  have hfinite : ∀ s : Finset ι, (∀ i ∈ s, 0 < θL i) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i ∈ s, P φ i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨id, strictMono_id, fun i hi => by simp at hi⟩
    | @insert i s his ih =>
      intro hs
      obtain ⟨φ, hφ, hP⟩ := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
      obtain ⟨ψ, hψ, hi⟩ := hextract φ hφ i (hs i (Finset.mem_insert_self i s))
      refine ⟨φ ∘ ψ, hφ.comp hψ, fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact hstable φ ψ hψ j (hP j hj)
  obtain ⟨φ, hφ, hP⟩ := hfinite (Finset.univ.filter fun i => 0 < θL i)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  refine ⟨φ, hφ, fun i hi => ?_⟩
  obtain ⟨ρL, ε, R, hε, hae, hub, hLb⟩ := hP i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hpt : ∀ᵐ x ∂haar 1,
      Tendsto (fun n => (ρ (φ n) i).sqrt x) atTop (𝓝 (ρL.sqrt x)) := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs]
      exact hx n) hε
  exact ⟨ρL, ε, R, hε, hae, hub, hLb, tendsto_ordinaryEntropy h hub hpt,
    ordinaryFisher_le_liminf h (fun n => ρ (φ n) i) ρL hε hae⟩

/-- Extract a simplex weight limit without retaining zero weights as species. The
later family construction uses only its positive support. -/
theorem finite_simplex_weight_subsequence {ι : Type*} [Fintype ι]
    (θ : ℕ → ι → ℝ) (hθ : ∀ n i, 0 ≤ θ n i) (hmass : ∀ n, ∑ i, θ n i = 1) :
    ∃ (φ : ℕ → ℕ) (θL : ι → ℝ), StrictMono φ ∧
      (∀ i, 0 ≤ θL i) ∧ (∑ i, θL i = 1) ∧
      ∀ i, Tendsto (fun n => θ (φ n) i) atTop (𝓝 (θL i)) := by
  classical
  have hupper : ∀ n i, θ n i ≤ 1 := by
    intro n i
    calc
      _ ≤ ∑ j, θ n j := Finset.single_le_sum (fun j _ => hθ n j) (Finset.mem_univ i)
      _ = _ := hmass n
  let z : ℕ → (ι → Set.Icc (0 : ℝ) 1) :=
    fun n i => ⟨θ n i, hθ n i, hupper n i⟩
  obtain ⟨zL, φ, hφ, hz⟩ := CompactSpace.tendsto_subseq z
  let θL : ι → ℝ := fun i => (zL i).val
  have hlim (i : ι) : Tendsto (fun n => θ (φ n) i) atTop (𝓝 (θL i)) := by
    have hc : Continuous (fun y : ι → Set.Icc (0 : ℝ) 1 => ((y i) : ℝ)) :=
      continuous_subtype_val.comp (continuous_apply i)
    simpa only [Function.comp_def, z, θL] using (hc.tendsto zL).comp hz
  refine ⟨φ, θL, hφ, fun i => (zL i).property.1, ?_, hlim⟩
  have hs := tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  have he : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (∑ i, θL i)) := by
    simpa only [hmass] using hs
  exact tendsto_nhds_unique he tendsto_const_nhds

/-- Bounded continuous moments of a disappearing label vanish with its weight,
without compactness of that label's density. -/
theorem densityMoment_vanishing_weight (θ : ℕ → ℝ) (ρ : ℕ → AbsoluteDensity 1)
    (hθ : ∀ n, 0 ≤ θ n) (ht : Tendsto θ atTop (𝓝 0))
    (g : Torus 1 →ᵇ ℝ) :
    Tendsto (fun n => θ n * ∫ x, g x ∂(densityMeasure (ρ n) : Measure (Torus 1)))
      atTop (𝓝 0) := by
  have hb (n : ℕ) : |∫ x, g x ∂(densityMeasure (ρ n) : Measure (Torus 1))| ≤ ‖g‖ := by
    simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := (densityMeasure (ρ n) : Measure (Torus 1)))
        (Eventually.of_forall fun x => g.norm_coe_le_norm x))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => show ‖θ n * ∫ x, g x ∂(densityMeasure (ρ n) : Measure (Torus 1))‖ ≤ θ n * ‖g‖ from ?_)
    (by simpa using ht.mul_const ‖g‖)
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hθ n), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hb n) (hθ n)

/-- The existing one-dimensional root convergence controls every bounded
continuous moment of the actual density measure. -/
theorem densityMoment_tendsto_of_uniform_root {ρ : ℕ → AbsoluteDensity 1}
    {ρL : AbsoluteDensity 1} {ε : ℕ → ℝ} {R : ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ ε n)
    (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R) (g : Torus 1 →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, g x ∂(densityMeasure (ρ n) : Measure (Torus 1))) atTop
      (𝓝 (∫ x, g x ∂(densityMeasure ρL : Measure (Torus 1)))) := by
  have hpt : ∀ᵐ x ∂haar 1,
      Tendsto (fun n => (ρ n).sqrt x) atTop (𝓝 (ρL.sqrt x)) := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs]
      exact hx n) hε
  simp_rw [Structural.budget_integral_densityMeasure]
  exact tendsto_integral_comp_mul (T := fun t : ℝ => t ^ 2) (continuous_pow 2) g.continuous
    (fun x => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x)
    (fun n => (ρ n).memLp_sqrt.aestronglyMeasurable) hub hpt

private theorem finite_sum_liminf_ennreal_le {ι : Type*} [Fintype ι]
    (a : ℕ → ι → ℝ≥0∞) :
    (∑ i, liminf (fun n => a n i) atTop) ≤ liminf (fun n => ∑ i, a n i) atTop := by
  classical
  letI : MeasurableSpace ι := ⊤
  have hfat := lintegral_liminf_le (μ := Measure.count) (u := atTop) (f := a)
    (fun n => (Measurable.of_discrete : Measurable (a n)))
  simpa only [lintegral_fintype, Measure.count_singleton, mul_one] using hfat

/-- Native weighted-information lower semicontinuity discards zero-limit labels
by nonnegativity. The positive-label gradient LSC is derived from actual root
convergence, rather than imposed as a conclusion assumption. -/
theorem finite_weighted_ordinaryFisher_lsc {ι : Type*} [Fintype ι]
    (h : ℝ) (θ : ℕ → ι → ℝ) (θL : ι → ℝ)
    (ρ : ℕ → ι → AbsoluteDensity 1) (ρL : ι → AbsoluteDensity 1)
    (hθ : ∀ n i, 0 ≤ θ n i) (hL0 : ∀ i, 0 ≤ θL i)
    (ht : ∀ i, Tendsto (fun n => θ n i) atTop (𝓝 (θL i)))
    (hroot : ∀ i, 0 < θL i → ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n, ∀ᵐ x ∂haar 1, |(ρ n i).sqrt x - (ρL i).sqrt x| ≤ ε n) :
    ENNReal.ofReal (∑ i, θL i * (ordinaryFisher h (ρL i)).toReal) ≤
      liminf (fun n => ENNReal.ofReal (∑ i, θ n i * (ordinaryFisher h (ρ n i)).toReal)) atTop := by
  classical
  have he (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (τ : ι → AbsoluteDensity 1) :
      ENNReal.ofReal (∑ i, w i * (ordinaryFisher h (τ i)).toReal) =
        ∑ i, ENNReal.ofReal (w i) * ordinaryFisher h (τ i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) ENNReal.toReal_nonneg)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_mul (hw i), ENNReal.ofReal_toReal (str025_fisher_ne_top h (τ i))]
  simp_rw [he θL hL0 ρL, he _ (hθ _) _]
  have hlabel (i : ι) : ENNReal.ofReal (θL i) * ordinaryFisher h (ρL i) ≤
      liminf (fun n => ENNReal.ofReal (θ n i) * ordinaryFisher h (ρ n i)) atTop := by
    by_cases hi : 0 < θL i
    · obtain ⟨ε, hε, hae⟩ := hroot i hi
      have hI := ordinaryFisher_le_liminf h (fun n => ρ n i) (ρL i) hε hae
      have htE := ENNReal.tendsto_ofReal (ht i)
      calc
        _ ≤ ENNReal.ofReal (θL i) * liminf (fun n => ordinaryFisher h (ρ n i)) atTop :=
          mul_le_mul' le_rfl hI
        _ = (liminf (fun n => ENNReal.ofReal (θ n i)) atTop) *
            liminf (fun n => ordinaryFisher h (ρ n i)) atTop := by rw [htE.liminf_eq]
        _ ≤ _ := ENNReal.le_liminf_mul
    · have hz : θL i = 0 := le_antisymm (not_lt.mp hi) (hL0 i)
      simp only [hz, ENNReal.ofReal_zero, zero_mul]
      exact bot_le
  exact (Finset.sum_le_sum fun i _ => hlabel i).trans (finite_sum_liminf_ennreal_le _)

/-- Bounded weighted actual information gives finite-label compactness, including
vanishing weights. Zero-limit labels are genuinely removed into a strict-positive
actual family. This theorem deliberately makes no positive-gap or attainment claim. -/
theorem finite_species_weighted_information_compactness {ι : Type*} [Fintype ι]
    (h : ℝ) (θ : ℕ → ι → ℝ) (ρ : ℕ → ι → AbsoluteDensity 1)
    (hθ : ∀ n i, 0 ≤ θ n i) (hmass : ∀ n, ∑ i, θ n i = 1) {C : ℝ}
    (hI : ∀ n, ∑ i, θ n i * (ordinaryFisher h (ρ n i)).toReal ≤ C) :
    ∃ (φ : ℕ → ℕ) (θL : ι → ℝ) (G : SpeciesFamily 1) (σ : Fin G.count → ι),
      StrictMono φ ∧ (∀ i, 0 ≤ θL i) ∧ (∑ i, θL i = 1) ∧
      (∀ i, Tendsto (fun n => θ (φ n) i) atTop (𝓝 (θL i))) ∧
      (G.count : ℕ) ≤ Fintype.card ι ∧ Function.Injective σ ∧
      (∀ j, G.weight j = θL (σ j)) ∧ (∀ i, 0 < θL i → ∃ j, σ j = i) ∧
      (∀ j, ∃ (ε : ℕ → ℝ) (R : ℝ), Tendsto ε atTop (𝓝 0) ∧
        (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n) (σ j)).sqrt x - (G.density j).sqrt x| ≤ ε n) ∧
        (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n) (σ j)).sqrt x| ≤ R) ∧
        Tendsto (fun n => ordinaryEntropy h (ρ (φ n) (σ j))) atTop
          (𝓝 (ordinaryEntropy h (G.density j))) ∧
        ordinaryFisher h (G.density j) ≤
          liminf (fun n => ordinaryFisher h (ρ (φ n) (σ j))) atTop) ∧
      Tendsto (fun n => ∑ i, θ (φ n) i * (ordinaryEntropy h (ρ (φ n) i)).toReal) atTop
        (𝓝 (∑ j, G.weight j * (ordinaryEntropy h (G.density j)).toReal)) ∧
      ENNReal.ofReal (∑ j, G.weight j * (ordinaryFisher h (G.density j)).toReal) ≤
        liminf (fun n => ENNReal.ofReal (∑ i, θ (φ n) i *
          (ordinaryFisher h (ρ (φ n) i)).toReal)) atTop ∧
      (∀ g : Torus 1 →ᵇ ℝ,
        Tendsto (fun n => ∑ i, θ (φ n) i *
          ∫ x, g x ∂(densityMeasure (ρ (φ n) i) : Measure (Torus 1))) atTop
          (𝓝 (∫ x, g x ∂(densityMeasure (barycenter G) : Measure (Torus 1))))) := by
  classical
  have hInd (n : ℕ) (i : ι) : θ n i * (ordinaryFisher h (ρ n i)).toReal ≤ C :=
    (Finset.single_le_sum (f := fun j => θ n j * (ordinaryFisher h (ρ n j)).toReal)
      (fun j _ => mul_nonneg (hθ n j) ENNReal.toReal_nonneg)
      (Finset.mem_univ i)).trans (hI n)
  obtain ⟨ψ, θL, hψ, hL0, hLmass, hL⟩ := finite_simplex_weight_subsequence θ hθ hmass
  obtain ⟨χ, hχ, hroots⟩ := finite_positive_weight_root_compactness h
    (fun n i => θ (ψ n) i) (fun n i => ρ (ψ n) i) θL hL (fun n i => hInd (ψ n) i)
  let φ := ψ ∘ χ
  have hφ : StrictMono φ := hψ.comp hχ
  have hlim (i : ι) : Tendsto (fun n => θ (φ n) i) atTop (𝓝 (θL i)) :=
    (hL i).comp hχ.tendsto_atTop
  let ρL : ι → AbsoluteDensity 1 := fun i =>
    if hi : 0 < θL i then (hroots i hi).choose else ρ 0 i
  have hroot (i : ι) (hi : 0 < θL i) :
      ∃ (ε : ℕ → ℝ) (R : ℝ), Tendsto ε atTop (𝓝 0) ∧
        (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n) i).sqrt x - (ρL i).sqrt x| ≤ ε n) ∧
        (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n) i).sqrt x| ≤ R) ∧ (∀ x, |(ρL i).sqrt x| ≤ R) ∧
        Tendsto (fun n => ordinaryEntropy h (ρ (φ n) i)) atTop (𝓝 (ordinaryEntropy h (ρL i))) ∧
        ordinaryFisher h (ρL i) ≤ liminf (fun n => ordinaryFisher h (ρ (φ n) i)) atTop := by
    simpa only [ρL, dite_eq_left hi, φ, Function.comp_def] using (hroots i hi).choose_spec
  let s := Finset.univ.filter fun i => 0 < θL i
  have hs : s.Nonempty := by
    by_contra hn
    have hz (i : ι) : θL i = 0 := by
      have hp : ¬0 < θL i := fun hi => hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
      exact le_antisymm (not_lt.mp hp) (hL0 i)
    simp only [hz, Finset.sum_const_zero] at hLmass
    norm_num at hLmass
  letI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have hcard : 0 < Fintype.card s := Fintype.card_pos_iff.mpr inferInstance
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let σ : Fin (Fintype.card s) → ι := fun j => (e j).val
  have hstat (f : ι → ℝ) : ∑ j, θL (σ j) * f (σ j) = ∑ i, θL i * f i := by
    calc
      _ = ∑ i : s, θL i.val * f i.val := e.sum_comp (fun i : s => θL i.val * f i.val)
      _ = ∑ i ∈ s, θL i * f i := Finset.sum_coe_sort s (fun i => θL i * f i)
      _ = _ := Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by
        have hp : ¬0 < θL i := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
        rw [le_antisymm (not_lt.mp hp) (hL0 i), zero_mul]
  let G : SpeciesFamily 1 :=
    { count := ⟨Fintype.card s, hcard⟩
      weight := fun j => θL (σ j)
      weight_pos := fun j => (Finset.mem_filter.mp (e j).property).2
      weight_sum := by
        change (∑ j : Fin (Fintype.card s), θL (σ j)) = 1
        have hh := hstat (fun _ => 1)
        simpa only [mul_one, hLmass] using hh
      density := fun j => ρL (σ j) }
  have hcount : (G.count : ℕ) ≤ Fintype.card ι := by
    change Fintype.card s ≤ Fintype.card ι
    rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.subset_univ s)).trans_eq Finset.card_univ
  have hσ : Function.Injective σ := fun i j hij => e.injective (Subtype.ext hij)
  have hsurj : ∀ i, 0 < θL i → ∃ j, σ j = i := by
    intro i hi
    let v : s := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    exact ⟨e.symm v, congrArg Subtype.val (e.apply_symm_apply v)⟩
  have hent (i : ι) : Tendsto (fun n => θ (φ n) i * (ordinaryEntropy h (ρ (φ n) i)).toReal)
      atTop (𝓝 (θL i * (ordinaryEntropy h (ρL i)).toReal)) := by
    by_cases hi : 0 < θL i
    · obtain ⟨ε, R, hε, hae, hub, hLb, hH, hIl⟩ := hroot i hi
      exact (hlim i).mul ((ENNReal.tendsto_toReal (str025_entropy_ne_top h (ρL i))).comp hH)
    · have hz : θL i = 0 := le_antisymm (not_lt.mp hi) (hL0 i)
      simpa only [hz, zero_mul] using ordinaryEntropy_vanishing_weight h
        (fun n => θ (φ n) i) (fun n => ρ (φ n) i) (fun n => hθ (φ n) i)
        (by simpa only [hz] using hlim i) (fun n => hInd (φ n) i)
  have hsumH : Tendsto (fun n => ∑ i, θ (φ n) i * (ordinaryEntropy h (ρ (φ n) i)).toReal)
      atTop (𝓝 (∑ j, G.weight j * (ordinaryEntropy h (G.density j)).toReal)) := by
    have ht := tendsto_finsetSum Finset.univ (fun i _ => hent i)
    have he : (∑ j, G.weight j * (ordinaryEntropy h (G.density j)).toReal) =
        ∑ i, θL i * (ordinaryEntropy h (ρL i)).toReal := by
      change (∑ j : Fin (Fintype.card s), θL (σ j) * (ordinaryEntropy h (ρL (σ j))).toReal) = _
      exact hstat (fun i => (ordinaryEntropy h (ρL i)).toReal)
    rw [he]
    exact ht
  refine ⟨φ, θL, G, σ, hφ, hL0, hLmass, hlim, hcount, hσ,
    fun _ => rfl, hsurj, ?_, hsumH, ?_, ?_⟩
  · intro j
    obtain ⟨ε, R, hε, hae, hub, hLb, hH, hIl⟩ := hroot (σ j) (G.weight_pos j)
    exact ⟨ε, R, hε, hae, hub, hH, hIl⟩
  · have hLSC := finite_weighted_ordinaryFisher_lsc h
      (fun n i => θ (φ n) i) θL (fun n i => ρ (φ n) i) ρL
      (fun n i => hθ (φ n) i) hL0 hlim (fun i hi => by
        obtain ⟨ε, R, hε, hae, hub, hLb, hH, hIl⟩ := hroot i hi
        exact ⟨ε, hε, hae⟩)
    change ENNReal.ofReal (∑ j, θL (σ j) * (ordinaryFisher h (ρL (σ j))).toReal) ≤ _
    rw [hstat (fun i => (ordinaryFisher h (ρL i)).toReal)]
    exact hLSC
  · intro g
    have hmoment (i : ι) : Tendsto (fun n => θ (φ n) i *
        ∫ x, g x ∂(densityMeasure (ρ (φ n) i) : Measure (Torus 1))) atTop
        (𝓝 (θL i * ∫ x, g x ∂(densityMeasure (ρL i) : Measure (Torus 1)))) := by
      by_cases hi : 0 < θL i
      · obtain ⟨ε, R, hε, hae, hub, hLb, hH, hIl⟩ := hroot i hi
        exact (hlim i).mul (densityMoment_tendsto_of_uniform_root hε hae hub g)
      · have hz : θL i = 0 := le_antisymm (not_lt.mp hi) (hL0 i)
        simpa only [hz, zero_mul] using densityMoment_vanishing_weight
          (fun n => θ (φ n) i) (fun n => ρ (φ n) i) (fun n => hθ (φ n) i)
          (by simpa only [hz] using hlim i) g
    have he : (∑ i, θL i * ∫ x, g x ∂(densityMeasure (ρL i) : Measure (Torus 1))) =
        ∫ x, g x ∂(densityMeasure (barycenter G) : Measure (Torus 1)) := by
      rw [Structural.budget_integral_barycenter G g.continuous]
      exact (hstat (fun i => ∫ x, g x ∂(densityMeasure (ρL i) : Measure (Torus 1)))).symm
    rw [← he]
    exact tendsto_finsetSum Finset.univ (fun i _ => hmoment i)

/-- The finite-label compactness result for an actual sequence of fixed-count
SpeciesFamily records. It retains actual original-coordinate roots and produces
an actual strict-positive limit family; zero limiting weights have been removed. -/
theorem fixedCount_species_weighted_information_compactness (h : ℝ) (k : ℕ+)
    (F : ℕ → SpeciesFamily 1) (hcount : ∀ n, (F n).count = k) {C : ℝ}
    (hI : ∀ n, ∑ i, (F n).weight i * (ordinaryFisher h ((F n).density i)).toReal ≤ C) :
    ∃ (φ : ℕ → ℕ) (G : SpeciesFamily 1) (σ : Fin G.count → Fin k),
      StrictMono φ ∧ (G.count : ℕ) ≤ k ∧ Function.Injective σ ∧
      (∀ j, ∃ (ε : ℕ → ℝ) (R : ℝ), Tendsto ε atTop (𝓝 0) ∧
        (∀ n, ∀ᵐ x ∂haar 1,
          |((F (φ n)).density (Fin.cast (congrArg PNat.val (hcount (φ n))).symm (σ j))).sqrt x -
            (G.density j).sqrt x| ≤ ε n) ∧
        (∀ n, ∀ᵐ x ∂haar 1,
          |((F (φ n)).density (Fin.cast (congrArg PNat.val (hcount (φ n))).symm (σ j))).sqrt x| ≤ R)) ∧
      Tendsto (fun n => ∑ i, (F (φ n)).weight i *
          (ordinaryEntropy h ((F (φ n)).density i)).toReal) atTop
        (𝓝 (∑ j, G.weight j * (ordinaryEntropy h (G.density j)).toReal)) ∧
      ENNReal.ofReal (∑ j, G.weight j * (ordinaryFisher h (G.density j)).toReal) ≤
        liminf (fun n => ENNReal.ofReal (∑ i, (F (φ n)).weight i *
          (ordinaryFisher h ((F (φ n)).density i)).toReal)) atTop ∧
      (∀ g : Torus 1 →ᵇ ℝ,
        Tendsto (fun n => ∫ x, g x ∂(densityMeasure (barycenter (F (φ n))) : Measure (Torus 1))) atTop
          (𝓝 (∫ x, g x ∂(densityMeasure (barycenter G) : Measure (Torus 1))))) := by
  classical
  let e (n : ℕ) : Fin k ≃ Fin (F n).count := finCongr (congrArg PNat.val (hcount n)).symm
  let θ : ℕ → Fin k → ℝ := fun n i => (F n).weight (e n i)
  let ρ : ℕ → Fin k → AbsoluteDensity 1 := fun n i => (F n).density (e n i)
  have hm (n : ℕ) : ∑ i, θ n i = 1 := by
    change (∑ i, (F n).weight (e n i)) = 1
    rw [(e n).sum_comp, (F n).weight_sum]
  have hsum (n : ℕ) (L : AbsoluteDensity 1 → ℝ) :
      (∑ i, θ n i * L (ρ n i)) = ∑ s, (F n).weight s * L ((F n).density s) :=
    (e n).sum_comp (fun s => (F n).weight s * L ((F n).density s))
  have hI' (n : ℕ) : ∑ i, θ n i * (ordinaryFisher h (ρ n i)).toReal ≤ C := by
    rw [hsum n (fun τ => (ordinaryFisher h τ).toReal)]
    exact hI n
  obtain ⟨φ, θL, G, σ, hφ, hL0, hmass, ht, hc, hσ, hw, hsurj, hroot, hH, hIl, hM⟩ :=
    finite_species_weighted_information_compactness h θ ρ
      (fun n i => (F n).weight_nonneg (e n i)) hm hI'
  refine ⟨φ, G, σ, hφ, by simpa only [Fintype.card_fin] using hc, hσ, ?_, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨ε, R, hε, hae, hub, hHj, hIj⟩ := hroot j
    exact ⟨ε, R, hε, hae, hub⟩
  · simpa only [hsum _ (fun τ => (ordinaryEntropy h τ).toReal)] using hH
  · simpa only [hsum _ (fun τ => (ordinaryFisher h τ).toReal)] using hIl
  · intro g
    have he (n : ℕ) : (∑ i, θ n i * ∫ x, g x ∂(densityMeasure (ρ n i) : Measure (Torus 1))) =
        ∫ x, g x ∂(densityMeasure (barycenter (F n)) : Measure (Torus 1)) := by
      rw [hsum n (fun τ => ∫ x, g x ∂(densityMeasure τ : Measure (Torus 1))),
        Structural.budget_integral_barycenter (F n) g.continuous]
    simpa only [he] using hM g

/-- A sequence of actual families with count at most four has a common fixed-count
subsequence. This changes no weights and imposes no positive lower bound on them. -/
theorem species_count_subsequence_four (F : ℕ → SpeciesFamily 1)
    (hcount : ∀ n, ((F n).count : ℕ) ≤ 4) :
    ∃ k : ℕ+, (k : ℕ) ≤ 4 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, (F (φ n)).count = k := by
  let c : ℕ → Fin 5 := fun n => ⟨(F n).count, by have := hcount n; omega⟩
  have hf : ∃ᶠ n in atTop, ∃ k : Fin 5, c n = k :=
    (Eventually.of_forall fun n => show ∃ k : Fin 5, c n = k from ⟨c n, rfl⟩).frequently
  obtain ⟨k, hk⟩ := frequently_exists.mp hf
  obtain ⟨φ, hφ, heq⟩ := extraction_of_frequently_atTop hk
  have he (n : ℕ) : ((F (φ n)).count : ℕ) = k.val := congrArg Fin.val (heq n)
  have hpos : 0 < k.val := by rw [← he 0]; exact (F (φ 0)).count.property
  refine ⟨⟨k.val, hpos⟩, ?_, φ, hφ, fun n => ?_⟩
  · change k.val ≤ 4
    rw [← he 0]
    exact hcount (φ 0)
  · apply Subtype.ext
    exact he n

private theorem speciesDissipation_lsc_of_correction_tendsto (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (F : ℕ → SpeciesFamily 1) (G : SpeciesFamily 1) {C : ℝ}
    (hI : ∀ n, ∑ i, (F n).weight i * (ordinaryFisher h ((F n).density i)).toReal ≤ C)
    (hIl : ENNReal.ofReal (∑ j, G.weight j * (ordinaryFisher h (G.density j)).toReal) ≤
      liminf (fun n => ENNReal.ofReal (∑ i, (F n).weight i *
        (ordinaryFisher h ((F n).density i)).toReal)) atTop)
    (hCorr : Tendsto (fun n => 2 * ε * (∫ x, (barycenter (F n)).density x *
        elementaryAK h (densityMeasure (barycenter (F n))) x ∂haar 1) +
        ε ^ 2 * elementaryJ h (barycenter (F n))) atTop
      (𝓝 (2 * ε * (∫ x, (barycenter G).density x *
        elementaryAK h (densityMeasure (barycenter G)) x ∂haar 1) +
        ε ^ 2 * elementaryJ h (barycenter G)))) :
    speciesDissipation (modelData h ε) b G ≤
      liminf (fun n => speciesDissipation (modelData h ε) b (F n)) atTop := by
  let I (F : SpeciesFamily 1) := ∑ i, F.weight i * (ordinaryFisher h (F.density i)).toReal
  let R (F : SpeciesFamily 1) := 2 * ε * (∫ x, (barycenter F).density x *
    elementaryAK h (densityMeasure (barycenter F)) x ∂haar 1) + ε ^ 2 * elementaryJ h (barycenter F)
  have hI0 (F : SpeciesFamily 1) : 0 ≤ I F :=
    Finset.sum_nonneg fun i _ => mul_nonneg (F.weight_nonneg i) ENNReal.toReal_nonneg
  have hR : Tendsto (fun n => R (F n)) atTop (𝓝 (R G)) := hCorr
  have hD (F : SpeciesFamily 1) : speciesDissipation (modelData h ε) b F ≠ ⊤ :=
    (elementaryModel_speciesDissipation_expansion h ε b F).1
  have hDeq (F : SpeciesFamily 1) : (speciesDissipation (modelData h ε) b F).toReal = I F + R F := by
    have he := (elementaryModel_speciesDissipation_expansion h ε b F).2
    dsimp only [I, R]
    linarith
  have hIB : ∀ᶠ n in atTop, ENNReal.ofReal (I (F n)) ≤ ENNReal.ofReal C :=
    Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal (hI n)
  have hIlfin : liminf (fun n => ENNReal.ofReal (I (F n))) atTop ≠ ⊤ := by
    refine ne_top_of_le_ne_top (show ENNReal.ofReal C ≠ ⊤ from ENNReal.ofReal_ne_top) ?_
    exact (liminf_le_liminf hIB).trans (by simp)
  have hIr : I G ≤ liminf (fun n => I (F n)) atTop := by
    have hh := ENNReal.toReal_mono hIlfin hIl
    rw [ENNReal.toReal_ofReal (hI0 G),
      ← ENNReal.liminf_toReal_eq ENNReal.ofReal_ne_top hIB] at hh
    simpa only [ENNReal.toReal_ofReal (hI0 _)] using hh
  have hIbelow : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop (fun n => I (F n)) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n : ℕ in atTop, 0 ≤ I (F n)
    exact Eventually.of_forall fun n => hI0 (F n)
  have hIabove : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop (fun n => I (F n)) := by
    refine ⟨C, ?_⟩
    change ∀ᶠ n : ℕ in atTop, I (F n) ≤ C
    exact Eventually.of_forall hI
  have hAdd := le_liminf_add hIbelow hIabove hR.isBoundedUnder_ge
    hR.isBoundedUnder_le.isCoboundedUnder_ge
  rw [hR.liminf_eq] at hAdd
  have hDr : (speciesDissipation (modelData h ε) b G).toReal ≤
      liminf (fun n => (speciesDissipation (modelData h ε) b (F n)).toReal) atTop := by
    simp_rw [hDeq]
    exact (add_le_add hIr (le_refl (R G))).trans hAdd
  obtain ⟨B, hB⟩ := hR.isBoundedUnder_le.bddAbove_range
  have hDB : ∀ᶠ n in atTop, speciesDissipation (modelData h ε) b (F n) ≤ ENNReal.ofReal (C + B) := by
    refine Eventually.of_forall fun n => ?_
    rw [← ENNReal.ofReal_toReal (hD (F n))]
    apply ENNReal.ofReal_le_ofReal
    rw [hDeq]
    exact add_le_add (hI n) (hB ⟨n, rfl⟩)
  have hDlfin : liminf (fun n => speciesDissipation (modelData h ε) b (F n)) atTop ≠ ⊤ := by
    refine ne_top_of_le_ne_top (show ENNReal.ofReal (C + B) ≠ ⊤ from ENNReal.ofReal_ne_top) ?_
    exact (liminf_le_liminf hDB).trans (by simp)
  have hh := ENNReal.ofReal_le_ofReal hDr
  rw [ENNReal.ofReal_toReal (hD G), ENNReal.liminf_toReal_eq ENNReal.ofReal_ne_top hDB,
    ENNReal.ofReal_toReal hDlfin] at hh
  exact hh

/-- Actual changing-force family dissipation is lower semicontinuous at the
constructed reference-compact limit. The correction limit is proved from actual
bounded-continuous barycenter moments, not assumed. No positive limit gap is needed. -/
theorem elementary_speciesDissipation_lsc (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (F : ℕ → SpeciesFamily 1) (G : SpeciesFamily 1) {C : ℝ}
    (hI : ∀ n, ∑ i, (F n).weight i * (ordinaryFisher h ((F n).density i)).toReal ≤ C)
    (hIl : ENNReal.ofReal (∑ j, G.weight j * (ordinaryFisher h (G.density j)).toReal) ≤
      liminf (fun n => ENNReal.ofReal (∑ i, (F n).weight i *
        (ordinaryFisher h ((F n).density i)).toReal)) atTop)
    (hweak : ∀ g : Torus 1 →ᵇ ℝ,
      Tendsto (fun n => ∫ x, g x ∂(densityMeasure (barycenter (F n)) : Measure (Torus 1))) atTop
        (𝓝 (∫ x, g x ∂(densityMeasure (barycenter G) : Measure (Torus 1))))) :
    speciesDissipation (modelData h ε) b G ≤
      liminf (fun n => speciesDissipation (modelData h ε) b (F n)) atTop :=
  speciesDissipation_lsc_of_correction_tendsto h ε b F G hI hIl
    (elementary_deficit_correction_tendsto h ε (fun n => barycenter (F n)) (barycenter G) hweak)

/-- Convergence of the actual family gap follows from total ordinary entropy and
the actual three barycenter moments. It makes no positivity claim for the limit. -/
theorem elementary_speciesGap_tendsto {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (F : ℕ → SpeciesFamily 1) (G : SpeciesFamily 1)
    (hH : Tendsto (fun n => ∑ i, (F n).weight i *
        (ordinaryEntropy h ((F n).density i)).toReal) atTop
      (𝓝 (∑ i, G.weight i * (ordinaryEntropy h (G.density i)).toReal)))
    (hweak : ∀ g : Torus 1 →ᵇ ℝ,
      Tendsto (fun n => ∫ x, g x ∂(densityMeasure (barycenter (F n)) : Measure (Torus 1))) atTop
        (𝓝 (∫ x, g x ∂(densityMeasure (barycenter G) : Measure (Torus 1))))) :
    Tendsto (fun n => (speciesGap (modelData h ε) (F n) : ℝ)) atTop
      (𝓝 (speciesGap (modelData h ε) G : ℝ)) := by
  have hC := hweak (BoundedContinuousFunction.mkOfCompact ⟨featureC h, featureC_continuous h⟩)
  have hS := hweak (BoundedContinuousFunction.mkOfCompact ⟨featureS h, featureS_continuous h⟩)
  have hB := hweak (BoundedContinuousFunction.mkOfCompact ⟨featureB h, featureB_continuous h⟩)
  have hQ : Tendsto (fun n => elementaryQ h (densityMeasure (barycenter (F n)))) atTop
      (𝓝 (elementaryQ h (densityMeasure (barycenter G)))) := by
    simp_rw [elementaryQ_moments]
    exact (((hC.pow 2).add (hS.pow 2)).const_mul kAlpha).sub ((hB.pow 2).const_mul kBeta)
  simp_rw [elementaryModel_speciesGap_expansion hh hε hεmax]
  exact hH.add (hQ.const_mul (ε / 2))

/-- Actual bounded-quotient sequences of families with at most four species are
compact after deleting zero limiting weights. The limit has convergent actual gap
and lower semicontinuous actual dissipation. Its gap may be zero; excluding that
case and proving attainment are separate mathematical steps. -/
theorem elementaryModel_boundedQuotient_family_compactness {h : ℝ} (hh : 0 < h) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (b : AbsoluteDrift (modelData h ε)) (M : ℝ), 0 ≤ M →
        ∀ F : ℕ → SpeciesFamily 1,
          (∀ n, ((F n).count : ℕ) ≤ 4) →
          (∀ n, 0 < speciesGap (modelData h ε) (F n)) →
          (∀ n, speciesQuotient (modelData h ε) b (F n) ≤ ENNReal.ofReal M) →
          ∃ (φ : ℕ → ℕ) (G : SpeciesFamily 1), StrictMono φ ∧ (G.count : ℕ) ≤ 4 ∧
            Tendsto (fun n => (speciesGap (modelData h ε) (F (φ n)) : ℝ)) atTop
              (𝓝 (speciesGap (modelData h ε) G : ℝ)) ∧
            speciesDissipation (modelData h ε) b G ≤
              liminf (fun n => speciesDissipation (modelData h ε) b (F (φ n))) atTop ∧
            Tendsto (fun n => ∑ i, (F (φ n)).weight i *
                (ordinaryEntropy h ((F (φ n)).density i)).toReal) atTop
              (𝓝 (∑ i, G.weight i * (ordinaryEntropy h (G.density i)).toReal)) ∧
            (∀ g : Torus 1 →ᵇ ℝ,
              Tendsto (fun n => ∫ x, g x ∂(densityMeasure (barycenter (F (φ n))) : Measure (Torus 1))) atTop
                (𝓝 (∫ x, g x ∂(densityMeasure (barycenter G) : Measure (Torus 1))))) := by
  obtain ⟨ε0, hε0, hεmax, hinfo⟩ := elementaryModel_boundedQuotient_weighted_information hh
  refine ⟨ε0, hε0, hεmax, fun ε hε hε0' b M hM F hcount hpos hq => ?_⟩
  obtain ⟨C, hC, hI⟩ := hinfo ε hε hε0' b M hM
  have hIFn (n : ℕ) : ∑ i, (F n).weight i * (ordinaryFisher h ((F n).density i)).toReal ≤ C :=
    hI (F n) (hpos n) (hq n)
  obtain ⟨k, hk, ψ, hψ, hψcount⟩ := species_count_subsequence_four F hcount
  obtain ⟨χ, G, σ, hχ, hGc, hσ, hroot, hH, hIl, hweak⟩ :=
    fixedCount_species_weighted_information_compactness h k (fun n => F (ψ n)) hψcount
      (fun n => hIFn (ψ n))
  let φ := ψ ∘ χ
  have hgap := elementary_speciesGap_tendsto hh hε (hε0'.trans_le hεmax)
    (fun n => F (φ n)) G hH hweak
  have hD := elementary_speciesDissipation_lsc h ε b (fun n => F (φ n)) G
    (fun n => hIFn (φ n)) hIl hweak
  exact ⟨φ, G, hψ.comp hχ, hGc.trans hk, hgap, hD, hH, hweak⟩

end DGPS.Examples.ThreeSpeciesCircle
