import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Set Function MeasureTheory Real
open scoped ContDiff Manifold

/-!
# FIN020: fixed partition IMS localization

Module `DGPS.FiniteN.Tools.IMS` (placed in a new file instead of `DGPS/FiniteN/Tools.lean`
to avoid file contention). On `ℝ^k = EuclideanSpace ℝ (Fin k)`, for a smooth `ψ` and finitely
many fixed bounded open neighborhoods `U j` covering the critical set of `ψ`, there is a smooth
quadratic partition of unity `χ : Option (Fin m) → ℝ^k → ℝ` (`none` is the exterior cutoff,
supported where `∇ψ ≠ 0`), with `χ (some j)` supported in `U j`, the cutoff `χ (some j₀)` equal to
one on a smaller set `V` (`closure V ⊆ U j₀`; `j₀` is the neighborhood of the global minimum),
and `∑ ‖∇χ_j‖² ≤ C`, such that for every `N`, with `η_N ∝ e^{-Nψ}`,
`∑_j E(χ_j F) = E(F) + ∫ ∑‖∇χ_j‖² F² dη_N`, `E(F) = ∫ ‖∇F‖² dη_N`, and the localization error is
`≤ C ∫ F² dη_N` independently of `N`.
-/

namespace DGPS.FiniteN


theorem ims_exists_partition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (U : ι → Set E) (ho : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) :
    ∃ p : ι → E → ℝ, (∀ i, ContDiff ℝ ∞ (p i)) ∧ (∀ i x, 0 ≤ p i x) ∧
      (∀ x, ∑ i, p i x = 1) ∧ ∀ i, tsupport (p i) ⊆ U i := by
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) (isClosed_univ (X := E)) U ho
    (by rw [hcov])
  refine ⟨fun i => f i, fun i => contMDiff_iff_contDiff.mp (f i).contMDiff, fun i x => f.nonneg i x,
    fun x => ?_, hf⟩
  have := f.sum_eq_one (Set.mem_univ x)
  rwa [finsum_eq_sum_of_fintype] at this

/-- Normalization of a partition of unity to a quadratic one. -/
theorem ims_normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (p : ι → E → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (hp0 : ∀ i x, 0 ≤ p i x) (hp1 : ∀ x, ∑ i, p i x = 1) :
    ∃ χ : ι → E → ℝ, (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ x, ∑ i, χ i x ^ 2 = 1) ∧
      (∀ i, support (χ i) = support (p i)) ∧
      (∀ x i₁, (∀ i, i ≠ i₁ → p i x = 0) → χ i₁ x = 1) := by
  classical
  have hs : ∀ x, 0 < ∑ k, p k x ^ 2 := by
    intro x
    have : ∃ i, 0 < p i x := by
      by_contra h
      push Not at h
      have h0 : ∀ i, p i x = 0 := fun i => le_antisymm (h i) (hp0 i x)
      have := hp1 x
      simp [h0] at this
    obtain ⟨i, hi⟩ := this
    exact Finset.sum_pos' (fun k _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩
  have hsm : ContDiff ℝ ∞ (fun x => ∑ k, p k x ^ 2) :=
    ContDiff.sum fun k _ => (hp k).pow 2
  have hsq : ContDiff ℝ ∞ (fun x => Real.sqrt (∑ k, p k x ^ 2)) :=
    hsm.sqrt (fun x => (hs x).ne')
  have hpos : ∀ x, 0 < Real.sqrt (∑ k, p k x ^ 2) := fun x => Real.sqrt_pos.mpr (hs x)
  refine ⟨fun i x => p i x / Real.sqrt (∑ k, p k x ^ 2), fun i => (hp i).div hsq
    (fun x => (hpos x).ne'), fun x => ?_, fun i => ?_, fun x i₁ h => ?_⟩
  · simp only [div_pow]
    rw [← Finset.sum_div, Real.sq_sqrt (hs x).le, div_self (hs x).ne']
  · ext x
    simp [Function.mem_support, (hpos x).ne']
  · have h1 : p i₁ x = 1 := by
      have := hp1 x
      rw [Finset.sum_eq_single i₁ (fun i _ hi => h i hi) (by simp)] at this
      exact this
    have h2 : ∑ k, p k x ^ 2 = 1 := by
      rw [Finset.sum_eq_single i₁ (fun i _ hi => by simp [h i hi]) (by simp), h1]; norm_num
    simp [h1, h2]

theorem ims_cutoffs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {m : ℕ} (U : Fin m → Set E) (hU : ∀ j, IsOpen (U j)) (hUc : ∀ j, IsCompact (closure (U j)))
    (W : Set E) (hW : IsOpen W) (hcov : Wᶜ ⊆ ⋃ j, U j) (j₀ : Fin m) (V : Set E)
    (hV : closure V ⊆ U j₀) :
    ∃ χ : Option (Fin m) → E → ℝ, (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ x, ∑ i, χ i x ^ 2 = 1) ∧
      (∀ j, tsupport (χ (some j)) ⊆ U j) ∧ tsupport (χ none) ⊆ W ∧
      (∀ x ∈ V, χ (some j₀) x = 1) ∧ ∃ C : ℝ, ∀ x, ∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2 ≤ C := by
  classical
  let U' : Option (Fin m) → Set E := fun i =>
    match i with
    | none => W \ closure V
    | some j => if j = j₀ then U j else U j \ closure V
  have hU' : ∀ i, IsOpen (U' i) := by
    intro i
    cases i with
    | none => exact hW.sdiff isClosed_closure
    | some j =>
      by_cases h : j = j₀
      · subst h; simpa [U'] using hU j
      · simpa [U', h] using (hU j).sdiff isClosed_closure
  have hcov' : ⋃ i, U' i = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ closure V
    · exact mem_iUnion.mpr ⟨some j₀, by simpa [U'] using hV hx⟩
    · by_cases hxW : x ∈ W
      · exact mem_iUnion.mpr ⟨none, hxW, hx⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov hxW)
        refine mem_iUnion.mpr ⟨some j, ?_⟩
        by_cases h : j = j₀
        · subst h; simpa [U'] using hj
        · simp [U', h, hj, hx]
  obtain ⟨p, hp, hp0, hp1, hpU⟩ := ims_exists_partition U' hU' hcov'
  obtain ⟨χ, hχ, hχ1, hsupp, hone⟩ := ims_normalize p hp hp0 hp1
  have htsupp : ∀ i, tsupport (χ i) = tsupport (p i) := fun i => by
    simp only [tsupport, hsupp i]
  have hUsub : ∀ j, U' (some j) ⊆ U j := by
    intro j; by_cases h : j = j₀ <;> simp [U', h]
  -- the compact set
  let Q : Set E := ⋃ j, closure (U j)
  have hQ : IsCompact Q := isCompact_iUnion hUc
  have hpQ : ∀ x, x ∉ Q → ∀ j, p (some j) x = 0 := by
    intro x hx j
    by_contra h
    exact hx (mem_iUnion.mpr ⟨j, subset_closure (hUsub j (hpU _ (subset_tsupport _ h)))⟩)
  have hQo : IsOpen Qᶜ := hQ.isClosed.isOpen_compl
  have hχQ : ∀ x, x ∉ Q → ∀ i, fderiv ℝ (χ i) x = 0 := by
    intro x hx i
    have hev : χ i =ᶠ[nhds x] fun _ => (if i = none then (1 : ℝ) else 0) := by
      filter_upwards [hQo.mem_nhds hx] with y hy
      have hy' : ∀ j, p (some j) y = 0 := hpQ y hy
      cases i with
      | none =>
        simpa using hone y none (fun i hi => by
          cases i with
          | none => exact absurd rfl hi
          | some j => exact hy' j)
      | some j =>
        have : support (χ (some j)) = support (p (some j)) := hsupp _
        by_contra hne
        have : y ∈ support (χ (some j)) := by simpa using hne
        rw [hsupp] at this
        exact this (hy' j)
    rw [hev.fderiv_eq]; simp
  refine ⟨χ, hχ, hχ1, fun j => ?_, ?_, fun x hx => ?_, ?_⟩
  · rw [htsupp]; exact (hpU _).trans (hUsub j)
  · rw [htsupp]; exact (hpU none).trans sdiff_subset
  · refine hone x (some j₀) fun i hi => ?_
    cases i with
    | none =>
      by_contra h
      exact (hpU none (subset_tsupport _ h)).2 (subset_closure hx)
    | some j =>
      by_contra h
      have := hpU _ (subset_tsupport _ h)
      have hj : j ≠ j₀ := fun e => hi (by rw [e])
      simp [U', hj] at this
      exact this.2 (subset_closure hx)
  · have hc : Continuous fun x => ∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2 :=
      continuous_finsetSum _ fun i _ =>
        ((hχ i).continuous_fderiv (by simp)).norm.pow 2
    obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ Q
    · exact (le_abs_self _).trans ((hC x hx).trans (le_max_left _ _))
    · simp [hχQ x hx]



theorem ims_pointwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (χ : ι → E → ℝ) (F : E → ℝ) (x : E)
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) x) (hF : DifferentiableAt ℝ F x)
    (hsum : ∀ y, ∑ i, χ i y ^ 2 = 1) :
    ∑ i, ‖fderiv ℝ (fun y => χ i y * F y) x‖ ^ 2 =
      ‖fderiv ℝ F x‖ ^ 2 + (∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2) * F x ^ 2 := by
  classical
  -- derivative of the constraint
  have hD : ∑ i, (2 * χ i x) • fderiv ℝ (χ i) x = 0 := by
    have h1 : HasFDerivAt (fun y => ∑ i, χ i y ^ 2)
        (∑ i, (2 * χ i x) • fderiv ℝ (χ i) x) x := by
      refine HasFDerivAt.fun_sum (fun i _ => ?_)
      have := (hχ i).hasFDerivAt.pow 2
      simpa using this
    have h2 : HasFDerivAt (fun y => ∑ i, χ i y ^ 2) (0 : E →L[ℝ] ℝ) x := by
      simp only [hsum]; exact hasFDerivAt_const _ _
    exact h1.unique h2
  let Φ := (InnerProductSpace.toDual ℝ E).symm
  have hΦ : ∀ φ : E →L[ℝ] ℝ, ‖Φ φ‖ = ‖φ‖ := fun φ => (InnerProductSpace.toDual ℝ E).symm.norm_map φ
  have hsumv : ∑ i, (2 * χ i x) • Φ (fderiv ℝ (χ i) x) = 0 := by
    have := congrArg Φ hD
    simpa [map_sum, map_smul] using this
  have hcross : ∑ i, χ i x * inner ℝ (Φ (fderiv ℝ F x)) (Φ (fderiv ℝ (χ i) x)) = 0 := by
    have := congrArg (fun v => inner ℝ (Φ (fderiv ℝ F x)) v) hsumv
    simp only [inner_sum, inner_smul_right, inner_zero_right] at this
    have h3 : ∑ i, 2 * (χ i x * inner ℝ (Φ (fderiv ℝ F x)) (Φ (fderiv ℝ (χ i) x))) = 0 := by
      rw [← this]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [← Finset.mul_sum] at h3
    linarith
  have hterm : ∀ i, ‖fderiv ℝ (fun y => χ i y * F y) x‖ ^ 2 =
      χ i x ^ 2 * ‖fderiv ℝ F x‖ ^ 2 + F x ^ 2 * ‖fderiv ℝ (χ i) x‖ ^ 2
        + 2 * F x * (χ i x * inner ℝ (Φ (fderiv ℝ F x)) (Φ (fderiv ℝ (χ i) x))) := by
    intro i
    rw [fderiv_fun_mul (hχ i) hF, ← hΦ, map_add, map_smul, map_smul, norm_add_sq_real,
      norm_smul, norm_smul, inner_smul_left, inner_smul_right, hΦ, hΦ]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial]
    ring
  simp only [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsum x, ← Finset.mul_sum, hcross]
  ring


/-- The normalized Gibbs measure `η_N ∝ e^{-Nψ} dx` on `ℝ^k`. -/
noncomputable def imsEta {k : ℕ} (N : ℝ) (ψ : EuclideanSpace ℝ (Fin k) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin k)) :=
  (∫⁻ x, ENNReal.ofReal (exp (-(N * ψ x)))) ⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
      (fun x => ENNReal.ofReal (exp (-(N * ψ x))))

/-- Integrated IMS identity and localization error bound, for an arbitrary measure `μ`. -/
theorem ims_integral_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    {ι : Type*} [Fintype ι] (χ : ι → E → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hsum : ∀ y, ∑ i, χ i y ^ 2 = 1) (C : ℝ) (hC : ∀ x, ∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2 ≤ C)
    (μ : Measure E) (F : E → ℝ) (hF : ContDiff ℝ 1 F)
    (h1 : Integrable (fun x => ‖fderiv ℝ F x‖ ^ 2) μ) (h2 : Integrable (fun x => F x ^ 2) μ) :
    ∑ i, ∫ x, ‖fderiv ℝ (fun y => χ i y * F y) x‖ ^ 2 ∂μ =
        ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂μ + ∫ x, (∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2) * F x ^ 2 ∂μ ∧
      ∫ x, (∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2) * F x ^ 2 ∂μ ≤ C * ∫ x, F x ^ 2 ∂μ := by
  have hχ1 : ∀ i, ContDiff ℝ 1 (χ i) := fun i => (hχ i).of_le (by exact_mod_cast le_top)
  have hdχ : ∀ i, Continuous fun x => ‖fderiv ℝ (χ i) x‖ ^ 2 := fun i =>
    ((hχ i).continuous_fderiv (by simp)).norm.pow 2
  have hG : Continuous fun x => ∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2 :=
    continuous_finsetSum _ fun i _ => hdχ i
  have hdF : Continuous fun x => ‖fderiv ℝ F x‖ ^ 2 := (hF.continuous_fderiv (by simp)).norm.pow 2
  have hFc : Continuous fun x => F x ^ 2 := hF.continuous.pow 2
  have hGF : Integrable (fun x => (∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2) * F x ^ 2) μ := by
    refine ((h2.const_mul C)).mono' (hG.mul hFc).aestronglyMeasurable (Filter.Eventually.of_forall
      fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hC x) (sq_nonneg _)
  have hpt : ∀ x, ∑ i, ‖fderiv ℝ (fun y => χ i y * F y) x‖ ^ 2 =
      ‖fderiv ℝ F x‖ ^ 2 + (∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2) * F x ^ 2 := fun x =>
    ims_pointwise χ F x (fun i => ((hχ1 i).differentiable (by simp)) x)
      ((hF.differentiable (by simp)) x) hsum
  have hint : ∀ i, Integrable (fun x => ‖fderiv ℝ (fun y => χ i y * F y) x‖ ^ 2) μ := by
    intro i
    have hcd : ContDiff ℝ 1 (fun y => χ i y * F y) := (hχ1 i).mul hF
    refine (h1.add hGF).mono' ((hcd.continuous_fderiv (by simp)).norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply, ← hpt x]
    exact Finset.single_le_sum (f := fun i => ‖fderiv ℝ (fun y => χ i y * F y) x‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  constructor
  · rw [← integral_finsetSum _ fun i _ => hint i, ← integral_add h1 hGF]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hpt x)
  · rw [← integral_const_mul]
    refine integral_mono hGF (h2.const_mul C) fun x => ?_
    exact mul_le_mul_of_nonneg_right (hC x) (sq_nonneg _)

/-- **FIN020.** Fixed partition IMS localization. -/
theorem fixed_partition_ims_localization {k m : ℕ} (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (U : Fin m → Set (EuclideanSpace ℝ (Fin k)))
    (hU : ∀ j, IsOpen (U j)) (hUc : ∀ j, IsCompact (closure (U j)))
    (hcrit : {x | fderiv ℝ ψ x = 0} ⊆ ⋃ j, U j) (j₀ : Fin m)
    (V : Set (EuclideanSpace ℝ (Fin k))) (hV : closure V ⊆ U j₀) :
    ∃ (χ : Option (Fin m) → EuclideanSpace ℝ (Fin k) → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ x, ∑ i, χ i x ^ 2 = 1) ∧
      (∀ j, tsupport (χ (some j)) ⊆ U j) ∧ tsupport (χ none) ⊆ {x | fderiv ℝ ψ x ≠ 0} ∧
      (∀ x ∈ V, χ (some j₀) x = 1) ∧ (∀ x, ∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2 ≤ C) ∧
      ∀ (N : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ 1 F →
        Integrable (fun x => ‖fderiv ℝ F x‖ ^ 2) (imsEta N ψ) →
        Integrable (fun x => F x ^ 2) (imsEta N ψ) →
        ∑ i, ∫ x, ‖fderiv ℝ (fun y => χ i y * F y) x‖ ^ 2 ∂(imsEta N ψ) =
            ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂(imsEta N ψ) +
              ∫ x, (∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2) * F x ^ 2 ∂(imsEta N ψ) ∧
          ∫ x, (∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2) * F x ^ 2 ∂(imsEta N ψ) ≤
            C * ∫ x, F x ^ 2 ∂(imsEta N ψ) := by
  have hW : IsOpen {x : EuclideanSpace ℝ (Fin k) | fderiv ℝ ψ x ≠ 0} :=
    (hψ.continuous_fderiv (by simp)).isOpen_preimage _ isOpen_compl_singleton
  obtain ⟨χ, hχ, hsum, hsub, hext, hone, C, hC⟩ :=
    ims_cutoffs U hU hUc _ hW (fun x hx => hcrit (by simpa using hx)) j₀ V hV
  refine ⟨χ, max C 0, le_max_right _ _, hχ, hsum, hsub, hext, hone,
    fun x => (hC x).trans (le_max_left _ _), fun N F hF h1 h2 => ?_⟩
  exact ims_integral_identity χ hχ hsum (max C 0) (fun x => (hC x).trans (le_max_left _ _))
    _ F hF h1 h2

end DGPS.FiniteN
