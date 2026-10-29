import DGPS.Analysis.BoundedPerturbation
import DGPS.Foundations.Entropy
import Mathlib

/-!
# Bounded comparison, tensorization and covariance (FIN004)

Abstract (measure-theoretic) tools for Poincare / log-Sobolev inverse constants, with an abstract
test class `Sm` and an abstract carre-du-champ `Gamma : (α → ℝ) → α → ℝ≥0∞`, the energy of a
measure `μ` being `∫⁻ Gamma f dμ`.

* `PoincareAt μ Sm Gamma C`: `Var_μ f ≤ C ∫⁻ Gamma f dμ` (inverse constant `C`);
* `LogSobolevAt μ Sm Gamma C`: `Ent_μ(f²) ≤ C ∫⁻ Gamma f dμ`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace DGPS.FiniteN.Tools.BoundedComparison

section Defs

variable {α : Type*} [MeasurableSpace α]

/-- Poincare inequality with inverse constant `C` for the test class `Sm` and carre-du-champ `Γ`. -/
def PoincareAt (μ : Measure α) (Sm : (α → ℝ) → Prop) (Γ : (α → ℝ) → α → ℝ≥0∞) (C : ℝ) : Prop :=
  ∀ f, Sm f → evariance f μ ≤ ENNReal.ofReal C * ∫⁻ x, Γ f x ∂μ

/-- Log-Sobolev inequality with inverse constant `C`: `Ent_μ(f²) ≤ C ∫ Γ f`. -/
def LogSobolevAt (μ : Measure α) (Sm : (α → ℝ) → Prop) (Γ : (α → ℝ) → α → ℝ≥0∞) (C : ℝ) :
    Prop :=
  ∀ f, Sm f → DGPS.homogeneousEntropy μ (fun x => f x ^ 2) ≤
    ENNReal.ofReal C * ∫⁻ x, Γ f x ∂μ

end Defs

section Comparison

variable {α : Type*} [MeasurableSpace α]

theorem evariance_le_lintegral_sub {P : Measure α} [IsProbabilityMeasure P] {f : α → ℝ}
    (hf : MemLp f 2 P) (c : ℝ) :
    evariance f P ≤ ∫⁻ x, ‖f x - c‖ₑ ^ 2 ∂P := by
  rw [← hf.ofReal_variance_eq]
  have hsub : MemLp (fun x => f x - c) 2 P := hf.sub (memLp_const c)
  have h1 : variance f P = variance (fun x => f x - c) P :=
    (variance_sub_const hf.aestronglyMeasurable c).symm
  have h2 := variance_le_expectation_sq (μ := P) (X := fun x => f x - c) hsub.aestronglyMeasurable
  have hint : Integrable (fun x => (f x - c) ^ 2) P := hsub.integrable_sq
  rw [h1]
  have h3 : variance (fun x => f x - c) P ≤ ∫ x, (f x - c) ^ 2 ∂P := h2
  refine (ENNReal.ofReal_le_ofReal h3).trans ?_
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _)]
  refine le_of_eq (lintegral_congr fun x => ?_)
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- Two-sided density bounds from the oscillation hypothesis: `m ≤ ρ ≤ e^K m` with `m > 0`. -/
theorem density_bounds {Q P : Measure α} [IsProbabilityMeasure P] {ρ : α → ℝ} {K : ℝ}
    (hP : P = Q.withDensity (fun x => ENNReal.ofReal (ρ x))) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hosc : ∀ x y, ρ x ≤ Real.exp K * ρ y) :
    ∃ m : ℝ, 0 < m ∧ (∀ x, m ≤ ρ x) ∧ ∀ x, ρ x ≤ Real.exp K * m := by
  have hne : Nonempty α := by
    by_contra h
    have h1 := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.2 (not_nonempty_iff.1 h)] at h1
    simp at h1
  have hbdd : BddBelow (Set.range ρ) := ⟨0, by rintro _ ⟨y, rfl⟩; exact hρ0 y⟩
  set m : ℝ := ⨅ y, ρ y with hm
  have hle : ∀ x, m ≤ ρ x := fun x => ciInf_le hbdd x
  have hup : ∀ x, ρ x ≤ Real.exp K * m := by
    intro x
    have : ρ x / Real.exp K ≤ m := le_ciInf fun y => by
      rw [div_le_iff₀ (Real.exp_pos K), mul_comm]
      exact hosc x y
    rwa [div_le_iff₀ (Real.exp_pos K), mul_comm] at this
  refine ⟨m, ?_, hle, hup⟩
  by_contra hm0
  have hz : ∀ x, ρ x = 0 := fun x =>
    le_antisymm ((hup x).trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos K).le
      (not_lt.1 hm0))) (hρ0 x)
  have h1 := measure_univ (μ := P)
  rw [hP, withDensity_apply _ MeasurableSet.univ] at h1
  simp [hz] at h1

theorem measure_le_of_density {Q : Measure α} {ρ : α → ℝ} {c : ℝ} (hc : ∀ x, ρ x ≤ c) :
    Q.withDensity (fun x => ENNReal.ofReal (ρ x)) ≤ ENNReal.ofReal c • Q := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hc x)

theorem measure_ge_of_density {Q : Measure α} {ρ : α → ℝ} {m : ℝ} (hm : 0 < m)
    (hc : ∀ x, m ≤ ρ x) :
    Q ≤ ENNReal.ofReal m⁻¹ • Q.withDensity (fun x => ENNReal.ofReal (ρ x)) := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← setLIntegral_one]
  · refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hm.le), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_mul_eq_div, le_div_iff₀ hm]
    linarith [hc x]

/-- **Poincare comparison.** -/
theorem poincare_comparison {Q P : Measure α} [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    {ρ : α → ℝ} {K : ℝ} (hP : P = Q.withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hρ0 : ∀ x, 0 ≤ ρ x) (hosc : ∀ x y, ρ x ≤ Real.exp K * ρ y)
    {Sm : (α → ℝ) → Prop} {Γ : (α → ℝ) → α → ℝ≥0∞} (hmem : ∀ f, Sm f → MemLp f 2 Q)
    {C : ℝ} (hQ : PoincareAt Q Sm Γ C) :
    PoincareAt P Sm Γ (Real.exp K * C) := by
  obtain ⟨m, hm, hlo, hhi⟩ := density_bounds hP hρ0 hosc
  have h1 : P ≤ ENNReal.ofReal (Real.exp K * m) • Q := hP ▸ measure_le_of_density hhi
  have h2 : Q ≤ ENNReal.ofReal m⁻¹ • P := hP ▸ measure_ge_of_density hm hlo
  intro f hf
  have hfP : MemLp f 2 P := (hmem f hf).of_measure_le_smul ENNReal.ofReal_ne_top h1
  refine (evariance_le_lintegral_sub hfP (∫ x, f x ∂Q)).trans ?_
  calc ∫⁻ x, ‖f x - ∫ y, f y ∂Q‖ₑ ^ 2 ∂P
      ≤ ∫⁻ x, ‖f x - ∫ y, f y ∂Q‖ₑ ^ 2 ∂(ENNReal.ofReal (Real.exp K * m) • Q) :=
        lintegral_mono' h1 le_rfl
    _ = ENNReal.ofReal (Real.exp K * m) * evariance f Q := by
        rw [lintegral_smul_measure, smul_eq_mul]; rfl
    _ ≤ ENNReal.ofReal (Real.exp K * m) * (ENNReal.ofReal C * ∫⁻ x, Γ f x ∂Q) :=
        mul_le_mul' le_rfl (hQ f hf)
    _ ≤ ENNReal.ofReal (Real.exp K * m) * (ENNReal.ofReal C *
          ∫⁻ x, Γ f x ∂(ENNReal.ofReal m⁻¹ • P)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (lintegral_mono' h2 le_rfl))
    _ = ENNReal.ofReal (Real.exp K * C) * ∫⁻ x, Γ f x ∂P := by
        rw [lintegral_smul_measure, smul_eq_mul]
        have : ENNReal.ofReal (Real.exp K * m) * (ENNReal.ofReal C * ENNReal.ofReal m⁻¹) =
            ENNReal.ofReal (Real.exp K * C) := by
          rcases le_or_gt 0 C with hC | hC
          · rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            field_simp
          · rw [ENNReal.ofReal_of_nonpos hC.le, ENNReal.ofReal_of_nonpos
              (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos K).le hC.le)]
            simp
        rw [← this]; ring

theorem ofReal_mul_ofReal_inv_aux {K C m : ℝ} (hm : 0 < m) :
    ENNReal.ofReal (Real.exp K * m) * (ENNReal.ofReal C * ENNReal.ofReal m⁻¹) =
      ENNReal.ofReal (Real.exp K * C) := by
  rcases le_or_gt 0 C with hC | hC
  · rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  · rw [ENNReal.ofReal_of_nonpos hC.le, ENNReal.ofReal_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos K).le hC.le)]
    simp

/-- **Log-Sobolev comparison.** -/
theorem logSobolev_comparison {Q P : Measure α} [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    {ρ : α → ℝ} {K : ℝ} (hP : P = Q.withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hρ0 : ∀ x, 0 ≤ ρ x) (hosc : ∀ x y, ρ x ≤ Real.exp K * ρ y)
    {Sm : (α → ℝ) → Prop} {Γ : (α → ℝ) → α → ℝ≥0∞} (hmem : ∀ f, Sm f → MemLp f 2 Q)
    {C : ℝ} (hQ : LogSobolevAt Q Sm Γ C) :
    LogSobolevAt P Sm Γ (Real.exp K * C) := by
  obtain ⟨m, hm, hlo, hhi⟩ := density_bounds hP hρ0 hosc
  have h1 : P ≤ ENNReal.ofReal (Real.exp K * m) • Q := hP ▸ measure_le_of_density hhi
  have h2 : Q ≤ ENNReal.ofReal m⁻¹ • P := hP ▸ measure_ge_of_density hm hlo
  have hac : P ≪ Q := hP ▸ withDensity_absolutelyContinuous _ _
  intro f hf
  have hfQ := hmem f hf
  have hfP : MemLp f 2 P := hfQ.of_measure_le_smul ENNReal.ofReal_ne_top h1
  have hvQ : Integrable (fun x => f x ^ 2) Q := hfQ.integrable_sq
  have hvP : Integrable (fun x => f x ^ 2) P := hfP.integrable_sq
  have hv0 : ∀ x, 0 ≤ f x ^ 2 := fun x => sq_nonneg _
  by_cases hP0 : ∫ x, f x ^ 2 ∂P = 0
  · rw [DGPS.homogeneousEntropy_of_integral_eq_zero hP0]; exact bot_le
  have hb : 0 < ∫ x, f x ^ 2 ∂Q := by
    refine lt_of_le_of_ne (integral_nonneg hv0) fun h0 => hP0 ?_
    have hz : (fun x => f x ^ 2) =ᵐ[Q] 0 := (integral_eq_zero_iff_of_nonneg hv0 hvQ).1 h0.symm
    exact integral_eq_zero_of_ae (hac.ae_le hz)
  calc DGPS.homogeneousEntropy P (fun x => f x ^ 2)
      ≤ ∫⁻ x, ENNReal.ofReal (DGPS.entropyIntegrand (∫ y, f y ^ 2 ∂Q) (f x ^ 2)) ∂P :=
        DGPS.def025_entropy_le_lintegral hv0 hvP hb
    _ ≤ ∫⁻ x, ENNReal.ofReal (DGPS.entropyIntegrand (∫ y, f y ^ 2 ∂Q) (f x ^ 2))
          ∂(ENNReal.ofReal (Real.exp K * m) • Q) := lintegral_mono' h1 le_rfl
    _ = ENNReal.ofReal (Real.exp K * m) * DGPS.homogeneousEntropy Q (fun x => f x ^ 2) := by
        rw [lintegral_smul_measure, smul_eq_mul,
          DGPS.homogeneousEntropy_of_integral_ne_zero hb.ne']
    _ ≤ ENNReal.ofReal (Real.exp K * m) * (ENNReal.ofReal C * ∫⁻ x, Γ f x ∂Q) :=
        mul_le_mul' le_rfl (hQ f hf)
    _ ≤ ENNReal.ofReal (Real.exp K * m) * (ENNReal.ofReal C *
          ∫⁻ x, Γ f x ∂(ENNReal.ofReal m⁻¹ • P)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (lintegral_mono' h2 le_rfl))
    _ = ENNReal.ofReal (Real.exp K * C) * ∫⁻ x, Γ f x ∂P := by
        have := ofReal_mul_ofReal_inv_aux (K := K) (C := C) hm
        rw [lintegral_smul_measure, smul_eq_mul, ← this]
        ring

end Comparison

section Covariance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The trace of the covariance matrix of a random vector in `ℝ^m`: the sum of the variances of the
coordinates. -/
noncomputable def traceCov {m : ℕ} (X : Ω → EuclideanSpace ℝ (Fin m)) (μ : Measure Ω) : ℝ :=
  ∑ k, variance (fun ω => X ω k) μ

/-- `tr Cov (Σ_i φ_i) ≤ N L²` for independent vector features with `‖φ_i‖ ≤ L`. -/
theorem traceCov_sum_le {μ : Measure Ω} [IsProbabilityMeasure μ] {N m : ℕ}
    {φ : Fin N → Ω → EuclideanSpace ℝ (Fin m)} (hmeas : ∀ i, Measurable (φ i))
    (hind : iIndepFun φ μ) {L : ℝ} (hL : ∀ i ω, ‖φ i ω‖ ≤ L) :
    traceCov (fun ω => ∑ i, φ i ω) μ ≤ N * L ^ 2 := by
  have hcoord : ∀ (i : Fin N) (k : Fin m), Measurable (fun ω => φ i ω k) := fun i k =>
    (EuclideanSpace.proj k).continuous.measurable.comp (hmeas i)
  have hbd : ∀ (i : Fin N) (k : Fin m) ω, |φ i ω k| ≤ L := fun i k ω =>
    by simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (φ i ω) k).trans (hL i ω)
  have hL0 : ∀ i : Fin N, ∀ ω, 0 ≤ L := fun i ω => (norm_nonneg _).trans (hL i ω)
  have hLp : ∀ (i : Fin N) (k : Fin m), MemLp (fun ω => φ i ω k) 2 μ := fun i k =>
    MemLp.of_bound (hcoord i k).aestronglyMeasurable L
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hbd i k ω)
  have hindk : ∀ k : Fin m, iIndepFun (fun (i : Fin N) ω => φ i ω k) μ := fun k =>
    hind.comp (fun _ x => x k) (fun _ => (EuclideanSpace.proj k).continuous.measurable)
  have hvar : ∀ k : Fin m, variance (fun ω => (∑ i, φ i ω) k) μ =
      ∑ i, variance (fun ω => φ i ω k) μ := by
    intro k
    have h := IndepFun.variance_sum (μ := μ) (s := Finset.univ)
      (X := fun (i : Fin N) ω => φ i ω k) (fun i _ => hLp i k)
      (fun i _ j _ hij => (hindk k).indepFun hij)
    have e : (fun ω => (∑ i, φ i ω) k) = ∑ i, fun ω => φ i ω k := by
      funext ω; simp [Finset.sum_apply, WithLp.ofLp_sum]
    rw [e]; exact h
  unfold traceCov
  simp_rw [hvar]
  rw [Finset.sum_comm]
  have hone : ∀ i : Fin N, ∑ k, variance (fun ω => φ i ω k) μ ≤ L ^ 2 := by
    intro i
    have h1 : ∀ k, variance (fun ω => φ i ω k) μ ≤ ∫ ω, (φ i ω k) ^ 2 ∂μ := fun k => by
      have := variance_le_expectation_sq (μ := μ) (X := fun ω => φ i ω k)
        (hcoord i k).aestronglyMeasurable
      simpa [Pi.pow_apply] using this
    have hint : ∀ k, Integrable (fun ω => (φ i ω k) ^ 2) μ := fun k => (hLp i k).integrable_sq
    calc ∑ k, variance (fun ω => φ i ω k) μ ≤ ∑ k, ∫ ω, (φ i ω k) ^ 2 ∂μ :=
          Finset.sum_le_sum fun k _ => h1 k
      _ = ∫ ω, ∑ k, (φ i ω k) ^ 2 ∂μ := (integral_finsetSum _ fun k _ => hint k).symm
      _ ≤ ∫ ω, L ^ 2 ∂μ := by
          refine integral_mono (integrable_finsetSum _ fun k _ => hint k)
            (integrable_const _) fun ω => ?_
          have : ∑ k, (φ i ω k) ^ 2 = ‖φ i ω‖ ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
          rw [this]
          exact pow_le_pow_left₀ (norm_nonneg _) (hL i ω) 2
      _ = L ^ 2 := by simp
  calc ∑ i, ∑ k, variance (fun ω => φ i ω k) μ ≤ ∑ _i : Fin N, L ^ 2 :=
        Finset.sum_le_sum fun i _ => hone i
    _ = N * L ^ 2 := by simp

end Covariance


section BinaryVar

variable {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure β} {ν : Measure γ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem lintegral_sub_const_eq {s : β → ℝ} (hs : MemLp s 2 μ) (c : ℝ) :
    ∫⁻ x, ‖s x - c‖ₑ ^ 2 ∂μ = evariance s μ + ‖∫ x, s x ∂μ - c‖ₑ ^ 2 := by
  have hsub : MemLp (fun x => s x - c) 2 μ := hs.sub (memLp_const c)
  have h1 : variance s μ = variance (fun x => s x - c) μ :=
    (variance_sub_const hs.aestronglyMeasurable c).symm
  have hv := variance_eq_sub hsub
  have hint : Integrable (fun x => (s x - c) ^ 2) μ := hsub.integrable_sq
  have hs1 : Integrable s μ := hs.integrable one_le_two
  have hmean : ∫ x, (s x - c) ∂μ = ∫ x, s x ∂μ - c := by
    rw [integral_sub hs1 (integrable_const c)]; simp
  rw [← hs.ofReal_variance_eq]
  have hL : ∫⁻ x, ‖s x - c‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, (s x - c) ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [hL]
  have hE : ∫ x, (s x - c) ^ 2 ∂μ = variance s μ + (∫ x, s x ∂μ - c) ^ 2 := by
    have : variance (fun x => s x - c) μ = ∫ x, (s x - c) ^ 2 ∂μ - (∫ x, (s x - c) ∂μ) ^ 2 := by
      simpa [Pi.pow_apply] using hv
    rw [hmean] at this
    linarith
  rw [hE, ENNReal.ofReal_add (variance_nonneg _ _) (sq_nonneg _), Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]


theorem enorm_integral_sq_le (g : β → ℝ) : ‖∫ x, g x ∂μ‖ₑ ^ 2 ≤ ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
  by_cases hg : Integrable g μ
  swap
  · rw [integral_undef hg]; simp
  by_cases htop : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ⊤
  · rw [htop]; exact le_top
  have hint : Integrable (fun x => g x ^ 2) μ := by
    refine ⟨hg.aestronglyMeasurable.pow 2, ?_⟩
    have : ∫⁻ x, ‖g x ^ 2‖ₑ ∂μ = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
      refine lintegral_congr fun x => ?_
      rw [enorm_pow]
    show ∫⁻ x, ‖g x ^ 2‖ₑ ∂μ < ⊤
    rw [this]; exact lt_top_iff_ne_top.2 htop
  have hmem : MemLp g 2 μ := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hint
  have hv := variance_eq_sub hmem
  have h0 := variance_nonneg g μ
  have hle : (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
    have : variance g μ = ∫ x, g x ^ 2 ∂μ - (∫ x, g x ∂μ) ^ 2 := by
      simpa [Pi.pow_apply] using hv
    linarith
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  calc ENNReal.ofReal ((∫ x, g x ∂μ) ^ 2) ≤ ENNReal.ofReal (∫ x, g x ^ 2 ∂μ) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _)]
        refine lintegral_congr fun x => ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem variance_binary {f : β × γ → ℝ} (hf : Measurable f) (hL : MemLp f 2 (μ.prod ν)) :
    evariance f (μ.prod ν) ≤ ∫⁻ y, evariance (fun x => f (x, y)) μ ∂ν
      + ∫⁻ x, evariance (fun y => f (x, y)) ν ∂μ := by
  have hf1 : Integrable f (μ.prod ν) := hL.integrable one_le_two
  have hf2 : Integrable (fun z => f z ^ 2) (μ.prod ν) := hL.integrable_sq
  set m := ∫ z, f z ∂(μ.prod ν) with hm
  set A : γ → ℝ := fun y => ∫ x, f (x, y) ∂μ with hA
  set h : β → ℝ := fun x => ∫ y, f (x, y) ∂ν with hh
  have hAm : Measurable A := (hf.stronglyMeasurable.integral_prod_left').measurable
  have hhm : Measurable h := (hf.stronglyMeasurable.integral_prod_right').measurable
  have hsl : ∀ᵐ y ∂ν, MemLp (fun x => f (x, y)) 2 μ := by
    filter_upwards [hf2.prod_left_ae] with y hy
    exact (memLp_two_iff_integrable_sq (hf.comp measurable_prodMk_right).aestronglyMeasurable).2 hy
  have hsl1 : ∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ := hf1.prod_left_ae
  have hmeas : Measurable (fun z : β × γ => ‖f z - m‖ₑ ^ 2) := (hf.sub_const m).enorm.pow_const 2
  have step1 : ∫⁻ z, ‖f z - m‖ₑ ^ 2 ∂(μ.prod ν)
      = ∫⁻ y, evariance (fun x => f (x, y)) μ ∂ν + ∫⁻ y, ‖A y - m‖ₑ ^ 2 ∂ν := by
    rw [lintegral_prod_symm _ hmeas.aemeasurable,
      ← lintegral_add_right _ ((hAm.sub_const m).enorm.pow_const 2)]
    refine lintegral_congr_ae ?_
    filter_upwards [hsl] with y hy
    exact lintegral_sub_const_eq hy m
  have hhint : Integrable h μ := hf1.integral_prod_left
  have hmh : ∫ x, h x ∂μ = m := (integral_prod f hf1).symm
  have step2 : ∫⁻ y, ‖A y - m‖ₑ ^ 2 ∂ν ≤ ∫⁻ x, evariance (fun y => f (x, y)) ν ∂μ := by
    have hae : ∀ᵐ y ∂ν, ‖A y - m‖ₑ ^ 2 ≤ ∫⁻ x, ‖f (x, y) - h x‖ₑ ^ 2 ∂μ := by
      filter_upwards [hsl1] with y hy
      have : A y - m = ∫ x, (f (x, y) - h x) ∂μ := by
        rw [integral_sub hy hhint, hmh]
      rw [this]
      exact enorm_integral_sq_le _
    refine (lintegral_mono_ae hae).trans ?_
    have hmeas2 : Measurable (Function.uncurry fun x y => ‖f (x, y) - h x‖ₑ ^ 2) := by
      have : Function.uncurry (fun x y => ‖f (x, y) - h x‖ₑ ^ 2)
          = fun z : β × γ => ‖f z - h z.1‖ₑ ^ 2 := by
        funext z; rfl
      rw [this]
      exact (hf.sub (hhm.comp measurable_fst)).enorm.pow_const 2
    rw [← lintegral_lintegral_swap hmeas2.aemeasurable]
    exact le_of_eq rfl
  calc evariance f (μ.prod ν) = ∫⁻ z, ‖f z - m‖ₑ ^ 2 ∂(μ.prod ν) := rfl
    _ = _ := step1
    _ ≤ _ := by gcongr

end BinaryVar

section BinaryEntropy

variable {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure β} {ν : Measure γ}

theorem ent_pointwise {M a b s : ℝ} (hM : 0 < M) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s)
    (hpos : 0 < s → 0 < a ∧ 0 < b) :
    0 ≤ DGPS.entropyIntegrand a s ∧ 0 ≤ DGPS.entropyIntegrand b s ∧
    DGPS.entropyIntegrand M s ≤ DGPS.entropyIntegrand a s + DGPS.entropyIntegrand b s
      - (1 - a / M) * (b - M) := by
  rcases hs.eq_or_lt with h0 | hs0
  · subst h0
    simp only [DGPS.entropyIntegrand, zero_div, Real.log_zero, mul_zero,
      zero_add, sub_zero]
    refine ⟨ha, hb, ?_⟩
    have : (1 - a / M) * (b - M) = b - M - a * b / M + a := by field_simp; ring
    rw [this]
    have : 0 ≤ a * b / M := by positivity
    linarith
  · obtain ⟨ha0, hb0⟩ := hpos hs0
    refine ⟨DGPS.entropyIntegrand_nonneg ha0 hs, DGPS.entropyIntegrand_nonneg hb0 hs, ?_⟩
    have hr : 0 < a * b / (M * s) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hr
    have key : Real.log (s / M) - Real.log (s / a) - Real.log (s / b)
        = Real.log (a * b / (M * s)) := by
      rw [Real.log_div hs0.ne' hM.ne', Real.log_div hs0.ne' ha0.ne', Real.log_div hs0.ne' hb0.ne',
        Real.log_div (mul_pos ha0 hb0).ne' (mul_pos hM hs0).ne', Real.log_mul ha0.ne' hb0.ne',
        Real.log_mul hM.ne' hs0.ne']
      ring
    have hsr : s * (a * b / (M * s)) = a * b / M := by field_simp
    have h2 : s * (Real.log (s / M) - Real.log (s / a) - Real.log (s / b)) ≤ a * b / M - s := by
      rw [key]
      nlinarith [mul_le_mul_of_nonneg_left hlog hs, hsr]
    have : (1 - a / M) * (b - M) = b - M - a * b / M + a := by field_simp; ring
    unfold DGPS.entropyIntegrand
    rw [this]
    nlinarith [h2]


theorem homogeneousEntropy_eq_lintegral_of_nonneg {P : Measure β} {v : β → ℝ}
    (hv : ∀ x, 0 ≤ v x) :
    DGPS.homogeneousEntropy P v
      = ∫⁻ x, ENNReal.ofReal (DGPS.entropyIntegrand (∫ y, v y ∂P) (v x)) ∂P := by
  by_cases h : ∫ y, v y ∂P = 0
  · rw [DGPS.homogeneousEntropy_of_integral_eq_zero h, h]
    symm
    rw [← lintegral_zero (μ := P)]
    refine lintegral_congr fun x => ?_
    have : DGPS.entropyIntegrand 0 (v x) = - v x := by
      simp [DGPS.entropyIntegrand]
    rw [this]
    exact ENNReal.ofReal_eq_zero.2 (by linarith [hv x])
  · exact DGPS.homogeneousEntropy_of_integral_ne_zero h

/-- If `g ≥ 0`, `∫ h = 0` and `g + h ≥ 0` a.e. then `∫⁻ ofReal (g + h) ≤ ∫⁻ ofReal g`. -/
theorem lintegral_ofReal_add_le {Z : Type*} [MeasurableSpace Z] {P : Measure Z} {g h : Z → ℝ}
    (hg : Measurable g) (hg0 : 0 ≤ᵐ[P] g) (hh : Integrable h P) (hh0 : ∫ z, h z ∂P = 0)
    (hgh : 0 ≤ᵐ[P] fun z => g z + h z) :
    ∫⁻ z, ENNReal.ofReal (g z + h z) ∂P ≤ ∫⁻ z, ENNReal.ofReal (g z) ∂P := by
  by_cases htop : ∫⁻ z, ENNReal.ofReal (g z) ∂P = ⊤
  · rw [htop]; exact le_top
  have hgi : Integrable g P := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have : ∫⁻ z, ‖g z‖ₑ ∂P = ∫⁻ z, ENNReal.ofReal (g z) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hg0] with z hz
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hz]
    rw [this]; exact lt_top_iff_ne_top.2 htop
  have hsum : Integrable (fun z => g z + h z) P := hgi.add hh
  rw [← ofReal_integral_eq_lintegral_ofReal hsum hgh,
    ← ofReal_integral_eq_lintegral_ofReal hgi hg0, integral_add hgi hh, hh0, add_zero]

theorem entropy_binary [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {F : β × γ → ℝ}
    (hFm : Measurable F) (hF0 : ∀ z, 0 ≤ F z) (hFi : Integrable F (μ.prod ν)) :
    DGPS.homogeneousEntropy (μ.prod ν) F ≤
      ∫⁻ y, DGPS.homogeneousEntropy μ (fun x => F (x, y)) ∂ν
      + ∫⁻ x, DGPS.homogeneousEntropy ν (fun y => F (x, y)) ∂μ := by
  set M := ∫ z, F z ∂(μ.prod ν) with hM
  have hM0 : 0 ≤ M := integral_nonneg hF0
  rcases hM0.eq_or_lt with hMz | hMpos
  · rw [DGPS.homogeneousEntropy_of_integral_eq_zero hMz.symm]; exact bot_le
  set a : γ → ℝ := fun y => ∫ x, F (x, y) ∂μ with ha
  set b : β → ℝ := fun x => ∫ y, F (x, y) ∂ν with hb
  have ham : Measurable a := (hFm.stronglyMeasurable.integral_prod_left').measurable
  have hbm : Measurable b := (hFm.stronglyMeasurable.integral_prod_right').measurable
  have ha0 : ∀ y, 0 ≤ a y := fun y => integral_nonneg fun x => hF0 _
  have hb0 : ∀ x, 0 ≤ b x := fun x => integral_nonneg fun y => hF0 _
  have haint : Integrable a ν := hFi.integral_prod_right
  have hbint : Integrable b μ := hFi.integral_prod_left
  have haM : ∫ y, a y ∂ν = M := (integral_prod_symm F hFi).symm
  have hbM : ∫ x, b x ∂μ = M := (integral_prod F hFi).symm
  -- cross term
  set T : β × γ → ℝ := fun z => -((b z.1 - M) * (1 - a z.2 / M)) with hT
  have hTint : Integrable T (μ.prod ν) := by
    have h1 : Integrable (fun x => b x - M) μ := hbint.sub (integrable_const M)
    have h2 : Integrable (fun y => 1 - a y / M) ν :=
      (integrable_const (1 : ℝ)).sub (haint.div_const M)
    exact (h1.mul_prod h2).neg
  have hT0 : ∫ z, T z ∂(μ.prod ν) = 0 := by
    have : ∫ z, T z ∂(μ.prod ν) = -((∫ x, (b x - M) ∂μ) * ∫ y, (1 - a y / M) ∂ν) := by
      rw [integral_neg, integral_prod_mul (fun x => b x - M) (fun y => 1 - a y / M)]
    rw [this, integral_sub hbint (integrable_const M), hbM]
    simp
  -- positivity a.e.
  have hset1 : MeasurableSet {z : β × γ | 0 < F z → 0 < b z.1} := by
    have : {z : β × γ | 0 < F z → 0 < b z.1} = {z | 0 < F z}ᶜ ∪ {z | 0 < b z.1} := by
      ext z; simp [imp_iff_not_or]
    rw [this]
    exact (measurableSet_lt measurable_const hFm).compl.union
      (measurableSet_lt measurable_const (hbm.comp measurable_fst))
  have hset2 : MeasurableSet {z : β × γ | 0 < F z → 0 < a z.2} := by
    have : {z : β × γ | 0 < F z → 0 < a z.2} = {z | 0 < F z}ᶜ ∪ {z | 0 < a z.2} := by
      ext z; simp [imp_iff_not_or]
    rw [this]
    exact (measurableSet_lt measurable_const hFm).compl.union
      (measurableSet_lt measurable_const (ham.comp measurable_snd))
  have hpos1 : ∀ᵐ z ∂(μ.prod ν), 0 < F z → 0 < b z.1 := by
    rw [Measure.ae_prod_iff_ae_ae hset1]
    filter_upwards [hFi.prod_right_ae] with x hx
    by_cases hbx : b x = 0
    · have := (integral_eq_zero_iff_of_nonneg (fun y => hF0 (x, y)) hx).1 hbx
      filter_upwards [this] with y hy hp
      have hy' : F (x, y) = 0 := hy
      rw [hy'] at hp; exact absurd hp (lt_irrefl _)
    · exact Eventually.of_forall fun y _ => lt_of_le_of_ne (hb0 x) (Ne.symm hbx)
  have hpos2 : ∀ᵐ z ∂(μ.prod ν), 0 < F z → 0 < a z.2 := by
    rw [Measure.ae_prod_iff_ae_ae hset2]
    refine (Measure.ae_ae_comm (p := fun x y => 0 < F (x, y) → 0 < a y) hset2).2 ?_
    filter_upwards [hFi.prod_left_ae] with y hy
    by_cases hay : a y = 0
    · have := (integral_eq_zero_iff_of_nonneg (fun x => hF0 (x, y)) hy).1 hay
      filter_upwards [this] with x hx hp
      have hx' : F (x, y) = 0 := hx
      rw [hx'] at hp; exact absurd hp (lt_irrefl _)
    · exact Eventually.of_forall fun x _ => lt_of_le_of_ne (ha0 y) (Ne.symm hay)
  -- the two entropy integrands
  set u : β × γ → ℝ := fun z => DGPS.entropyIntegrand (a z.2) (F z) with hu
  set v : β × γ → ℝ := fun z => DGPS.entropyIntegrand (b z.1) (F z) with hv
  have hum : Measurable u := by
    simp only [hu, DGPS.entropyIntegrand]
    exact ((hFm.mul (Real.measurable_log.comp (hFm.div (ham.comp measurable_snd)))).sub hFm).add
      (ham.comp measurable_snd)
  have hvm : Measurable v := by
    simp only [hv, DGPS.entropyIntegrand]
    exact ((hFm.mul (Real.measurable_log.comp (hFm.div (hbm.comp measurable_fst)))).sub hFm).add
      (hbm.comp measurable_fst)
  have hpt : ∀ᵐ z ∂(μ.prod ν), 0 ≤ u z ∧ 0 ≤ v z ∧
      DGPS.entropyIntegrand M (F z) ≤ u z + v z + T z := by
    filter_upwards [hpos1, hpos2] with z h1 h2
    obtain ⟨p1, p2, p3⟩ := ent_pointwise hMpos (ha0 z.2) (hb0 z.1) (hF0 z)
      (fun hp => ⟨h2 hp, h1 hp⟩)
    refine ⟨p1, p2, ?_⟩
    simp only [hu, hv, hT]
    linarith
  have hE0 : ∀ z, 0 ≤ DGPS.entropyIntegrand M (F z) := fun z =>
    DGPS.entropyIntegrand_nonneg hMpos (hF0 z)
  calc DGPS.homogeneousEntropy (μ.prod ν) F
      = ∫⁻ z, ENNReal.ofReal (DGPS.entropyIntegrand M (F z)) ∂(μ.prod ν) :=
        homogeneousEntropy_eq_lintegral_of_nonneg hF0
    _ ≤ ∫⁻ z, ENNReal.ofReal ((u z + v z) + T z) ∂(μ.prod ν) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpt] with z hz
        exact ENNReal.ofReal_le_ofReal (by linarith [hz.2.2])
    _ ≤ ∫⁻ z, ENNReal.ofReal (u z + v z) ∂(μ.prod ν) := by
        refine lintegral_ofReal_add_le (hum.add hvm) ?_ hTint hT0 ?_
        · filter_upwards [hpt] with z hz
          exact add_nonneg hz.1 hz.2.1
        · filter_upwards [hpt] with z hz
          have := hE0 z
          show 0 ≤ u z + v z + T z
          linarith [hz.2.2]
    _ ≤ ∫⁻ z, (ENNReal.ofReal (u z) + ENNReal.ofReal (v z)) ∂(μ.prod ν) :=
        lintegral_mono fun z => ENNReal.ofReal_add_le
    _ = ∫⁻ z, ENNReal.ofReal (u z) ∂(μ.prod ν) + ∫⁻ z, ENNReal.ofReal (v z) ∂(μ.prod ν) :=
        lintegral_add_left hum.ennreal_ofReal _
    _ = _ := by
        congr 1
        · rw [lintegral_prod_symm _ hum.ennreal_ofReal.aemeasurable]
          refine lintegral_congr fun y => ?_
          rw [homogeneousEntropy_eq_lintegral_of_nonneg (fun x => hF0 (x, y))]
        · rw [lintegral_prod _ hvm.ennreal_ofReal.aemeasurable]
          refine lintegral_congr fun x => ?_
          rw [homogeneousEntropy_eq_lintegral_of_nonneg (fun y => hF0 (x, y))]



end BinaryEntropy

universe u

section Cons

variable {α : Type u} [MeasurableSpace α]

/-- `Fin.cons` as a measurable equivalence. -/
noncomputable def consEquiv (n : ℕ) : α × (Fin n → α) ≃ᵐ (Fin (n + 1) → α) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm

theorem consEquiv_apply {n : ℕ} (p : α × (Fin n → α)) :
    consEquiv n p = (Fin.cons p.1 p.2 : Fin (n + 1) → α) := by
  simp [consEquiv]
  rfl

theorem measurePreserving_consEquiv {n : ℕ} (μs : Fin (n + 1) → Measure α)
    [∀ i, IsProbabilityMeasure (μs i)] :
    MeasurePreserving (consEquiv n) ((μs 0).prod (Measure.pi fun j : Fin n => μs j.succ))
      (Measure.pi μs) := by
  have h := (measurePreserving_piFinSuccAbove μs 0).symm
  exact h

theorem aemeasurable_slice {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] {μ : Measure β} {ν : Measure γ} [SFinite μ] [SFinite ν] {h : β × γ → δ}
    (hh : AEMeasurable h (μ.prod ν)) : ∀ᵐ x ∂μ, AEMeasurable (fun y => h (x, y)) ν := by
  obtain ⟨g, hg, heq⟩ := hh
  filter_upwards [Measure.ae_ae_of_ae_prod heq] with x hx
  exact (hg.comp measurable_prodMk_left).aemeasurable.congr (hx.mono fun y hy => hy.symm)

end Cons

section Tensor

variable {α : Type u} [MeasurableSpace α]

/-- The one-coordinate slice of `f` through `x` at coordinate `i`. -/
def slice {n : ℕ} (i : Fin n) (f : (Fin n → α) → ℝ) (x : Fin n → α) : α → ℝ :=
  fun a => f (Function.update x i a)

/-- The site energy density of `f` at `x` in coordinate `i`. -/
def dens (Θ : (α → ℝ) → α → ℝ≥0∞) {n : ℕ} (f : (Fin n → α) → ℝ) (i : Fin n)
    (x : Fin n → α) : ℝ≥0∞ :=
  Θ (slice i f x) (x i)

structure Functional
    (Ψ : ∀ {β : Type u} [MeasurableSpace β], Measure β → (β → ℝ) → ℝ≥0∞) : Prop where
  bin : ∀ {β γ : Type u} [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure β) (ν : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : β × γ → ℝ), Measurable f →
    MemLp f 2 (μ.prod ν) →
    Ψ (μ.prod ν) f ≤ ∫⁻ y, Ψ μ (fun x => f (x, y)) ∂ν + ∫⁻ x, Ψ ν (fun y => f (x, y)) ∂μ
  comp : ∀ {β γ : Type u} [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure β) (ν : Measure γ)
    (e : β ≃ᵐ γ), MeasurePreserving e μ ν → ∀ f : γ → ℝ, Ψ μ (f ∘ e) = Ψ ν f
  pt : ∀ {β : Type u} [MeasurableSpace β] [Subsingleton β] (ν : Measure β)
    [IsProbabilityMeasure ν] (f : β → ℝ), Ψ ν f = 0

structure TP (Sm : (α → ℝ) → Prop) (Θ : (α → ℝ) → α → ℝ≥0∞) {n : ℕ}
    (μs : Fin n → Measure α) (f : (Fin n → α) → ℝ) : Prop where
  meas : Measurable f
  memLp : MemLp f 2 (Measure.pi μs)
  sm : ∀ x i, Sm (slice i f x)
  aem : ∀ i, AEMeasurable (dens Θ f i) (Measure.pi μs)

omit [MeasurableSpace α] in
theorem slice_zero_cons {n : ℕ} (f : (Fin (n + 1) → α) → ℝ) (a : α) (y : Fin n → α) :
    slice 0 f (Fin.cons a y) = fun b => f (Fin.cons b y) := by
  funext b; simp [slice, Fin.update_cons_zero]

omit [MeasurableSpace α] in
theorem slice_succ_cons {n : ℕ} (f : (Fin (n + 1) → α) → ℝ) (a : α) (y : Fin n → α) (j : Fin n) :
    slice j.succ f (Fin.cons a y) = slice j (fun y' => f (Fin.cons a y')) y := by
  funext b; simp [slice, Fin.cons_update]

theorem tensor_bound {Ψ : ∀ {β : Type u} [MeasurableSpace β], Measure β → (β → ℝ) → ℝ≥0∞}
    (hΨ : Functional Ψ) {Sm : (α → ℝ) → Prop} {Θ : (α → ℝ) → α → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (n : ℕ) :
    ∀ (μs : Fin n → Measure α) [∀ i, IsProbabilityMeasure (μs i)],
      (∀ i g, Sm g → Ψ (μs i) g ≤ c * ∫⁻ a, Θ g a ∂μs i) →
      ∀ f, TP Sm Θ μs f →
        Ψ (Measure.pi μs) f ≤ c * ∫⁻ x, ∑ i, dens Θ f i x ∂Measure.pi μs := by
  induction n with
  | zero =>
    intro μs _ _ f _
    rw [hΨ.pt]; exact bot_le
  | succ n ih =>
    intro μs _ hs f hf
    have : Nonempty α := nonempty_of_isProbabilityMeasure (μs 0)
    obtain ⟨a0⟩ := this
    have hmp := measurePreserving_consEquiv μs
    set e : α × (Fin n → α) ≃ᵐ (Fin (n + 1) → α) := consEquiv n with he
    set P' : Measure (α × (Fin n → α)) := (μs 0).prod (Measure.pi fun j : Fin n => μs j.succ)
      with hP'
    have hemb := e.measurableEmbedding
    have hf'm : Measurable (f ∘ e) := hf.meas.comp e.measurable
    have hf'L : MemLp (f ∘ e) 2 P' := by
      refine (memLp_two_iff_integrable_sq hf'm.aestronglyMeasurable).2 ?_
      exact (hmp.integrable_comp_emb hemb (g := fun x => f x ^ 2)).2 hf.memLp.integrable_sq
    have h0 : Ψ P' (f ∘ e) = Ψ (Measure.pi μs) f := hΨ.comp P' _ e hmp f
    have hbin := hΨ.bin (μs 0) (Measure.pi fun j : Fin n => μs j.succ) (f ∘ e) hf'm hf'L
    have hD : ∀ i, AEMeasurable (fun z => dens Θ f i (e z)) P' := fun i =>
      (hmp.aemeasurable_comp_iff hemb (g := dens Θ f i)).2 (hf.aem i)
    -- Term A
    have hA : ∫⁻ y, Ψ (μs 0) (fun a => (f ∘ e) (a, y)) ∂(Measure.pi fun j : Fin n => μs j.succ)
        ≤ c * ∫⁻ x, dens Θ f 0 x ∂Measure.pi μs := by
      calc _ ≤ ∫⁻ y, c * ∫⁻ a, dens Θ f 0 (e (a, y)) ∂(μs 0)
              ∂(Measure.pi fun j : Fin n => μs j.succ) := by
            refine lintegral_mono fun y => ?_
            have hsm : Sm (fun b => f (Fin.cons b y)) := by
              have := hf.sm (Fin.cons a0 y) 0
              rwa [slice_zero_cons] at this
            have hg : (fun a => (f ∘ e) (a, y)) = fun b => f (Fin.cons b y) := by
              funext a; simp [he, consEquiv_apply]
            rw [hg]
            refine (hs 0 _ hsm).trans (le_of_eq ?_)
            congr 1
            refine lintegral_congr fun a => ?_
            simp [dens, consEquiv_apply, slice_zero_cons, he]
        _ = c * ∫⁻ z, dens Θ f 0 (e z) ∂P' := by
            rw [lintegral_const_mul' _ _ hc, lintegral_prod_symm _ (hD 0)]
        _ = _ := by
            rw [hmp.lintegral_comp_emb hemb (dens Θ f 0)]
    -- Term B
    have hB : ∫⁻ a, Ψ (Measure.pi fun j : Fin n => μs j.succ) (fun y => (f ∘ e) (a, y)) ∂(μs 0)
        ≤ c * ∫⁻ x, ∑ j : Fin n, dens Θ f j.succ x ∂Measure.pi μs := by
      have hae_mem : ∀ᵐ a ∂(μs 0), MemLp (fun y => (f ∘ e) (a, y)) 2
          (Measure.pi fun j : Fin n => μs j.succ) := by
        filter_upwards [hf'L.integrable_sq.prod_right_ae] with a ha
        exact (memLp_two_iff_integrable_sq
          (hf'm.comp measurable_prodMk_left).aestronglyMeasurable).2 ha
      have hae_aem : ∀ᵐ a ∂(μs 0), ∀ j : Fin n, AEMeasurable
          (fun y => dens Θ f j.succ (e (a, y))) (Measure.pi fun j : Fin n => μs j.succ) := by
        rw [ae_all_iff]
        exact fun j => aemeasurable_slice (hD j.succ)
      have hsum : AEMeasurable (fun z => ∑ j : Fin n, dens Θ f j.succ (e z)) P' :=
        Finset.aemeasurable_fun_sum (f := fun (j : Fin n) z => dens Θ f j.succ (e z)) _
          fun j _ => hD j.succ
      calc _ ≤ ∫⁻ a, c * ∫⁻ y, ∑ j : Fin n, dens Θ f j.succ (e (a, y))
              ∂(Measure.pi fun j : Fin n => μs j.succ) ∂(μs 0) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae_mem, hae_aem] with a ha1 ha2
            have hTP : TP Sm Θ (fun j : Fin n => μs j.succ) (fun y => (f ∘ e) (a, y)) :=
              { meas := hf'm.comp measurable_prodMk_left
                memLp := ha1
                sm := fun y j => by
                  have := hf.sm (Fin.cons a y) j.succ
                  rw [slice_succ_cons] at this
                  simpa [he, consEquiv_apply] using this
                aem := fun j => by
                  refine (ha2 j).congr (Eventually.of_forall fun y => ?_)
                  simp [dens, consEquiv_apply, slice_succ_cons, he] }
            refine (ih (fun j => μs j.succ) (fun j g hg => hs j.succ g hg) _ hTP).trans
              (le_of_eq ?_)
            congr 1
            refine lintegral_congr fun y => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            simp [dens, consEquiv_apply, slice_succ_cons, he]
        _ = c * ∫⁻ z, ∑ j : Fin n, dens Θ f j.succ (e z) ∂P' := by
            rw [lintegral_const_mul' _ _ hc, lintegral_prod _ hsum]
        _ = _ := by
            rw [hmp.lintegral_comp_emb hemb (fun x => ∑ j : Fin n, dens Θ f j.succ x)]
    calc Ψ (Measure.pi μs) f = Ψ P' (f ∘ e) := h0.symm
      _ ≤ _ := hbin
      _ ≤ c * ∫⁻ x, dens Θ f 0 x ∂Measure.pi μs
          + c * ∫⁻ x, ∑ j : Fin n, dens Θ f j.succ x ∂Measure.pi μs := add_le_add hA hB
      _ = _ := by
        rw [← mul_add, ← lintegral_add_left' (hf.aem 0)]
        congr 1
        refine lintegral_congr fun x => ?_
        rw [Fin.sum_univ_succ]

end Tensor



section Instances

variable {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]

theorem evariance_comp_equiv {μ : Measure β} {ν : Measure γ} (e : β ≃ᵐ γ)
    (hmp : MeasurePreserving e μ ν) (f : γ → ℝ) : evariance (f ∘ e) μ = evariance f ν := by
  unfold evariance
  have h1 : ∫ x, (f ∘ e) x ∂μ = ∫ y, f y ∂ν := hmp.integral_comp' f
  rw [h1]
  exact hmp.lintegral_comp_emb e.measurableEmbedding (fun y => ‖f y - ∫ z, f z ∂ν‖ₑ ^ 2)

theorem homogeneousEntropy_comp_equiv {μ : Measure β} {ν : Measure γ} (e : β ≃ᵐ γ)
    (hmp : MeasurePreserving e μ ν) (v : γ → ℝ) :
    DGPS.homogeneousEntropy μ (v ∘ e) = DGPS.homogeneousEntropy ν v := by
  have h1 : ∫ x, (v ∘ e) x ∂μ = ∫ y, v y ∂ν := hmp.integral_comp' v
  by_cases h : ∫ y, v y ∂ν = 0
  · rw [DGPS.homogeneousEntropy_of_integral_eq_zero h,
      DGPS.homogeneousEntropy_of_integral_eq_zero (by rw [h1]; exact h)]
  · rw [DGPS.homogeneousEntropy_of_integral_ne_zero h,
      DGPS.homogeneousEntropy_of_integral_ne_zero (by rw [h1]; exact h), h1]
    exact hmp.lintegral_comp_emb e.measurableEmbedding
      (fun y => ENNReal.ofReal (DGPS.entropyIntegrand (∫ z, v z ∂ν) (v y)))

theorem evariance_subsingleton [Subsingleton β] (ν : Measure β) [IsProbabilityMeasure ν]
    (f : β → ℝ) : evariance f ν = 0 := by
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure ν
  have hf : f = fun _ => f x0 := funext fun x => congrArg f (Subsingleton.elim _ _)
  unfold evariance
  rw [hf]
  simp

theorem homogeneousEntropy_subsingleton [Subsingleton β] (ν : Measure β)
    [IsProbabilityMeasure ν] (v : β → ℝ) : DGPS.homogeneousEntropy ν v = 0 := by
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure ν
  have hf : v = fun _ => v x0 := funext fun x => congrArg v (Subsingleton.elim _ _)
  by_cases h : v x0 = 0
  · rw [hf, h]
    exact DGPS.homogeneousEntropy_of_integral_eq_zero (by simp)
  · rw [hf, DGPS.homogeneousEntropy_of_integral_ne_zero (by simpa using h)]
    simp [DGPS.entropyIntegrand, h]

end Instances

section Tensorization

universe w

theorem functional_variance :
    Functional.{w} (fun {β : Type w} [MeasurableSpace β] (μ : Measure β) (f : β → ℝ) =>
      evariance f μ) where
  bin := fun _ _ _ _ _ hf hL => variance_binary hf hL
  comp := fun _ _ e hmp f => evariance_comp_equiv e hmp f
  pt := fun ν _ f => evariance_subsingleton ν f

theorem functional_entropy :
    Functional.{w} (fun {β : Type w} [MeasurableSpace β] (μ : Measure β) (f : β → ℝ) =>
      DGPS.homogeneousEntropy μ (fun x => f x ^ 2)) where
  bin := fun _ _ _ _ f hf hL =>
    entropy_binary (F := fun z => f z ^ 2) (hf.pow_const 2) (fun _ => sq_nonneg _)
      hL.integrable_sq
  comp := fun _ _ e hmp f => homogeneousEntropy_comp_equiv e hmp (fun x => f x ^ 2)
  pt := fun ν _ f => homogeneousEntropy_subsingleton ν (fun x => f x ^ 2)

variable {α : Type w} [MeasurableSpace α]

/-- Tensorization of a common single-site Poincare inverse constant. -/
theorem poincare_tensorization {n : ℕ} (μs : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (μs i)] {Sm : (α → ℝ) → Prop} {Γ : (α → ℝ) → α → ℝ≥0∞} {C : ℝ}
    (h : ∀ i, PoincareAt (μs i) Sm Γ C) (f : (Fin n → α) → ℝ) (hf : TP Sm Γ μs f) :
    evariance f (Measure.pi μs) ≤
      ENNReal.ofReal C * ∫⁻ x, ∑ i, Γ (slice i f x) (x i) ∂Measure.pi μs :=
  tensor_bound functional_variance ENNReal.ofReal_ne_top n μs (fun i g hg => h i g hg) f hf

/-- Tensorization of a common single-site log-Sobolev inverse constant. -/
theorem logSobolev_tensorization {n : ℕ} (μs : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (μs i)] {Sm : (α → ℝ) → Prop} {Γ : (α → ℝ) → α → ℝ≥0∞} {C : ℝ}
    (h : ∀ i, LogSobolevAt (μs i) Sm Γ C) (f : (Fin n → α) → ℝ) (hf : TP Sm Γ μs f) :
    DGPS.homogeneousEntropy (Measure.pi μs) (fun x => f x ^ 2) ≤
      ENNReal.ofReal C * ∫⁻ x, ∑ i, Γ (slice i f x) (x i) ∂Measure.pi μs :=
  tensor_bound functional_entropy ENNReal.ofReal_ne_top n μs (fun i g hg => h i g hg) f hf

end Tensorization

/-- FIN004: bounded comparison, tensorization and covariance. -/
theorem bounded_comparison_tensorization_and_covariance.{w} :
    (∀ {α : Type w} [MeasurableSpace α] {Q P : Measure α} [IsProbabilityMeasure Q]
      [IsProbabilityMeasure P] {ρ : α → ℝ} {K : ℝ},
      P = Q.withDensity (fun x => ENNReal.ofReal (ρ x)) → (∀ x, 0 ≤ ρ x) →
      (∀ x y, ρ x ≤ Real.exp K * ρ y) →
      ∀ {Sm : (α → ℝ) → Prop} {Γ : (α → ℝ) → α → ℝ≥0∞}, (∀ f, Sm f → MemLp f 2 Q) →
      ∀ {C : ℝ}, (PoincareAt Q Sm Γ C → PoincareAt P Sm Γ (Real.exp K * C)) ∧
        (LogSobolevAt Q Sm Γ C → LogSobolevAt P Sm Γ (Real.exp K * C))) ∧
    (∀ {α : Type w} [MeasurableSpace α] {n : ℕ} (μs : Fin n → Measure α)
      [∀ i, IsProbabilityMeasure (μs i)] {Sm : (α → ℝ) → Prop} {Γ : (α → ℝ) → α → ℝ≥0∞} {C : ℝ},
      ((∀ i, PoincareAt (μs i) Sm Γ C) → ∀ f, TP Sm Γ μs f →
        evariance f (Measure.pi μs) ≤
          ENNReal.ofReal C * ∫⁻ x, ∑ i, Γ (slice i f x) (x i) ∂Measure.pi μs) ∧
      ((∀ i, LogSobolevAt (μs i) Sm Γ C) → ∀ f, TP Sm Γ μs f →
        DGPS.homogeneousEntropy (Measure.pi μs) (fun x => f x ^ 2) ≤
          ENNReal.ofReal C * ∫⁻ x, ∑ i, Γ (slice i f x) (x i) ∂Measure.pi μs)) ∧
    (∀ {Ω : Type w} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N m : ℕ}
      {φ : Fin N → Ω → EuclideanSpace ℝ (Fin m)}, (∀ i, Measurable (φ i)) → iIndepFun φ μ →
      ∀ {L : ℝ}, (∀ i ω, ‖φ i ω‖ ≤ L) → traceCov (fun ω => ∑ i, φ i ω) μ ≤ N * L ^ 2) :=
  ⟨fun hP hρ0 hosc _ _ hmem _ =>
      ⟨fun hQ => poincare_comparison hP hρ0 hosc hmem hQ,
        fun hQ => logSobolev_comparison hP hρ0 hosc hmem hQ⟩,
    fun μs _ _ _ _ => ⟨fun h f hf => poincare_tensorization μs h f hf,
        fun h f hf => logSobolev_tensorization μs h f hf⟩,
    fun hmeas hind _ hL => traceCov_sum_le hmeas hind hL⟩

end DGPS.FiniteN.Tools.BoundedComparison

namespace DGPS.FiniteN

/-- Interface name from `declaration_ownership.json` (FIN004). -/
alias bounded_comparison_tensorization_and_covariance :=
  DGPS.FiniteN.Tools.BoundedComparison.bounded_comparison_tensorization_and_covariance

end DGPS.FiniteN

