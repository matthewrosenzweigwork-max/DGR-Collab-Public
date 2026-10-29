import FullLabeledLSI.Paper.Sec3DiluteC
import SharpSymmetricLSI.Paper.TorusLSI

/-!
# Proposition 3.3 (≤), part D: truncation and Fatou

For `f ∈ H¹(q)` (with `q` bounded below): `f ∈ H¹(haar)`, `min(|f|, M)` is a weak-gradient function
with `|∇ min(|f|, M)| ≤ |∇f|`, and `Ent(f²) ≤ liminf_n Ent(min(|f|, n)²)`.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ}

theorem haar_le_smul_densMeasure {q : Torus d → ℝ} {c : ℝ} (hc : 0 < c) (hq : ∀ x, c ≤ q x) :
    haar d ≤ ENNReal.ofReal (1 / c) • densMeasure q := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  unfold densMeasure
  rw [withDensity_apply _ hs]
  have h1 : ENNReal.ofReal c * haar d s ≤ ∫⁻ x in s, ENNReal.ofReal (q x) ∂haar d := by
    calc ENNReal.ofReal c * haar d s = ∫⁻ _ in s, ENNReal.ofReal c ∂haar d := by
          rw [setLIntegral_const]
      _ ≤ _ := setLIntegral_mono' hs fun x _ => ENNReal.ofReal_le_ofReal (hq x)
  calc haar d s = ENNReal.ofReal (1 / c) * (ENNReal.ofReal c * haar d s) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hc.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ _ := by gcongr

theorem memH1_haar_of_dens {q f : Torus d → ℝ} {c : ℝ} (hc : 0 < c) (hq : ∀ x, c ≤ q x)
    (h : MemH1 (densMeasure q) f) : MemH1 (haar d) f :=
  ⟨h.1, h.2.1.of_measure_le_smul ENNReal.ofReal_ne_top (haar_le_smul_densMeasure hc hq),
    h.2.2.of_measure_le_smul ENNReal.ofReal_ne_top (haar_le_smul_densMeasure hc hq)⟩

theorem ent_sq_ne_top {q f : Torus d → ℝ} {c C : ℝ} (hc : 0 < c) (hbd : ∀ x, c ≤ q x ∧ q x ≤ C)
    (hq1 : ∫ x, q x ∂haar d = 1) (hqm : Measurable q) (hf : MemH1 (densMeasure q) f) :
    ent (densMeasure q) (fun x => f x ^ 2) ≠ ⊤ := by
  haveI : IsProbabilityMeasure (densMeasure q) :=
    isProbabilityMeasure_densMeasure' (fun x => (hc.trans_le (hbd x).1).le) hq1
  have hlsi := reference_lsi hc hbd hq1 hqm hf
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (dirichlet_lt_top hf).ne)
    hlsi

theorem dirichlet_densMeasure_eq {q f : Torus d → ℝ} (hqm : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (hf : HasWeakGrad f) :
    dirichlet (densMeasure q) f =
      ∫⁻ x, ENNReal.ofReal (q x * sqNorm (weakGrad f x)) ∂haar d := by
  unfold dirichlet densMeasure
  have hb : AEMeasurable (fun x => ENNReal.ofReal (q x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hqm.aemeasurable
  have hg : AEMeasurable (fun x => ENNReal.ofReal (sqNorm (weakGrad f x))) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (isWeakGrad_weakGrad hf).aestronglyMeasurable_sqNorm.aemeasurable
  rw [lintegral_withDensity_eq_lintegral_mul₀ hb hg]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul (hq0 x)]

theorem exists_trunc_grad {f : Torus d → ℝ} (hf : MemH1 (haar d) f) (M : ℝ) :
    ∃ G : Torus d → Fin d → ℝ, IsWeakGrad (fun x => min |f x| M) G ∧
      (∀ k, MemLp (fun y => G y k) 2 (haar d)) ∧
      ∀ x, sqNorm (G x) ≤ sqNorm (weakGrad f x) := by
  have hw := isWeakGrad_weakGrad hf.1
  have hfi : Integrable f volume := hf.2.1.integrable one_le_two
  have hgL : ∀ k, MemLp (fun y => weakGrad f y k) 2 (haar d) := memLp_comp_weakGrad hf
  have hgi : ∀ k, Integrable (fun y => weakGrad f y k) volume := fun k =>
    (hgL k).integrable one_le_two
  have habs := isWeakGrad_abs hw hfi hgi
  obtain ⟨ga, hga, hgale⟩ : ∃ ga : Torus d → Fin d → ℝ, IsWeakGrad (fun y => |f y|) ga ∧
      ∀ y k, |ga y k| ≤ |weakGrad f y k| := by
    refine ⟨_, habs, fun y k => ?_⟩
    split_ifs <;> simp
  have hgai : ∀ k, Integrable (fun y => ga y k) volume := fun k =>
    Integrable.mono' (hgi k).norm (hga.aestronglyMeasurable_grad k)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hgale y k)
  have hmin := isWeakGrad_min hga hfi.abs hgai M
  have hle : ∀ y k, |(if M < |f y| then (0 : ℝ) else ga y k)| ≤ |weakGrad f y k| := fun y k => by
    split_ifs
    · simp
    · exact hgale y k
  refine ⟨_, hmin, fun k => ?_, fun x => ?_⟩
  · refine (hgL k).mono (hmin.aestronglyMeasurable_grad k) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hle y k
  · have := sqNorm_le_of_abs_le (A := 1) (v := fun k => if M < |f x| then (0 : ℝ) else ga x k)
      (w := weakGrad f x) (fun k => by rw [one_mul]; exact hle x k)
    simpa using this

theorem ent_le_liminf_trunc {P : Measure (Torus d)} [IsProbabilityMeasure P] {f : Torus d → ℝ}
    (hf : MemLp f 2 P) :
    ent P (fun x => f x ^ 2) ≤
      liminf (fun n : ℕ => ent P (fun x => (min |f x| (n : ℝ)) ^ 2)) atTop := by
  have hm : ∀ n : ℕ, AEStronglyMeasurable (fun x => (min |f x| (n : ℝ)) ^ 2) P := fun n =>
    ((continuous_abs.min continuous_const).comp_aestronglyMeasurable hf.aestronglyMeasurable).pow 2
  have hb : ∀ (n : ℕ) x, (min |f x| (n : ℝ)) ^ 2 ≤ f x ^ 2 := fun n x => by
    rw [← sq_abs (f x)]
    exact pow_le_pow_left₀ (le_min (abs_nonneg _) (Nat.cast_nonneg n)) (min_le_left _ _) 2
  have hFi : ∀ n : ℕ, Integrable (fun x => (min |f x| (n : ℝ)) ^ 2) P := fun n =>
    Integrable.of_bound (C := (n : ℝ) ^ 2) (hm n) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (le_min (abs_nonneg _) (Nat.cast_nonneg n)) (min_le_right _ _) 2)
  have hae : ∀ x, Tendsto (fun n : ℕ => (min |f x| (n : ℝ)) ^ 2) atTop (𝓝 (f x ^ 2)) := by
    intro x
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|f x|⌉₊] with n hn
    have : |f x| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [min_eq_left this, sq_abs]
  refine ent_le_liminf hFi hf.integrable_sq (Eventually.of_forall hae) ?_
  exact tendsto_integral_of_dominated_convergence (fun x => f x ^ 2) hm hf.integrable_sq
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb n x)
    (Eventually.of_forall hae)

end SharpLSI.FL
