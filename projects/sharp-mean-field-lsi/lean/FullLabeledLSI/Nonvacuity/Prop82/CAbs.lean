import SharpSymmetricLSI.Infra.ChainRule
import SharpSymmetricLSI.Paper.CircleLSIExt
open MeasureTheory Filter Topology
open scoped ENNReal Real ContDiff
namespace SharpLSI.FL.Prop82

open SharpLSI

/-- Smooth approximation of `|·|`. -/
noncomputable def absApprox (j : ℕ) (s : ℝ) : ℝ := Real.sqrt (s ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2)

private lemma absApprox_pos (j : ℕ) (s : ℝ) : 0 < s ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2 := by
  have : 0 < (1 / ((j : ℝ) + 1)) ^ 2 := by positivity
  positivity

lemma absApprox_contDiff (j : ℕ) : ContDiff ℝ 1 (absApprox j) := by
  unfold absApprox
  refine ContDiff.sqrt (by fun_prop) fun s => (absApprox_pos j s).ne'

lemma absApprox_hasDerivAt (j : ℕ) (s : ℝ) :
    HasDerivAt (absApprox j) (s / Real.sqrt (s ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2)) s := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_pow 2 s).add_const ((1 / ((j : ℝ) + 1)) ^ 2))
  have h2 := h1.sqrt (absApprox_pos j s).ne'
  have hs : 0 < Real.sqrt (s ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) := Real.sqrt_pos.mpr (absApprox_pos j s)
  have e : absApprox j = fun y => Real.sqrt (y ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) := rfl
  rw [e]
  convert h2 using 1
  field_simp

lemma absApprox_deriv (j : ℕ) (s : ℝ) :
    deriv (absApprox j) s = s / Real.sqrt (s ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) :=
  (absApprox_hasDerivAt j s).deriv

lemma absApprox_deriv_abs_le (j : ℕ) (t : ℝ) : |deriv (absApprox j) t| ≤ 1 := by
  rw [absApprox_deriv]
  have hs : 0 < Real.sqrt (t ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) :=
    Real.sqrt_pos.mpr (absApprox_pos j t)
  rw [abs_div, abs_of_pos hs, div_le_one hs]
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (1 / ((j : ℝ) + 1))])

lemma absApprox_unif {ε : ℝ} (hε : 0 < ε) : ∀ᶠ j : ℕ in atTop, ∀ t, abs (absApprox j t - |t|) ≤ ε := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  filter_upwards [h.eventually (Iic_mem_nhds hε)] with j hj t
  have hj' : 1 / ((j : ℝ) + 1) ≤ ε := hj
  have h0 : 0 ≤ 1 / ((j : ℝ) + 1) := by positivity
  have hA : |t| ≤ absApprox j t := by
    unfold absApprox
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (1 / ((j : ℝ) + 1))])
  have hB : absApprox j t ≤ |t| + 1 / ((j : ℝ) + 1) := by
    unfold absApprox
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_abs t, abs_nonneg t]
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- The sign function `s / |s|` (with value `0` at `0`). -/
noncomputable def sgn (s : ℝ) : ℝ := s / |s|

lemma sgn_measurable : Measurable sgn := measurable_id.div measurable_id.abs

lemma sgn_abs_le (s : ℝ) : |sgn s| ≤ 1 := by
  unfold sgn
  rw [abs_div, abs_abs]
  rcases eq_or_ne |s| 0 with h | h
  · rw [h]; simp
  · rw [div_self h]

lemma absApprox_tendsto (t : ℝ) :
    Tendsto (fun j => deriv (absApprox j) t) atTop (𝓝 (sgn t)) := by
  simp_rw [absApprox_deriv]
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [sgn]
  · have h1 : Tendsto (fun j : ℕ => t ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2) atTop (𝓝 (t ^ 2 + 0 ^ 2)) :=
      tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2)
    have h2 := (Real.continuous_sqrt.tendsto _).comp h1
    have h3 : Real.sqrt (t ^ 2 + 0 ^ 2) = |t| := by simp [Real.sqrt_sq_eq_abs]
    rw [h3] at h2
    have := (tendsto_const_nhds (x := t)).div h2 (abs_ne_zero.mpr h)
    exact this

theorem isWeakGrad_abs {w : Torus 1 → ℝ} {g : Torus 1 → Fin 1 → ℝ}
    (h : IsWeakGrad w g) (hw : Integrable w (haar 1)) (hg : ∀ k, Integrable (fun y => g y k) (haar 1)) :
    IsWeakGrad (fun y => |w y|) (fun y k => sgn (w y) * g y k) :=
  isWeakGrad_comp_limit h hw hg (fun j => absApprox_contDiff j) (L := 1)
    (fun j t => absApprox_deriv_abs_le j t) continuous_abs sgn_measurable
    (fun _ hε => absApprox_unif hε) absApprox_tendsto

theorem memH1_abs_div {w : Torus 1 → ℝ} (hw : MemH1 (haar 1) w) {c : ℝ} (hc : 0 < c) :
    MemH1 (haar 1) (fun x => |w x| / c) ∧
    (∀ᵐ x ∂(haar 1), weakGrad (fun y => |w y| / c) x 0 ^ 2 ≤ weakGrad w x 0 ^ 2 / c ^ 2) := by
  have : IsProbabilityMeasure (haar 1) := haar_isProbabilityMeasure 1
  have h := isWeakGrad_weakGrad hw.1
  have hwi : Integrable w (haar 1) := hw.2.1.integrable (by norm_num)
  have hgL := memLp_weakGrad_zero hw
  have hgi : ∀ k : Fin 1, Integrable (fun y => weakGrad w y k) (haar 1) := by
    intro k
    have : k = 0 := Subsingleton.elim _ _
    subst this
    exact hgL.integrable (by norm_num)
  have h1 := isWeakGrad_abs h hwi hgi
  have h2 := h1.cmul c⁻¹
  have e1 : (fun y => c⁻¹ * |w y|) = fun y => |w y| / c := by
    funext y; rw [div_eq_inv_mul]
  rw [e1] at h2
  have hae := weakGrad_ae_eq h2
  have hbd : ∀ᵐ x ∂(haar 1), |weakGrad (fun y => |w y| / c) x 0| ≤ c⁻¹ * |weakGrad w x 0| := by
    filter_upwards [hae] with x hx
    rw [hx]
    show |c⁻¹ * (sgn (w x) * weakGrad w x 0)| ≤ _
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hc)]
    gcongr
    calc |sgn (w x)| * |weakGrad w x 0| ≤ 1 * |weakGrad w x 0| := by
          gcongr; exact sgn_abs_le _
      _ = _ := one_mul _
  have hwc := hw.2.1.const_mul c⁻¹
  have hsq : ∀ x, Real.sqrt (sqNorm (weakGrad (fun y => |w y| / c) x)) =
      |weakGrad (fun y => |w y| / c) x 0| := by
    intro x
    simp [sqNorm, Real.sqrt_sq_eq_abs]
  refine ⟨⟨⟨_, h2⟩, ?_, ?_⟩, ?_⟩
  · refine MemLp.of_le hwc h2.aestronglyMeasurable_fun (Eventually.of_forall fun x => le_of_eq ?_)
    simp only [Real.norm_eq_abs, abs_div, abs_abs, abs_mul, abs_of_pos hc, abs_of_pos (inv_pos.mpr hc)]
    rw [div_eq_inv_mul]
  · have hg2 := hgL.const_mul c⁻¹
    refine MemLp.of_le hg2.norm ?_ ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable
        (isWeakGrad_weakGrad (u := fun y => |w y| / c) ⟨_, h2⟩).aestronglyMeasurable_sqNorm
    · filter_upwards [hbd] with x hx
      rw [hsq x]
      simp only [Real.norm_eq_abs, abs_abs, abs_mul, abs_of_pos (inv_pos.mpr hc)]
      exact hx
  · filter_upwards [hbd] with x hx
    have h3 : weakGrad (fun y => |w y| / c) x 0 ^ 2 ≤ (c⁻¹ * |weakGrad w x 0|) ^ 2 := by
      rw [← sq_abs (weakGrad (fun y => |w y| / c) x 0)]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    calc weakGrad (fun y => |w y| / c) x 0 ^ 2 ≤ (c⁻¹ * |weakGrad w x 0|) ^ 2 := h3
      _ = weakGrad w x 0 ^ 2 / c ^ 2 := by rw [mul_pow, sq_abs]; field_simp

end SharpLSI.FL.Prop82
