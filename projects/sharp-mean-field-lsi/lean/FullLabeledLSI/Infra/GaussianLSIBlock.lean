import SharpSymmetricLSI.Paper.GaussLSI2
import SharpSymmetricLSI.Paper.GaussForm19
import SharpSymmetricLSI.Paper.GaussForm10

/-!
# Gaussian log-Sobolev for smooth functions of finite energy (plan, section 4)

* `gross_smooth`: for `H ∈ C^∞(ℝⁿ)` with `H ∈ L²(γ_n)` and `|∇H|² ∈ L¹(γ_n)`,
  `Ent_{γ_n}(H²) ≤ 2 ∫ |∇H|² dγ_n` (cutoffs `χ_R H`, `gross_cc`, Fatou for the entropy).
* `gauss_lsi_smooth_of`, `gauss_lsi_smooth`: the same for `ν = (γ_M).map (A ·)` with `A Aᵀ = S`
  (resp. `A = √S`) and weights `lam'` with `ρ vᵀSv ≤ ∑ lam'_k v_k²`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset InformationTheory Matrix
open scoped ENNReal ContDiff MatrixOrder

namespace SharpLSI.FL

open SharpLSI

section generic
variable {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]

theorem ent_sq_eq_gen {f : α → ℝ} (hf : MemLp f 2 P) :
    ent P (fun x => f x ^ 2) = ∫⁻ x, ENNReal.ofReal ((∫ y, f y ^ 2 ∂P) *
      klFun (f x ^ 2 / ∫ y, f y ^ 2 ∂P)) ∂P := by
  unfold ent; rw [if_pos hf.integrable_sq]

/-- Fatou for the entropy along an a.e.-convergent sequence with converging second moments. -/
theorem ent_sq_le_liminf_of_ae_gen {u : ℕ → α → ℝ} {f : α → ℝ}
    (hu : ∀ n, MemLp (u n) 2 P) (hf : MemLp f 2 P)
    (hc : Tendsto (fun n => ∫ x, u n x ^ 2 ∂P) atTop (𝓝 (∫ x, f x ^ 2 ∂P)))
    (hae : ∀ᵐ x ∂P, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    ent P (fun x => f x ^ 2) ≤ liminf (fun n => ent P (fun x => u n x ^ 2)) atTop := by
  set c := ∫ x, f x ^ 2 ∂P
  rcases (integral_nonneg (fun x => sq_nonneg (f x)) : 0 ≤ c).eq_or_lt with h0 | hpos
  · rw [ent_sq_eq_gen hf, ← h0]; simp
  rw [ent_sq_eq_gen hf]
  simp_rw [ent_sq_eq_gen (hu _)]
  have hmeas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal ((∫ y, u n y ^ 2 ∂P) *
      klFun (u n x ^ 2 / ∫ y, u n y ^ 2 ∂P))) P := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_const.mul (continuous_klFun.comp
        ((continuous_pow 2).div_const _))).comp_aestronglyMeasurable
        (hu n).aestronglyMeasurable).aemeasurable
  refine le_trans ?_ (lintegral_liminf_le' hmeas)
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with x hx
  have hlim : Tendsto (fun n => ENNReal.ofReal ((∫ y, u n y ^ 2 ∂P) *
      klFun (u n x ^ 2 / ∫ y, u n y ^ 2 ∂P))) atTop
      (𝓝 (ENNReal.ofReal (c * klFun (f x ^ 2 / c)))) :=
    ENNReal.tendsto_ofReal (hc.mul ((continuous_klFun.tendsto _).comp
      ((hx.pow 2).div hc hpos.ne')))
  rw [hlim.liminf_eq]

/-- `ent = ofReal ∘ entR` for bounded nonnegative measurable functions. -/
theorem ent_eq_ofReal_entR_gen {u : α → ℝ} (hu : AEStronglyMeasurable u P)
    (hu0 : ∀ z, 0 ≤ u z) {B : ℝ} (huB : ∀ z, u z ≤ B) :
    ent P u = ENNReal.ofReal (entR P u) := by
  have hB0 : 0 ≤ B ∨ IsEmpty α := by
    by_cases h : Nonempty α
    · obtain ⟨z⟩ := h; exact Or.inl ((hu0 z).trans (huB z))
    · exact Or.inr (not_nonempty_iff.1 h)
  have hB0' : 0 ≤ B := by
    rcases hB0 with h | h
    · exact h
    · exact absurd (inferInstance : IsProbabilityMeasure P).measure_univ
        (by simp [Set.univ_eq_empty_iff.2 h])
  have hi : Integrable u P := Integrable.of_bound hu B
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hu0 z)]; exact huB z)
  have hlog : Integrable (fun z => u z * Real.log (u z)) P := by
    refine Integrable.of_bound ((Real.continuous_mul_log.comp_aestronglyMeasurable hu))
      (B ^ 2 + 1) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hu0 z
    have h2 := huB z
    rcases h1.eq_or_lt with h0 | hpos
    · rw [← h0]; simp only [zero_mul]; constructor <;> nlinarith [sq_nonneg B]
    have hl := Real.one_sub_inv_le_log_of_pos hpos
    have hlu := Real.log_le_sub_one_of_pos hpos
    have e1 : u z * (1 - (u z)⁻¹) = u z - 1 := by field_simp
    constructor
    · have := mul_le_mul_of_nonneg_left hl h1
      nlinarith [e1]
    · have := mul_le_mul_of_nonneg_left hlu h1
      nlinarith
  rw [ent_eq_formula P u hu0 hi hlog]
  rfl

end generic

section gross
variable {n : ℕ}

theorem gross_smooth {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (hL2 : MemLp H 2 (gpi n))
    (hE : Integrable (fun x => ∑ k, fderiv ℝ H x (Pi.single k 1) ^ 2) (gpi n)) :
    ent (gpi n) (fun x => H x ^ 2) ≤
      ENNReal.ofReal (2 * ∫ x, ∑ k, fderiv ℝ H x (Pi.single k 1) ^ 2 ∂gpi n) := by
  obtain ⟨M, hM0, hM⟩ := exists_fderiv_chiR_bound n
  set Hm : ℕ → (Fin n → ℝ) → ℝ := fun m y => chiR n ((m : ℝ) + 1) y * H y with hHm
  have hHmc : ∀ m, ContDiff ℝ ∞ (Hm m) := fun m => (contDiff_chiR n _).mul hH
  have hHcont : Continuous H := hH.continuous
  have hcd : Continuous fun x => fderiv ℝ H x := hH.continuous_fderiv (by simp)
  have hpos : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 1 := fun m => by positivity
  have hev : ∀ x : Fin n → ℝ, ∀ᶠ m : ℕ in atTop, ‖x‖ < (m : ℝ) + 1 := fun x => by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with m hm
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hHm_abs : ∀ m x, |Hm m x| ≤ |H x| := fun m x => by
    simp only [hHm, abs_mul]
    rw [abs_of_nonneg (chiR_nonneg _ _ _)]
    calc chiR n ((m : ℝ) + 1) x * |H x| ≤ 1 * |H x| :=
          mul_le_mul_of_nonneg_right (chiR_le_one _ _ _) (abs_nonneg _)
      _ = |H x| := one_mul _
  have hHm_ev : ∀ x, ∀ᶠ m : ℕ in atTop, Hm m x = H x := fun x => by
    filter_upwards [hev x] with m hm
    simp only [hHm, chiR_eq_one (hpos m) hm.le, one_mul]
  -- the cut-offs
  have hcs : ∀ m, HasCompactSupport (Hm m) := fun m =>
    (hasCompactSupport_chiR (hpos m)).mul_right
  have hbdd : ∀ m, ∃ B, ∀ x, |Hm m x| ≤ B := fun m => by
    obtain ⟨B, hB⟩ := (hcs m).exists_bound_of_continuous (hHmc m).continuous
    exact ⟨B, fun x => by simpa using hB x⟩
  have hMemLp : ∀ m, MemLp (Hm m) 2 (gpi n) := fun m =>
    hL2.mono (hHmc m).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hHm_abs m x)
  have hent_m : ∀ m, ent (gpi n) (fun x => Hm m x ^ 2) =
      ENNReal.ofReal (entR (gpi n) (fun x => Hm m x ^ 2)) := fun m => by
    obtain ⟨B, hB⟩ := hbdd m
    refine ent_eq_ofReal_entR_gen ((hHmc m).continuous.pow 2).aestronglyMeasurable
      (fun z => sq_nonneg _) (B := B ^ 2) (fun z => ?_)
    have := pow_le_pow_left₀ (abs_nonneg _) (hB z) 2
    rwa [sq_abs] at this
  have hgross : ∀ m, entR (gpi n) (fun x => Hm m x ^ 2) ≤
      2 * ∫ x, ∑ k, fderiv ℝ (Hm m) x (Pi.single k 1) ^ 2 ∂gpi n := fun m =>
    gross_cc (hHmc m) (hcs m)
  -- lower semicontinuity
  have hc : Tendsto (fun m => ∫ x, Hm m x ^ 2 ∂gpi n) atTop (𝓝 (∫ x, H x ^ 2 ∂gpi n)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => H x ^ 2)
      (fun m => ((hHmc m).continuous.pow 2).aestronglyMeasurable) hL2.integrable_sq
      (fun m => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := pow_le_pow_left₀ (abs_nonneg _) (hHm_abs m x) 2
      rwa [sq_abs, sq_abs] at this
    · exact tendsto_const_nhds.congr' ((hHm_ev x).mono fun m hm => by simp only [hm])
  have hae : ∀ᵐ x ∂gpi n, Tendsto (fun m => Hm m x) atTop (𝓝 (H x)) :=
    Eventually.of_forall fun x => tendsto_const_nhds.congr' ((hHm_ev x).mono fun m hm => hm.symm)
  have hlsc := ent_sq_le_liminf_of_ae_gen hMemLp hL2 hc hae
  -- energy convergence
  have hk : ∀ m x (k : Fin n), fderiv ℝ (Hm m) x (Pi.single k 1) ^ 2 ≤
      2 * fderiv ℝ H x (Pi.single k 1) ^ 2 + 2 * (M ^ 2 * H x ^ 2) := fun m x k => by
    rw [hHm, fderiv_chiR_mul hH]
    have h2 : |fderiv ℝ (chiR n ((m : ℝ) + 1)) x (Pi.single k 1)| ≤ M := by
      refine (abs_fderiv_single_le (B := M * ((m : ℝ) + 1)⁻¹) (hM _ (hpos m)) x k).trans ?_
      have : ((m : ℝ) + 1)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
      nlinarith
    set c := fderiv ℝ (chiR n ((m : ℝ) + 1)) x (Pi.single k 1)
    set d := fderiv ℝ H x (Pi.single k 1)
    have hc2 : c ^ 2 ≤ M ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h2 2
      rwa [sq_abs] at this
    have h0 := chiR_nonneg n ((m : ℝ) + 1) x
    have h1 := chiR_le_one n ((m : ℝ) + 1) x
    set χ := chiR n ((m : ℝ) + 1) x
    have ha : (χ * d) ^ 2 ≤ d ^ 2 := by
      rw [mul_pow]
      have : χ ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg d]
    have hb : (H x * c) ^ 2 ≤ M ^ 2 * H x ^ 2 := by
      rw [mul_pow]; nlinarith [sq_nonneg (H x)]
    nlinarith [sq_nonneg (χ * d - H x * c)]
  set g : (Fin n → ℝ) → ℝ := fun x =>
    2 * ∑ k, fderiv ℝ H x (Pi.single k 1) ^ 2 + (2 * n * M ^ 2) * H x ^ 2 with hg
  have hgint : Integrable g (gpi n) :=
    (hE.const_mul 2).add (hL2.integrable_sq.const_mul (2 * n * M ^ 2))
  have hdm_cont : ∀ m, Continuous fun x => ∑ k, fderiv ℝ (Hm m) x (Pi.single k 1) ^ 2 :=
    fun m => by
      have hc' : Continuous fun x => fderiv ℝ (Hm m) x := (hHmc m).continuous_fderiv (by simp)
      exact continuous_finsetSum _ fun k _ => (hc'.clm_apply continuous_const).pow 2
  have hI : Tendsto (fun m => ∫ x, ∑ k, fderiv ℝ (Hm m) x (Pi.single k 1) ^ 2 ∂gpi n) atTop
      (𝓝 (∫ x, ∑ k, fderiv ℝ H x (Pi.single k 1) ^ 2 ∂gpi n)) := by
    refine tendsto_integral_of_dominated_convergence g
      (fun m => (hdm_cont m).aestronglyMeasurable) hgint
      (fun m => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
      calc _ ≤ ∑ k : Fin n, (2 * fderiv ℝ H x (Pi.single k 1) ^ 2 + 2 * (M ^ 2 * H x ^ 2)) :=
            Finset.sum_le_sum fun k _ => hk m x k
        _ = g x := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hg]
            ring
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with m hm
      refine (Finset.sum_congr rfl fun k _ => ?_)
      rw [hHm, fderiv_chiR_mul hH, chiR_eq_one (hpos m) hm.le, fderiv_chiR_eq_zero (hpos m) hm]
      simp
  have hR : Tendsto (fun m => ENNReal.ofReal
      (2 * ∫ x, ∑ k, fderiv ℝ (Hm m) x (Pi.single k 1) ^ 2 ∂gpi n)) atTop
      (𝓝 (ENNReal.ofReal (2 * ∫ x, ∑ k, fderiv ℝ H x (Pi.single k 1) ^ 2 ∂gpi n))) :=
    ENNReal.tendsto_ofReal (hI.const_mul 2)
  calc ent (gpi n) (fun x => H x ^ 2)
      ≤ liminf (fun m => ent (gpi n) (fun x => Hm m x ^ 2)) atTop := hlsc
    _ ≤ liminf (fun m => ENNReal.ofReal
          (2 * ∫ x, ∑ k, fderiv ℝ (Hm m) x (Pi.single k 1) ^ 2 ∂gpi n)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun m => by
          rw [hent_m m]; exact ENNReal.ofReal_le_ofReal (hgross m))
    _ = _ := hR.liminf_eq

end gross


section transport
variable {M : ℕ}

theorem measurable_mulVec (A : Matrix (Fin M) (Fin M) ℝ) :
    Measurable fun y : Fin M → ℝ => A *ᵥ y :=
  (continuous_const.matrix_mulVec continuous_id).measurable

/-- Change of variables for the entropy under a linear image of `γ_M`. -/
theorem ent_map_mulVec (A : Matrix (Fin M) (Fin M) ℝ) {u : (Fin M → ℝ) → ℝ} (hu : Continuous u) :
    ent ((gpi M).map fun y => A *ᵥ y) u = ent (gpi M) (fun y => u (A *ᵥ y)) := by
  have hm := measurable_mulVec A
  have hint : Integrable u ((gpi M).map fun y => A *ᵥ y) ↔ Integrable (fun y => u (A *ᵥ y)) (gpi M) :=
    integrable_map_measure hu.aestronglyMeasurable hm.aemeasurable
  have hI : ∫ y, u y ∂(gpi M).map (fun y => A *ᵥ y) = ∫ y, u (A *ᵥ y) ∂gpi M :=
    integral_map hm.aemeasurable hu.aestronglyMeasurable
  unfold ent
  by_cases h : Integrable u ((gpi M).map fun y => A *ᵥ y)
  · rw [if_pos h, if_pos (hint.1 h), hI]
    rw [lintegral_map _ hm]
    exact (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (continuous_klFun.measurable.comp
        (hu.measurable.div_const _))))
  · rw [if_neg h, if_neg (fun h' => h (hint.2 h'))]

variable {S : Matrix (Fin M) (Fin M) ℝ} (A : Matrix (Fin M) (Fin M) ℝ) (hA : A * Aᵀ = S)

theorem fderiv_comp_mulVec {h : (Fin M → ℝ) → ℝ} (hh : ContDiff ℝ ∞ h) (g : Fin M → ℝ) (k : Fin M) :
    fderiv ℝ (fun y => h (A *ᵥ y)) g (Pi.single k 1) =
      ∑ l, A l k * fderiv ℝ h (A *ᵥ g) (Pi.single l 1) := by
  have hder : fderiv ℝ (fun y => h (matCLM A y)) g = (fderiv ℝ h (matCLM A g)).comp (matCLM A) :=
    ((hh.differentiable (by simp) (matCLM A g)).hasFDerivAt.comp g
      (matCLM A).hasFDerivAt).fderiv
  have e : fderiv ℝ (fun y => h (A *ᵥ y)) g = fderiv ℝ (fun y => h (matCLM A y)) g := rfl
  rw [e, hder, ContinuousLinearMap.comp_apply, matCLM_single, fderiv_apply_sum]
  rfl

include hA in
theorem sum_sq_fderiv_comp {h : (Fin M → ℝ) → ℝ} (hh : ContDiff ℝ ∞ h) (g : Fin M → ℝ) :
    ∑ k, fderiv ℝ (fun y => h (A *ᵥ y)) g (Pi.single k 1) ^ 2 =
      (fun l => fderiv ℝ h (A *ᵥ g) (Pi.single l 1)) ⬝ᵥ
        (S *ᵥ fun l => fderiv ℝ h (A *ᵥ g) (Pi.single l 1)) := by
  simp_rw [fderiv_comp_mulVec A hh g]
  rw [sum_sq_mulVec_transpose, hA]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  ring

include hA in
/-- **Gaussian log-Sobolev for smooth functions of finite energy**, general factor `A Aᵀ = S`. -/
theorem gauss_lsi_smooth_of {ρ : ℝ} (hρ : 0 ≤ ρ) {lam' : Fin M → ℝ}
    (hlam : ∀ v : Fin M → ℝ, ρ * (v ⬝ᵥ (S *ᵥ v)) ≤ ∑ k, lam' k * v k ^ 2)
    {h : (Fin M → ℝ) → ℝ} (hh : ContDiff ℝ ∞ h)
    (hL2 : MemLp h 2 ((gpi M).map fun y => A *ᵥ y))
    (hE : Integrable (fun x => ∑ k, lam' k * fderiv ℝ h x (Pi.single k 1) ^ 2)
      ((gpi M).map fun y => A *ᵥ y)) :
    ENNReal.ofReal (ρ / 2) * ent ((gpi M).map fun y => A *ᵥ y) (fun x => h x ^ 2) ≤
      ENNReal.ofReal (∫ x, ∑ k, lam' k * fderiv ℝ h x (Pi.single k 1) ^ 2
        ∂(gpi M).map fun y => A *ᵥ y) := by
  have hm := measurable_mulVec A
  have hhc : Continuous h := hh.continuous
  have hdc : ∀ k : Fin M, Continuous fun x => fderiv ℝ h x (Pi.single k 1) := fun k =>
    (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have hLc : Continuous fun x => ∑ k, lam' k * fderiv ℝ h x (Pi.single k 1) ^ 2 :=
    continuous_finsetSum _ fun k _ => continuous_const.mul ((hdc k).pow 2)
  set H : (Fin M → ℝ) → ℝ := fun y => h (A *ᵥ y) with hH
  have hHd : ContDiff ℝ ∞ H := hh.comp (matCLM A).contDiff
  set L : (Fin M → ℝ) → ℝ := fun x => ∑ k, lam' k * fderiv ℝ h x (Pi.single k 1) ^ 2 with hLdef
  have hLint : Integrable (fun y => L (A *ᵥ y)) (gpi M) :=
    (integrable_map_measure hLc.aestronglyMeasurable hm.aemeasurable).1 hE
  have hLI : ∫ x, L x ∂(gpi M).map (fun y => A *ᵥ y) = ∫ y, L (A *ᵥ y) ∂gpi M :=
    integral_map hm.aemeasurable hLc.aestronglyMeasurable
  have hent := ent_map_mulVec A (u := fun x => h x ^ 2) (hhc.pow 2)
  rw [hent, hLI]
  rcases hρ.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  -- pointwise comparison
  have hpt : ∀ y, ρ * ∑ k, fderiv ℝ H y (Pi.single k 1) ^ 2 ≤ L (A *ᵥ y) := fun y => by
    rw [hH, sum_sq_fderiv_comp A hA hh y]
    exact hlam _
  have hHL2 : MemLp H 2 (gpi M) := by
    exact (memLp_map_measure_iff hhc.aestronglyMeasurable hm.aemeasurable).1 hL2
  have hEc : Continuous fun y => ∑ k, fderiv ℝ H y (Pi.single k 1) ^ 2 := by
    have hc' : Continuous fun x => fderiv ℝ H x := hHd.continuous_fderiv (by simp)
    exact continuous_finsetSum _ fun k _ => (hc'.clm_apply continuous_const).pow 2
  have hEint : Integrable (fun y => ∑ k, fderiv ℝ H y (Pi.single k 1) ^ 2) (gpi M) := by
    refine (hLint.div_const ρ).mono' hEc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _),
      le_div_iff₀ hpos]
    linarith [hpt y]
  have hgs := gross_smooth hHd hHL2 hEint
  calc ENNReal.ofReal (ρ / 2) * ent (gpi M) (fun y => h (A *ᵥ y) ^ 2)
      ≤ ENNReal.ofReal (ρ / 2) * ENNReal.ofReal
          (2 * ∫ x, ∑ k, fderiv ℝ H x (Pi.single k 1) ^ 2 ∂gpi M) := by gcongr
    _ = ENNReal.ofReal (∫ y, ρ * ∑ k, fderiv ℝ H y (Pi.single k 1) ^ 2 ∂gpi M) := by
        rw [← ENNReal.ofReal_mul (by positivity), integral_const_mul]
        congr 1; ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (integral_mono (hEint.const_mul ρ) hLint hpt)

/-- **Gaussian log-Sobolev for smooth functions of finite energy** (plan, section 4):
`S` positive semidefinite, `ν = (γ_M).map (√S ·)`. -/
theorem gauss_lsi_smooth (hS : S.PosSemidef) {ρ : ℝ} (hρ : 0 ≤ ρ) {lam' : Fin M → ℝ}
    (hlam : ∀ v : Fin M → ℝ, ρ * (v ⬝ᵥ (S *ᵥ v)) ≤ ∑ k, lam' k * v k ^ 2)
    {h : (Fin M → ℝ) → ℝ} (hh : ContDiff ℝ ∞ h)
    (hL2 : MemLp h 2 ((gpi M).map fun y => CFC.sqrt S *ᵥ y))
    (hE : Integrable (fun x => ∑ k, lam' k * fderiv ℝ h x (Pi.single k 1) ^ 2)
      ((gpi M).map fun y => CFC.sqrt S *ᵥ y)) :
    ENNReal.ofReal (ρ / 2) * ent ((gpi M).map fun y => CFC.sqrt S *ᵥ y) (fun x => h x ^ 2) ≤
      ENNReal.ofReal (∫ x, ∑ k, lam' k * fderiv ℝ h x (Pi.single k 1) ^ 2
        ∂(gpi M).map fun y => CFC.sqrt S *ᵥ y) :=
  gauss_lsi_smooth_of (CFC.sqrt S) (sqrt_mul_transpose hS) hρ hlam hh hL2 hE

end transport

end SharpLSI.FL
