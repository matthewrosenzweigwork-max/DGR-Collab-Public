import SharpSymmetricLSI.Paper.CosineD5

/-!
# The `d`-dimensional cosine model (6): the mode-1 upper bound `r_* ≤ a(1 + κ/2)`

Along `ρ_ε(x) = 1 + ε cos 2πxᵢ`, the gap and the dissipation coincide with those of the circle
model along `1 + ε cos 2πx` (`gap_cosDmode1`, `dissipation_cosDmode1`): `Aᵢ = ε/2` and all
other `Aₖ`, `Bₖ` vanish, and the only nonzero partial derivative is `∂ᵢ`. The circle quotient
`tendsto_quotient_rho1` then gives `r_* ≤ a(1 + κ/2)` (`rStar_le_cosWd_mode1`).
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal Real

namespace SharpLSI

variable {d : ℕ}

/-! ### The profile `s ↦ √(1 + ε cos 2πs)` -/

theorem one_add_mul_cos_pos {ε : ℝ} (hε : |ε| < 1) (s : ℝ) : 0 < 1 + ε * Real.cos (2 * π * s) := by
  have : |ε * Real.cos (2 * π * s)| < 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg ε, abs_nonneg (Real.cos (2 * π * s)),
      Real.abs_cos_le_one (2 * π * s)]
  linarith [neg_abs_le (ε * Real.cos (2 * π * s))]

/-- `s ↦ √(1 + ε cos 2πs)`. -/
noncomputable def cosDg (ε s : ℝ) : ℝ := Real.sqrt (1 + ε * Real.cos (2 * π * s))

theorem hasDerivAt_cosDg {ε : ℝ} (hε : |ε| < 1) (s : ℝ) :
    HasDerivAt (cosDg ε) (ε * (-(2 * π) * Real.sin (2 * π * s)) / (2 * cosDg ε s)) s := by
  have h1 : HasDerivAt (fun s => 1 + ε * Real.cos (2 * π * s))
      (ε * (-(2 * π) * Real.sin (2 * π * s))) s := by
    have := (((hasDerivAt_id' s).const_mul (2 * π)).cos.const_mul ε).const_add 1
    convert this using 1
    ring
  exact h1.sqrt (one_add_mul_cos_pos hε s).ne'

theorem contDiff_cosDg {ε : ℝ} (hε : |ε| < 1) : ContDiff ℝ ⊤ (cosDg ε) :=
  (contDiff_const.add (contDiff_const.mul (Real.contDiff_cos.comp
    (contDiff_const.mul contDiff_id)))).sqrt fun s => (one_add_mul_cos_pos hε s).ne'

theorem cosDg_sq {ε : ℝ} (hε : |ε| < 1) (s : ℝ) :
    cosDg ε s ^ 2 = 1 + ε * Real.cos (2 * π * s) :=
  Real.sq_sqrt (one_add_mul_cos_pos hε s).le

theorem cosDg_pos {ε : ℝ} (hε : |ε| < 1) (s : ℝ) : 0 < cosDg ε s :=
  Real.sqrt_pos.2 (one_add_mul_cos_pos hε s)

/-! ### Mode 1 -/

/-- `ρ_ε(x) = 1 + ε cos 2πxᵢ`. -/
noncomputable def cosDmode1 (i : Fin d) (ε : ℝ) (x : Torus d) : ℝ := 1 + ε * cosDc i x

theorem cosDmode1_eq (i : Fin d) (ε : ℝ) :
    cosDmode1 i ε = fun x => 1 + ε * gCos (cosDproj i x) := rfl

theorem cosDA_mode1 (i : Fin d) (ε : ℝ) (k : Fin d) :
    cosDA (cosDmode1 i ε) k = if k = i then ε / 2 else 0 := by
  split_ifs with hk
  · subst hk
    unfold cosDA cosDmode1
    rw [show (fun y => cosDc k y * (1 + ε * cosDc k y)) =
      fun y => (fun z => gCos z * (1 + ε * gCos z)) (cosDproj k y) from rfl,
      integral_cosDproj_haar (F := fun z => gCos z * (1 + ε * gCos z)) k
        (continuous_gCos.mul (continuous_const.add (continuous_const.mul continuous_gCos))),
      integral_gCos_rho]
  · refine integral_eq_zero_of_half k fun x => ?_
    simp only [cosDmode1, cosDc_add_half_self, cosDc_add_half_ne hk]
    ring

theorem cosDB_mode1 (i : Fin d) (ε : ℝ) (k : Fin d) : cosDB (cosDmode1 i ε) k = 0 := by
  by_cases hk : k = i
  · subst hk
    unfold cosDB cosDmode1
    rw [show (fun y => cosDs k y * (1 + ε * cosDc k y)) =
      fun y => (fun z => sCos z * (1 + ε * gCos z)) (cosDproj k y) from rfl,
      integral_cosDproj_haar (F := fun z => sCos z * (1 + ε * gCos z)) k
        (continuous_sCos.mul (continuous_const.add (continuous_const.mul continuous_gCos))),
      integral_sCos_rho]
  · refine integral_eq_zero_of_half k fun x => ?_
    simp only [cosDmode1, cosDs_add_half_self, cosDc_add_half_ne hk]
    ring

theorem cosDmode1_nonneg (i : Fin d) {ε : ℝ} (hε : |ε| ≤ 1) (x : Torus d) :
    0 ≤ cosDmode1 i ε x := one_add_mul_nonneg abs_gCos_le hε _

theorem integral_cosDmode1 (i : Fin d) (ε : ℝ) : ∫ x, cosDmode1 i ε x ∂haar d = 1 :=
  integral_comp_mode (cosDPres_proj i) ε

theorem sum_cosDQ_mode1 (i : Fin d) {ε : ℝ} (hε : |ε| ≤ 1) :
    ∑ k, cosDQ k (densMeasure (cosDmode1 i ε)) = ε ^ 2 / 4 := by
  simp_rw [cosDQ_densMeasure (cosDmode1_nonneg i hε) (integral_cosDmode1 i ε), cosDA_mode1,
    cosDB_mode1]
  simp only [ite_pow, Finset.sum_add_distrib]
  simp; ring

theorem sqrt_cosDmode1_lift (i : Fin d) (ε : ℝ) :
    (fun x => Real.sqrt (cosDmode1 i ε x)) ∘ liftT = fun z : Fin d → ℝ => cosDg ε (z i) := by
  funext z
  simp only [Function.comp_apply, cosDmode1, cosDc_liftT, cosDg]

theorem contDiff_sqrt_cosDmode1 (i : Fin d) {ε : ℝ} (hε : |ε| < 1) :
    ContDiff ℝ ⊤ ((fun x => Real.sqrt (cosDmode1 i ε x)) ∘ liftT) := by
  rw [sqrt_cosDmode1_lift]
  exact (contDiff_cosDg hε).comp (contDiff_apply ℝ ℝ i)

theorem memH1_cosDmode1 (i : Fin d) {ε : ℝ} (hε : |ε| < 1) :
    MemH1 (haar d) (fun x => Real.sqrt (cosDmode1 i ε x)) :=
  memH1_of_contDiff ((contDiff_sqrt_cosDmode1 i hε).of_le le_top)

theorem fderiv_sqrt_cosDmode1 (i : Fin d) {ε : ℝ} (hε : |ε| < 1) (z : Fin d → ℝ) (k : Fin d) :
    fderiv ℝ ((fun x => Real.sqrt (cosDmode1 i ε x)) ∘ liftT) z (Pi.single k 1) =
      if k = i then ε * (-(2 * π) * Real.sin (2 * π * z i)) / (2 * cosDg ε (z i)) else 0 := by
  rw [sqrt_cosDmode1_lift]
  have h := (hasDerivAt_cosDg hε (z i)).comp_hasFDerivAt z
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).hasFDerivAt
  rw [show (fun z : Fin d → ℝ => cosDg ε (z i)) = cosDg ε ∘
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) from rfl, h.fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

/-- **The mode-1 dissipation equals that of the circle model.** -/
theorem dissipation_cosDmode1 (κ : ℝ) (i : Fin d) {ε : ℝ} (hε : |ε| < 1) :
    dissipation (fun _ => 0) (cosWd κ) (cosDmode1 i ε) =
      ENNReal.ofReal (ε ^ 2 * ∫ y, F1 κ ε y ∂haar 1) := by
  rw [dissipation_cosWd_eq κ (integral_cosDmode1 i ε) (memH1_cosDmode1 i hε)]
  have hu1 : ContDiff ℝ 1 ((fun x => Real.sqrt (cosDmode1 i ε x)) ∘ liftT) :=
    (contDiff_sqrt_cosDmode1 i hε).of_le le_top
  have hF : Continuous (F1 κ ε) := continuous_F1 κ hε
  rw [← integral_cosDproj_haar i hF, ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal (f := fun x => ε ^ 2 * F1 κ ε (cosDproj i x))
    (integrable_torusD
      (continuous_const.mul (hF.comp (continuous_cosDproj i))))
    (Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (F1_nonneg κ hε _))]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq_of_contDiff hu1] with x hx
  rw [hx]
  simp only [fderiv_sqrt_cosDmode1 i hε, cosDA_mode1, cosDB_mode1]
  congr 1
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_univ i) h)]
  simp only [if_true, zero_mul, add_zero]
  -- the circle computation
  set c := Real.cos (2 * π * secT x i) with hc
  set sn := Real.sin (2 * π * secT x i) with hsn
  set r := cosDg ε (secT x i) with hr
  have hcx : gCos (cosDproj i x) = c := cosDc_secT i x
  have hρx : Real.sqrt (cosDmode1 i ε x) = r := by
    simp only [cosDmode1, hr, cosDg, cosDc_secT]
  have hr2 : r ^ 2 = 1 + ε * c := cosDg_sq hε _
  have hr0 : 0 < r := cosDg_pos hε _
  have hs : sn ^ 2 = 1 - c ^ 2 := by linarith [Real.sin_sq_add_cos_sq (2 * π * secT x i)]
  rw [hρx, cosDs_secT, ← hsn]
  have key : (2 * (ε * (-(2 * π) * sn) / (2 * r)) + κ * r * (2 * π * (-(ε / 2) * sn))) ^ 2 =
      π ^ 2 * ε ^ 2 * sn ^ 2 * (2 + κ * r ^ 2) ^ 2 / r ^ 2 := by
    field_simp; ring
  rw [key, hs, hr2]
  unfold F1
  rw [hcx]
  field_simp

/-- **The mode-1 gap equals that of the circle model.** -/
theorem gap_cosDmode1 {κ : ℝ} (hκ : 0 < κ) (i : Fin d) {ε : ℝ} (hε : |ε| ≤ 1) :
    gap (fun _ => 0) (cosWd κ) (densMeasure (cosDmode1 i ε)) =
      gap cosV (cosW κ) (densMeasure (fun x => 1 + ε * gCos x)) := by
  have hP := isProbabilityMeasure_densMeasure' (cosDmode1_nonneg i hε) (integral_cosDmode1 i ε)
  have hKa : 0 ≤ ∫ y, klFun (1 + ε * gCos y) ∂haar 1 :=
    integral_nonneg fun y => klFun_nonneg (one_add_mul_nonneg abs_gCos_le hε y)
  have hb : 0 ≤ κ / 2 * (ε ^ 2 / 4) := mul_nonneg (by linarith) (by positivity)
  rw [gap_cosWd hκ, sum_cosDQ_mode1 i hε, gap_rho_eq hκ continuous_gCos abs_gCos_le integral_gCos hε,
    cosDmode1_eq, klDiv_comp_mode (cosDPres_proj i) hε, firstMode_rho1,
    EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, max_eq_left hKa,
    max_eq_left (add_nonneg hKa hb), EReal.coe_add]

theorem admissible_cosDmode1 {κ : ℝ} (hκ : 0 < κ) (i : Fin d) {ε : ℝ} (hε : |ε| < 1)
    (hne : ε ≠ 0) : Admissible (fun _ => 0) (cosWd κ) (cosDmode1 i ε) := by
  refine ⟨cosDmode1_nonneg i hε.le, integral_cosDmode1 i ε, memH1_cosDmode1 i hε, ?_⟩
  rw [gap_cosDmode1 hκ i hε.le]
  exact (admissible_rho hκ continuous_gCos contDiff_gCos_lift abs_gCos_le integral_gCos
    integral_gCos_sq_pos hε hne).2.2.2

/-- **`r_* ≤ a(1 + κ/2)`** for the `d`-dimensional cosine model. -/
theorem rStar_le_cosWd_mode1 (hd : 1 ≤ d) {κ : ℝ} (hκ : 0 < κ) :
    rStar (d := d) (fun _ => 0) (cosWd κ) ≤ ENNReal.ofReal (aCos * (1 + κ / 2)) := by
  set i : Fin d := ⟨0, hd⟩
  have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε| < 1 ∧ ε ≠ 0 := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds small_eventually,
      self_mem_nhdsWithin] with ε hε hne
    exact ⟨by linarith, hne⟩
  refine ge_of_tendsto (tendsto_quotient_rho1 hκ) ?_
  filter_upwards [hev] with ε hε
  have h := iInf₂_le (f := fun ρ (_ : ρ ∈ {ρ | Admissible (fun _ => (0 : ℝ)) (cosWd κ) ρ}) =>
    dissipation (fun _ => 0) (cosWd κ) ρ /
      (2 * (gap (fun _ => 0) (cosWd κ) (densMeasure ρ)).toENNReal)) (cosDmode1 i ε)
    (admissible_cosDmode1 hκ i hε.1 hε.2)
  rw [dissipation_cosDmode1 κ i hε.1, gap_cosDmode1 hκ i hε.1.le,
    ← dissipation_rho1 κ hε.1] at h
  exact h

end SharpLSI
