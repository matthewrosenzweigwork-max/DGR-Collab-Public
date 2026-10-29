import SharpSymmetricLSI.Paper.CosineD6

/-!
# The `d`-dimensional cosine model (7): the mode-2 upper bound `r_* ≤ 2a`, and `r_* ≤ a min{1+κ/2, 2}`

Along `ρ_ε(x) = 1 + ε cos 2π(xᵢ + xⱼ)` (`i ≠ j`) every one-coordinate first mode vanishes, so the
interaction drops out: `G(ρ_ε) = H(ρ_ε)` (`gap_cosDmode2`) and the dissipation is the free one,
`D(ρ_ε) = 2 ε² ∫ F1 0 ε` (`dissipation_cosDmode2`). Hence `D/(2G) → 2a` and `r_* ≤ 2a`
(`rStar_le_cosWd_mode2`, `d ≥ 2`).
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal Real

namespace SharpLSI

variable {d : ℕ}

/-- `ρ_ε(x) = 1 + ε cos 2π(xᵢ + xⱼ)`. -/
noncomputable def cosDmode2 (i j : Fin d) (ε : ℝ) (x : Torus d) : ℝ := 1 + ε * gCos (cosDsum i j x)

theorem gCos_cosDsum_add_half {i j l : Fin d} (hij : i ≠ j) (hl : l = i ∨ l = j) (x : Torus d) :
    gCos (cosDsum i j (x + cosDhalf l)) = -gCos (cosDsum i j x) := by
  have e : (x + cosDhalf l) i + (x + cosDhalf l) j = (x i + x j) + ((2⁻¹ : ℝ) : UnitAddCircle) := by
    rcases hl with rfl | rfl
    · rw [cosDhalf_apply_self, cosDhalf_apply_ne hij]; abel
    · rw [cosDhalf_apply_self, cosDhalf_apply_ne (Ne.symm hij)]; abel
  simp only [gCos, expT, cosDsum, e, fourier_add_half, Complex.neg_re]

theorem continuous_gCos_cosDsum (i j : Fin d) : Continuous fun x => gCos (cosDsum i j x) :=
  continuous_gCos.comp (continuous_cosDsum i j)

theorem integral_cosDc (k : Fin d) : ∫ x, cosDc k x ∂haar d = 0 := by
  rw [show (fun x => cosDc k x) = fun x => gCos (cosDproj k x) from rfl,
    integral_cosDproj_haar k continuous_gCos, integral_gCos]

theorem integral_cosDs (k : Fin d) : ∫ x, cosDs k x ∂haar d = 0 := by
  rw [show (fun x => cosDs k x) = fun x => sCos (cosDproj k x) from rfl,
    integral_cosDproj_haar k continuous_sCos, integral_sCos]

/-- The half-shift index `l ∈ {i, j}`, `l ≠ k`. -/
theorem exists_half_index {i j : Fin d} (hij : i ≠ j) (k : Fin d) :
    ∃ l, (l = i ∨ l = j) ∧ l ≠ k := by
  by_cases hk : k = i
  · exact ⟨j, Or.inr rfl, fun h => hij (hk ▸ h.symm ▸ rfl)⟩
  · exact ⟨i, Or.inl rfl, Ne.symm hk⟩

theorem cosDA_mode2 {i j : Fin d} (hij : i ≠ j) (ε : ℝ) (k : Fin d) :
    cosDA (cosDmode2 i j ε) k = 0 := by
  obtain ⟨l, hl, hlk⟩ := exists_half_index hij k
  have i1 := integrable_torusD (μ := haar d) (continuous_cosDc k)
  have i2 := integrable_torusD (μ := haar d) ((continuous_cosDc k).mul (continuous_gCos_cosDsum i j))
  unfold cosDA cosDmode2
  have e : ∀ y, cosDc k y * (1 + ε * gCos (cosDsum i j y)) =
      cosDc k y + ε * (cosDc k y * gCos (cosDsum i j y)) := fun y => by ring
  simp_rw [e]
  rw [integral_add (f := fun y => cosDc k y) (g := fun y => ε * (cosDc k y * gCos (cosDsum i j y)))
    i1 (i2.const_mul ε), integral_const_mul, integral_cosDc,
    integral_eq_zero_of_half l fun x => by
      rw [cosDc_add_half_ne hlk, gCos_cosDsum_add_half hij hl]; ring]
  ring

theorem cosDB_mode2 {i j : Fin d} (hij : i ≠ j) (ε : ℝ) (k : Fin d) :
    cosDB (cosDmode2 i j ε) k = 0 := by
  obtain ⟨l, hl, hlk⟩ := exists_half_index hij k
  have i1 := integrable_torusD (μ := haar d) (continuous_cosDs k)
  have i2 := integrable_torusD (μ := haar d) ((continuous_cosDs k).mul (continuous_gCos_cosDsum i j))
  unfold cosDB cosDmode2
  have e : ∀ y, cosDs k y * (1 + ε * gCos (cosDsum i j y)) =
      cosDs k y + ε * (cosDs k y * gCos (cosDsum i j y)) := fun y => by ring
  simp_rw [e]
  rw [integral_add (f := fun y => cosDs k y) (g := fun y => ε * (cosDs k y * gCos (cosDsum i j y)))
    i1 (i2.const_mul ε), integral_const_mul, integral_cosDs,
    integral_eq_zero_of_half l fun x => by
      rw [cosDs_add_half_ne hlk, gCos_cosDsum_add_half hij hl]; ring]
  ring

theorem cosDmode2_nonneg (i j : Fin d) {ε : ℝ} (hε : |ε| ≤ 1) (x : Torus d) :
    0 ≤ cosDmode2 i j ε x := one_add_mul_nonneg abs_gCos_le hε _

theorem integral_cosDmode2 {i j : Fin d} (hij : i ≠ j) (ε : ℝ) :
    ∫ x, cosDmode2 i j ε x ∂haar d = 1 :=
  integral_comp_mode (cosDPres_sum hij) ε

theorem sqrt_cosDmode2_lift (i j : Fin d) (ε : ℝ) :
    (fun x => Real.sqrt (cosDmode2 i j ε x)) ∘ liftT =
      fun z : Fin d → ℝ => cosDg ε (z i + z j) := by
  funext z
  simp only [Function.comp_apply, cosDmode2, cosDg]
  rw [gCos_coe _ (z i + z j)]
  simp [cosDsum, liftT]

theorem contDiff_sqrt_cosDmode2 (i j : Fin d) {ε : ℝ} (hε : |ε| < 1) :
    ContDiff ℝ ⊤ ((fun x => Real.sqrt (cosDmode2 i j ε x)) ∘ liftT) := by
  rw [sqrt_cosDmode2_lift]
  exact (contDiff_cosDg hε).comp ((contDiff_apply ℝ ℝ i).add (contDiff_apply ℝ ℝ j))

theorem memH1_cosDmode2 (i j : Fin d) {ε : ℝ} (hε : |ε| < 1) :
    MemH1 (haar d) (fun x => Real.sqrt (cosDmode2 i j ε x)) :=
  memH1_of_contDiff ((contDiff_sqrt_cosDmode2 i j hε).of_le le_top)

theorem fderiv_sqrt_cosDmode2 (i j : Fin d) {ε : ℝ} (hε : |ε| < 1) (z : Fin d → ℝ) (k : Fin d) :
    fderiv ℝ ((fun x => Real.sqrt (cosDmode2 i j ε x)) ∘ liftT) z (Pi.single k 1) =
      ε * (-(2 * π) * Real.sin (2 * π * (z i + z j))) / (2 * cosDg ε (z i + z j)) *
        ((Pi.single k (1 : ℝ) : Fin d → ℝ) i + (Pi.single k (1 : ℝ) : Fin d → ℝ) j) := by
  rw [sqrt_cosDmode2_lift]
  set L := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i +
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j
  have h := (hasDerivAt_cosDg hε (L z)).comp_hasFDerivAt z L.hasFDerivAt
  rw [show (fun z : Fin d → ℝ => cosDg ε (z i + z j)) = cosDg ε ∘ L from rfl, h.fderiv]
  simp only [smul_apply, smul_eq_mul, L, add_apply,
    ContinuousLinearMap.proj_apply]

/-- **The mode-2 dissipation is the free one, `2ε² ∫ F1 0 ε`.** -/
theorem dissipation_cosDmode2 (κ : ℝ) {i j : Fin d} (hij : i ≠ j) {ε : ℝ} (hε : |ε| < 1) :
    dissipation (fun _ => 0) (cosWd κ) (cosDmode2 i j ε) =
      ENNReal.ofReal (2 * ε ^ 2 * ∫ y, F1 0 ε y ∂haar 1) := by
  rw [dissipation_cosWd_eq κ (integral_cosDmode2 hij ε) (memH1_cosDmode2 i j hε)]
  have hu1 : ContDiff ℝ 1 ((fun x => Real.sqrt (cosDmode2 i j ε x)) ∘ liftT) :=
    (contDiff_sqrt_cosDmode2 i j hε).of_le le_top
  have hF : Continuous (F1 0 ε) := continuous_F1 0 hε
  rw [← integral_cosDsum hij hF, ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal (f := fun x => 2 * ε ^ 2 * F1 0 ε (cosDsum i j x))
    (integrable_torusD (continuous_const.mul (hF.comp (continuous_cosDsum i j))))
    (Eventually.of_forall fun y => mul_nonneg (by positivity) (F1_nonneg 0 hε _))]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq_of_contDiff hu1] with x hx
  rw [hx]
  simp only [fderiv_sqrt_cosDmode2 i j hε, cosDA_mode2 hij, cosDB_mode2 hij, neg_zero, zero_mul,
    mul_zero, add_zero]
  congr 1
  set t := secT x i + secT x j with ht
  set g' := ε * (-(2 * π) * Real.sin (2 * π * t)) / (2 * cosDg ε t) with hg'
  rw [Finset.sum_eq_add i j hij (fun c _ hc => by
      simp [Ne.symm hc.1, Ne.symm hc.2])
    (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)]
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij),
    add_zero, zero_add, mul_one]
  -- the circle computation
  set c := Real.cos (2 * π * t) with hc
  set sn := Real.sin (2 * π * t) with hsn
  set r := cosDg ε t with hr
  have hcx : gCos (cosDsum i j x) = c := by
    rw [hc, ht]
    conv_lhs => rw [← liftT_secT x]
    exact gCos_coe _ _ (by simp [cosDsum, liftT])
  have hr2 : r ^ 2 = 1 + ε * c := cosDg_sq hε _
  have hr0 : 0 < r := cosDg_pos hε _
  have hs : sn ^ 2 = 1 - c ^ 2 := by linarith [Real.sin_sq_add_cos_sq (2 * π * t)]
  have key : (2 * g') ^ 2 + (2 * g') ^ 2 = 8 * π ^ 2 * ε ^ 2 * sn ^ 2 / r ^ 2 := by
    rw [hg']; field_simp; ring
  rw [key, hs, hr2]
  unfold F1
  rw [hcx]
  field_simp
  ring

/-- **The mode-2 gap is the entropy.** -/
theorem gap_cosDmode2 {κ : ℝ} (hκ : 0 < κ) {i j : Fin d} (hij : i ≠ j) {ε : ℝ} (hε : |ε| ≤ 1) :
    gap (fun _ => 0) (cosWd κ) (densMeasure (cosDmode2 i j ε)) =
      ((ENNReal.ofReal (∫ y, klFun (1 + ε * gCos y) ∂haar 1) : ℝ≥0∞) : EReal) := by
  have hP := isProbabilityMeasure_densMeasure' (cosDmode2_nonneg i j hε) (integral_cosDmode2 hij ε)
  have hQ : ∑ k, cosDQ k (densMeasure (cosDmode2 i j ε)) = 0 := by
    simp_rw [cosDQ_densMeasure (cosDmode2_nonneg i j hε) (integral_cosDmode2 hij ε),
      cosDA_mode2 hij, cosDB_mode2 hij]
    simp
  rw [gap_cosWd hκ, hQ, show cosDmode2 i j ε = fun x => 1 + ε * gCos (cosDsum i j x) from rfl,
    klDiv_comp_mode (cosDPres_sum hij) hε]
  simp

theorem admissible_cosDmode2 {κ : ℝ} (hκ : 0 < κ) {i j : Fin d} (hij : i ≠ j) {ε : ℝ}
    (hε : |ε| < 1) (hne : ε ≠ 0) : Admissible (fun _ => 0) (cosWd κ) (cosDmode2 i j ε) := by
  refine ⟨cosDmode2_nonneg i j hε.le, integral_cosDmode2 hij ε, memH1_cosDmode2 i j hε, ?_⟩
  rw [gap_cosDmode2 hκ hij hε.le]
  exact EReal.coe_ennreal_pos.mpr (ENNReal.ofReal_pos.mpr (kl_mode_pos continuous_gCos abs_gCos_le
    integral_gCos integral_gCos_sq_pos hε hne))

/-- The mode-2 quotient `D/(2G) → 2a`. -/
theorem tendsto_quotient_cosDmode2 {κ : ℝ} (hκ : 0 < κ) {i j : Fin d} (hij : i ≠ j) :
    Tendsto (fun ε : ℝ => dissipation (fun _ => 0) (cosWd κ) (cosDmode2 i j ε) /
        (2 * (gap (fun _ => 0) (cosWd κ) (densMeasure (cosDmode2 i j ε))).toENNReal))
      (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (2 * aCos))) := by
  have hΦ := ((continuousAt_integral_F1 0).tendsto).mono_left
    (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
  rw [integral_F1_zero] at hΦ
  have hk := tendsto_kl_mode continuous_gCos abs_gCos_le integral_gCos
  rw [integral_gCos_sq] at hk
  have hq := (hΦ.const_mul 2).div (hk.const_mul 2) (by norm_num)
  have hval : 2 * (π ^ 2 * (2 + 0) ^ 2 / 2) / (2 * (1 / 2 / 2)) = 2 * aCos := by
    unfold aCos; ring
  rw [hval] at hq
  refine (ENNReal.tendsto_ofReal hq).congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds small_eventually, self_mem_nhdsWithin]
    with ε hε hne
  have hne' : ε ≠ 0 := hne
  have hε1 : |ε| < 1 := by linarith
  have hkp := kl_mode_pos continuous_gCos abs_gCos_le integral_gCos integral_gCos_sq_pos hε1 hne'
  rw [dissipation_cosDmode2 κ hij hε1, gap_cosDmode2 hκ hij hε1.le, EReal.toENNReal_coe,
    quotient_eq (mul_nonneg (by positivity) (integral_nonneg fun y => F1_nonneg 0 hε1 y)) hkp]
  congr 1
  simp only [Pi.div_apply]
  field_simp

/-- **`r_* ≤ 2a`** for the `d`-dimensional cosine model, `d ≥ 2`. -/
theorem rStar_le_cosWd_mode2 (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) :
    rStar (d := d) (fun _ => 0) (cosWd κ) ≤ ENNReal.ofReal (2 * aCos) := by
  set i : Fin d := ⟨0, by omega⟩
  set j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε| < 1 ∧ ε ≠ 0 := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds small_eventually,
      self_mem_nhdsWithin] with ε hε hne
    exact ⟨by linarith, hne⟩
  refine ge_of_tendsto (tendsto_quotient_cosDmode2 hκ hij) ?_
  filter_upwards [hev] with ε hε
  exact iInf₂_le (f := fun ρ (_ : ρ ∈ {ρ | Admissible (fun _ => (0 : ℝ)) (cosWd κ) ρ}) =>
    dissipation (fun _ => 0) (cosWd κ) ρ /
      (2 * (gap (fun _ => 0) (cosWd κ) (densMeasure ρ)).toENNReal)) (cosDmode2 i j ε)
    (admissible_cosDmode2 hκ hij hε.1 hε.2)

/-- **`r_* ≤ a min{1 + κ/2, 2}`** for the `d`-dimensional cosine model, `d ≥ 2`. -/
theorem rStar_le_cosWd (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) :
    rStar (d := d) (fun _ => 0) (cosWd κ) ≤ ENNReal.ofReal (aCos * min (1 + κ / 2) 2) := by
  have ha : 0 ≤ aCos := by unfold aCos; positivity
  rw [mul_min_of_nonneg _ _ ha, ENNReal.ofReal_min]
  exact le_min (rStar_le_cosWd_mode1 (by omega) hκ)
    (by rw [mul_comm]; exact rStar_le_cosWd_mode2 hd hκ)

end SharpLSI
