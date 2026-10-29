import SharpSymmetricLSI.Infra.CZTorus2

/-!
# Riesz transforms on `𝕋^ι` by the method of rotations (R23 lane, CZ part 3)

`γ` is the standard Gaussian on `ℝ^ι`. For `k ≠ 0`, `E_γ[ω_j sgn(k·ω)] = κ k_j/|k|`,
`κ = E|g|` (`integral_coord_sgn`: an orthonormal basis whose `i₀`-th vector is `k/|k|`
diagonalizes the problem). Hence the Riesz transform `R_j` (symbol `-i k_j/|k|`) is
`κ^{-1} E_γ[ω_j H_ω]`, and Hölder + Tonelli transfer the uniform bound of `hilb_bound`
(`γ`-a.e. `ω` is generic): `‖R_j f‖_{2^{m+1}} ≤ C_m ‖f‖_{2^{m+1}}` (`riesz_bound`).
-/

open MeasureTheory Complex ProbabilityTheory
open scoped ENNReal ComplexConjugate RealInnerProductSpace
open UnitAddTorus

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The standard Gaussian on `ℝ^ι` (as a Euclidean space). -/
noncomputable abbrev gam (ι : Type) [Fintype ι] : Measure (EuclideanSpace ℝ ι) :=
  stdGaussian (EuclideanSpace ℝ ι)

/-- `κ = E|g|` for a standard real Gaussian `g`. -/
noncomputable def kappaG : ℝ := ∫ x, |x| ∂(gaussianReal 0 1)

/-- The lattice point `k` as a Euclidean vector. -/
noncomputable def kvec (k : ι → ℤ) : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => (k i : ℝ))

theorem kdot_eq_inner (k : ι → ℤ) (ω : EuclideanSpace ℝ ι) :
    kdot k (WithLp.ofLp ω) = ⟪kvec k, ω⟫ := by
  simp only [kdot, kvec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem kvec_ne_zero {k : ι → ℤ} (hk : k ≠ 0) : kvec k ≠ 0 := by
  intro h
  apply hk
  funext i
  have := congrArg (fun v : EuclideanSpace ℝ ι => WithLp.ofLp v i) h
  simpa [kvec] using this

theorem measurable_sgnR : Measurable sgnR := by
  unfold sgnR
  exact Measurable.ite measurableSet_Ioi measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

theorem sgnR_mul_pos {t c : ℝ} (hc : 0 < c) : sgnR (t * c) = sgnR t := by
  unfold sgnR
  rcases lt_trichotomy t 0 with h | rfl | h
  · simp [h, not_lt.mpr h.le, mul_neg_of_neg_of_pos h hc, not_lt.mpr (mul_neg_of_neg_of_pos h hc).le]
  · simp
  · simp [h, mul_pos h hc]

theorem mul_sgnR (t : ℝ) : t * sgnR t = |t| := by
  unfold sgnR
  rcases lt_trichotomy t 0 with h | rfl | h
  · simp [h, not_lt.mpr h.le, abs_of_neg h]
  · simp
  · simp [h, abs_of_pos h]

theorem abs_sgnR_le (t : ℝ) : |sgnR t| ≤ 1 := by
  unfold sgnR; split_ifs <;> simp

/-! ### Product-Gaussian integrals -/

/-- `∫ ∏ₗ fₗ(xₗ) dγ^{⊗ι}` for `f` equal to `1` off two coordinates. -/
theorem gauss_integral_pi_two {i i₀ : ι} (hi : i ≠ i₀) (f g : ℝ → ℝ) :
    ∫ x, f (x i) * g (x i₀) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      (∫ t, f t ∂gaussianReal 0 1) * ∫ t, g t ∂gaussianReal 0 1 := by
  set h : ι → ℝ → ℝ := fun l t => (if l = i then f t else 1) * (if l = i₀ then g t else 1)
  have hprod : ∀ x : ι → ℝ, ∏ l, h l (x l) = f (x i) * g (x i₀) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i, Finset.prod_ite_eq'
      Finset.univ i₀]
    simp
  simp_rw [← hprod]
  rw [integral_fintype_prod_eq_prod]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨hi.symm, Finset.mem_univ i₀⟩)]
  have h1 : ∀ l ∈ (Finset.univ.erase i).erase i₀, ∫ t, h l t ∂gaussianReal 0 1 = 1 := by
    intro l hl
    have hl1 : l ≠ i₀ := (Finset.mem_erase.mp hl).1
    have hl2 : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    simp [h, hl1, hl2]
  rw [Finset.prod_congr rfl h1]
  simp [h, hi, hi.symm]

theorem gauss_integral_pi_one (i₀ : ι) (g : ℝ → ℝ) :
    ∫ x, g (x i₀) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) = ∫ t, g t ∂gaussianReal 0 1 := by
  set h : ι → ℝ → ℝ := fun l t => if l = i₀ then g t else 1
  have hprod : ∀ x : ι → ℝ, ∏ l, h l (x l) = g (x i₀) := by
    intro x
    rw [Finset.prod_ite_eq' Finset.univ i₀]
    simp
  simp_rw [← hprod]
  rw [integral_fintype_prod_eq_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  have h1 : ∀ l ∈ Finset.univ.erase i₀, ∫ t, h l t ∂gaussianReal 0 1 = 1 := by
    intro l hl
    simp [h, (Finset.mem_erase.mp hl).1]
  rw [Finset.prod_congr rfl h1]
  simp [h]

/-- Integrals against `γ` through the coordinates. -/
theorem integral_gam_eq_pi {F : EuclideanSpace ℝ ι → ℝ} (hF : Measurable F) :
    ∫ ω, F ω ∂gam ι = ∫ x, F (WithLp.toLp 2 x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  rw [gam, ← map_pi_eq_stdGaussian, integral_map (by fun_prop) hF.aestronglyMeasurable]

theorem integral_abs_coord (j : ι) : ∫ ω, |WithLp.ofLp ω j| ∂gam ι = kappaG := by
  rw [integral_gam_eq_pi (by fun_prop)]
  exact gauss_integral_pi_one j (fun t => |t|)

theorem integrable_gam_coord (j : ι) : Integrable (fun ω : EuclideanSpace ℝ ι => WithLp.ofLp ω j) (gam ι) := by
  have := (EuclideanSpace.proj j : EuclideanSpace ℝ ι →L[ℝ] ℝ).integrable_comp
    (IsGaussian.integrable_id (μ := gam ι))
  simpa using this

theorem kappaG_pos : 0 < kappaG := by
  unfold kappaG
  have hi : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl |>.abs
  rw [integral_pos_iff_support_of_nonneg (fun x => abs_nonneg x) hi]
  have hs : Function.support (fun x : ℝ => |x|) = {0}ᶜ := by
    ext x; simp
  rw [hs]
  haveI := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), measure_singleton]
  simp

/-- **The Gaussian rotation identity** `E[ω_j sgn(k·ω)] = κ k_j/|k|`. -/
theorem integral_coord_sgn {k : ι → ℤ} (hk : k ≠ 0) (j : ι) :
    ∫ ω, WithLp.ofLp ω j * sgnR (kdot k (WithLp.ofLp ω)) ∂gam ι =
      kappaG * ((k j : ℝ) / ‖kvec k‖) := by
  have hv := kvec_ne_zero hk
  have hn : 0 < ‖kvec k‖ := norm_pos_iff.mpr hv
  obtain ⟨i₀, -⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  set u : EuclideanSpace ℝ ι := ‖kvec k‖⁻¹ • kvec k with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hon : Orthonormal ℝ (({i₀} : Set ι).restrict fun _ => u) := by
    rw [orthonormal_iff_ite]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Set.mem_singleton_iff] at ha hb
    subst ha hb
    simp only [if_true, real_inner_self_eq_norm_sq]
    show ‖u‖ ^ 2 = 1
    rw [hu1, one_pow]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hbi₀ : b i₀ = u := hb i₀ rfl
  have hm : Measurable (fun ω : EuclideanSpace ℝ ι => WithLp.ofLp ω j * sgnR (kdot k (WithLp.ofLp ω))) :=
    (by fun_prop : Measurable fun ω : EuclideanSpace ℝ ι => WithLp.ofLp ω j).mul
      (measurable_sgnR.comp (by unfold kdot; fun_prop))
  have hφ : Measurable (fun x : ι → ℝ => ∑ i, x i • b i) := (by fun_prop : Continuous _).measurable
  rw [gam, stdGaussian_eq_map_pi_orthonormalBasis b, integral_map
    (φ := fun x : ι → ℝ => ∑ i, x i • b i) hφ.aemeasurable hm.aestronglyMeasurable]
  have hk' : kvec k = ‖kvec k‖ • b i₀ := by
    rw [hbi₀, hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hinner : ∀ x : ι → ℝ, kdot k (WithLp.ofLp (∑ i, x i • b i)) = x i₀ * ‖kvec k‖ := by
    intro x
    rw [kdot_eq_inner, hk', inner_smul_left, inner_sum]
    simp only [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, conj_trivial]
    rw [← hk']
    ring
  have hcoord : ∀ x : ι → ℝ, WithLp.ofLp (∑ i, x i • b i) j = ∑ i, x i * WithLp.ofLp (b i) j := by
    intro x; simp
  simp_rw [hinner, hcoord, sgnR_mul_pos hn, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => ?_]
  · have hterm : ∀ i, ∫ x, x i * WithLp.ofLp (b i) j * sgnR (x i₀)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
        if i = i₀ then kappaG * WithLp.ofLp (b i₀) j else 0 := by
      intro i
      have e : ∀ x : ι → ℝ, x i * WithLp.ofLp (b i) j * sgnR (x i₀) =
          WithLp.ofLp (b i) j * (x i * sgnR (x i₀)) := fun x => by ring
      simp_rw [e]
      rw [integral_const_mul]
      split_ifs with h
      · subst h
        simp_rw [mul_sgnR]
        rw [gauss_integral_pi_one i (fun t => |t|), kappaG]
        ring
      · rw [gauss_integral_pi_two h (fun t => t) sgnR, integral_id_gaussianReal]
        simp
    simp_rw [hterm]
    rw [Finset.sum_ite_eq' Finset.univ i₀]
    simp only [Finset.mem_univ, if_true, hbi₀, hu]
    simp [kvec, div_eq_inv_mul]
  · -- integrability of each term
    have hint : Integrable (fun x : ι → ℝ => x i) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
      have := (memLp_id_gaussianReal 1 (μ := 0) (v := 1)).integrable le_rfl
      exact ((measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).integrable_comp
        this.aestronglyMeasurable).mpr this
    refine (hint.mul_const (WithLp.ofLp (b i) j)).bdd_mul (c := 1)
      (measurable_sgnR.comp (measurable_pi_apply i₀)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using abs_sgnR_le (x i₀)) |>.congr ?_
    filter_upwards with x
    simp only [Function.comp]
    ring

/-! ### Generic directions are `γ`-almost all -/

theorem ae_generic : ∀ᵐ ω ∂gam ι, Generic (WithLp.ofLp ω) := by
  have h : ∀ k : ι → ℤ, ∀ᵐ ω ∂gam ι, k ≠ 0 → kdot k (WithLp.ofLp ω) ≠ 0 := by
    intro k
    by_cases hk : k = 0
    · exact Filter.Eventually.of_forall fun _ h => absurd hk h
    set L : StrongDual ℝ (EuclideanSpace ℝ ι) := innerSL ℝ (kvec k) with hL
    have hLn : ‖L‖ = ‖kvec k‖ := innerSL_apply_norm _ _
    have hmap : (gam ι).map L = gaussianReal 0 (‖L‖ ^ 2).toNNReal := by
      rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
        variance_dual_stdGaussian]
    have hne : (‖L‖ ^ 2).toNNReal ≠ 0 := by
      rw [hLn]
      simpa using norm_pos_iff.mpr (kvec_ne_zero hk)
    haveI := nullSingletonClass_gaussianReal (μ := 0) hne
    have h0 : gam ι (L ⁻¹' {0}) = 0 := by
      rw [← Measure.map_apply L.measurable (measurableSet_singleton 0), hmap, measure_singleton]
    have : ∀ᵐ ω ∂gam ι, ω ∉ L ⁻¹' {0} := measure_eq_zero_iff_ae_notMem.mp h0
    filter_upwards [this] with ω hω _
    rw [kdot_eq_inner]
    simpa [hL] using hω
  filter_upwards [ae_all_iff.mpr h] with ω hω
  exact hω

/-! ### Riesz transforms -/

/-- The symbol `-i k_j/|k|` of the Riesz transform `R_j` (`0` at `k = 0`). -/
noncomputable def rieszSym (j : ι) (k : ι → ℤ) : ℂ := -I * (((k j : ℝ) / ‖kvec k‖ : ℝ) : ℂ)

theorem integral_coord_hilbSym (j : ι) (k : ι → ℤ) :
    ∫ ω, (WithLp.ofLp ω j : ℂ) * hilbSym (WithLp.ofLp ω) k ∂gam ι = kappaG * rieszSym j k := by
  have e : ∀ ω : EuclideanSpace ℝ ι, (WithLp.ofLp ω j : ℂ) * hilbSym (WithLp.ofLp ω) k =
      -I * ((WithLp.ofLp ω j * sgnR (kdot k (WithLp.ofLp ω)) : ℝ) : ℂ) := fun ω => by
    simp only [hilbSym]; push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, integral_complex_ofReal]
  by_cases hk : k = 0
  · subst hk
    simp [rieszSym, sgnR]
  · rw [integral_coord_sgn hk j, rieszSym]
    push_cast; ring

theorem integrable_coord_hilbSym (j : ι) (k : ι → ℤ) :
    Integrable (fun ω : EuclideanSpace ℝ ι => (WithLp.ofLp ω j : ℂ) * hilbSym (WithLp.ofLp ω) k)
      (gam ι) := by
  have hm : Measurable fun ω : EuclideanSpace ℝ ι => hilbSym (WithLp.ofLp ω) k := by
    unfold hilbSym
    exact measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_sgnR.comp (by unfold kdot; fun_prop)))
  refine ((integrable_gam_coord j).ofReal (𝕜 := ℂ)).mul_bdd (c := 1) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => norm_hilbSym_le _ k)

/-- **The method of rotations**: `κ R_j = E_γ[ω_j H_ω]` on trigonometric polynomials. -/
theorem riesz_eq_integral (j : ι) (c : TP ι) (x : UnitAddTorus ι) :
    (kappaG : ℂ) * synth (mult (rieszSym j) c) x =
      ∫ ω, (WithLp.ofLp ω j : ℂ) * synth (hilb (WithLp.ofLp ω) c) x ∂gam ι := by
  have e : ∀ ω : EuclideanSpace ℝ ι, (WithLp.ofLp ω j : ℂ) * synth (hilb (WithLp.ofLp ω) c) x =
      ∑ k ∈ c.coeff.support, ((WithLp.ofLp ω j : ℂ) * hilbSym (WithLp.ofLp ω) k) *
        (c.coeff k * mFourier k x) := fun ω => by
    rw [hilb, synth_apply_of_subset _ (mult_support _ c), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mult_coeff]; ring
  simp_rw [e]
  rw [integral_finsetSum _ fun k _ => (integrable_coord_hilbSym j k).mul_const _]
  simp_rw [integral_mul_const, integral_coord_hilbSym]
  rw [synth_apply_of_subset _ (mult_support _ c), Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [mult_coeff]; ring

/-! ### The `L^{2^{m+1}}` bound -/

/-- Hölder in the form `(∫ a b)^P ≤ (∫ a)^{P-1} ∫ a b^P`. -/
theorem lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ≥0∞} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) {P : ℝ} (hP : 1 < P) :
    (∫⁻ x, a x * b x ∂μ) ^ P ≤ (∫⁻ x, a x ∂μ) ^ (P - 1) * ∫⁻ x, a x * b x ^ P ∂μ := by
  set Q := Real.conjExponent P with hQdef
  have hpq : P.HolderConjugate Q := Real.HolderConjugate.conjExponent hP
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := hpq.symm.pos
  have hsum : 1 / Q + 1 / P = 1 := by
    rw [one_div, one_div, add_comm]; exact hpq.inv_add_inv_eq_one
  have hfg : ∀ x, a x ^ (1 / Q) * (a x ^ (1 / P) * b x) = a x * b x := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg (1 / Q) (1 / P) (one_div_nonneg.mpr hQ0.le)
      (one_div_nonneg.mpr hP0.le), hsum, ENNReal.rpow_one]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq.symm (f := fun x => a x ^ (1 / Q))
    (g := fun x => a x ^ (1 / P) * b x) (ha.pow_const _) ((ha.pow_const _).mul hb)
  simp only [Pi.mul_apply, hfg] at hH
  have e1 : ∀ x, (a x ^ (1 / Q)) ^ Q = a x := fun x => by
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hQ0.ne', ENNReal.rpow_one]
  have e2 : ∀ x, (a x ^ (1 / P) * b x) ^ P = a x * b x ^ P := fun x => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hP0.le, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hP0.ne', ENNReal.rpow_one]
  simp only [e1, e2] at hH
  have hQP : 1 / Q * P = P - 1 := by
    rw [hQdef, Real.conjExponent]
    have : P - 1 ≠ 0 := by linarith
    field_simp
  have h1P : 1 / P * P = 1 := by field_simp
  calc (∫⁻ x, a x * b x ∂μ) ^ P
      ≤ ((∫⁻ x, a x ∂μ) ^ (1 / Q) * (∫⁻ x, a x * b x ^ P ∂μ) ^ (1 / P)) ^ P :=
        ENNReal.rpow_le_rpow hH hP0.le
    _ = (∫⁻ x, a x ∂μ) ^ (P - 1) * ∫⁻ x, a x * b x ^ P ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hP0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hQP,
          h1P, ENNReal.rpow_one]

theorem lintegral_rpow_le_of_nr_le {P : ℝ} (hP : 0 < P) {F G : UnitAddTorus ι → ℂ}
    (hF : MemLp F (ENNReal.ofReal P) volume) (hG : MemLp G (ENNReal.ofReal P) volume) {C : ℝ}
    (hC0 : 0 ≤ C) (h : nr (ENNReal.ofReal P) G ≤ C * nr (ENNReal.ofReal P) F) :
    ∫⁻ x, ‖G x‖ₑ ^ P ≤ ENNReal.ofReal C ^ P * ∫⁻ x, ‖F x‖ₑ ^ P := by
  have hp0 : ENNReal.ofReal P ≠ 0 := by simpa using hP
  have hpt : ENNReal.ofReal P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle : eLpNorm G (ENNReal.ofReal P) volume ≤
      ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal P) volume := by
    rw [← ENNReal.ofReal_toReal hG.eLpNorm_ne_top, ← ENNReal.ofReal_toReal hF.eLpNorm_ne_top,
      ← ENNReal.ofReal_mul hC0]
    exact ENNReal.ofReal_le_ofReal h
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hG.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hF.aestronglyMeasurable, ENNReal.toReal_ofReal hP.le] at hle
  have := ENNReal.rpow_le_rpow hle hP.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hP.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div,
    inv_mul_cancel₀ hP.ne', ENNReal.rpow_one, ENNReal.rpow_one] at this
  exact this


/-- **`L^{2^{m+1}}` bound for the Riesz transforms.** -/
theorem riesz_bound (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ (j : ι) (c : TP ι),
    nr (2 ^ (m + 1)) (synth (mult (rieszSym j) c)) ≤ A * nr (2 ^ (m + 1)) (synth c) := by
  obtain ⟨C, hC0, hC⟩ := hilb_bound (ι := ι) m
  refine ⟨C, hC0, fun j c => ?_⟩
  set P : ℝ := 2 ^ (m + 1) with hPdef
  have hP1 : 1 < P := one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero m)
  have hP0 : 0 < P := by linarith
  have hp : (2 : ℝ≥0∞) ^ (m + 1) = ENNReal.ofReal P := by
    rw [hPdef, ENNReal.ofReal_pow (by norm_num)]; simp
  rw [hp] at hC ⊢
  set F := synth c
  set R := synth (mult (rieszSym j) c)
  set G : EuclideanSpace ℝ ι → UnitAddTorus ι → ℂ := fun ω => synth (hilb (WithLp.ofLp ω) c)
  set a : EuclideanSpace ℝ ι → ℝ≥0∞ := fun ω => ‖WithLp.ofLp ω j‖ₑ
  have hκ := kappaG_pos
  have hκ0 : ENNReal.ofReal kappaG ≠ 0 := by simpa using hκ
  have hκt : ENNReal.ofReal kappaG ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha : ∫⁻ ω, a ω ∂gam ι = ENNReal.ofReal kappaG := by
    rw [← integral_abs_coord j, ← ofReal_integral_norm_eq_lintegral_enorm (integrable_gam_coord j)]
    rfl
  have ham : Measurable a := by fun_prop
  -- measurability of `G` in both variables
  have hsym : ∀ k : ι → ℤ, Measurable fun ω : EuclideanSpace ℝ ι => hilbSym (WithLp.ofLp ω) k := by
    intro k
    have h1 : Measurable fun ω : EuclideanSpace ℝ ι => kdot k (WithLp.ofLp ω) := by
      unfold kdot; fun_prop
    exact measurable_const.mul (Complex.measurable_ofReal.comp (measurable_sgnR.comp h1))
  have hGexp : ∀ ω x, G ω x =
      ∑ k ∈ c.coeff.support, hilbSym (WithLp.ofLp ω) k * c.coeff k * mFourier k x := by
    intro ω x
    simp only [G, hilb]
    rw [synth_apply_of_subset _ (mult_support _ c)]
    exact Finset.sum_congr rfl fun k _ => by rw [mult_coeff]
  have hGm : Measurable fun z : EuclideanSpace ℝ ι × UnitAddTorus ι => G z.1 z.2 := by
    have e : (fun z : EuclideanSpace ℝ ι × UnitAddTorus ι => G z.1 z.2) = fun z =>
        ∑ k ∈ c.coeff.support, hilbSym (WithLp.ofLp z.1) k * c.coeff k * mFourier k z.2 :=
      funext fun z => hGexp z.1 z.2
    rw [e]
    exact Finset.measurable_sum _ fun k _ => (((hsym k).comp measurable_fst).mul measurable_const).mul
      ((map_continuous (mFourier k)).measurable.comp measurable_snd)
  have hGx : ∀ x, Measurable fun ω => ‖G ω x‖ₑ := fun x =>
    (hGm.comp (measurable_id.prodMk measurable_const)).enorm
  have hGω : ∀ ω, Measurable fun x => ‖G ω x‖ₑ := fun ω =>
    (hGm.comp (measurable_const.prodMk measurable_id)).enorm
  -- pointwise bound
  have hpt : ∀ x, ENNReal.ofReal kappaG * ‖R x‖ₑ ≤ ∫⁻ ω, a ω * ‖G ω x‖ₑ ∂gam ι := by
    intro x
    have := riesz_eq_integral j c x
    calc ENNReal.ofReal kappaG * ‖R x‖ₑ = ‖(kappaG : ℂ) * R x‖ₑ := by
          rw [enorm_mul]
          congr 1
          rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg hκ.le]
      _ = ‖∫ ω, (WithLp.ofLp ω j : ℂ) * G ω x ∂gam ι‖ₑ := by rw [this]
      _ ≤ ∫⁻ ω, ‖(WithLp.ofLp ω j : ℂ) * G ω x‖ₑ ∂gam ι := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ ω, a ω * ‖G ω x‖ₑ ∂gam ι := by
          congr 1; funext ω
          rw [enorm_mul]
          congr 1
          show ‖((WithLp.ofLp ω j : ℝ) : ℂ)‖ₑ = ‖WithLp.ofLp ω j‖ₑ
          rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_real]
  -- the generic bound
  have hgen : ∀ᵐ ω ∂gam ι, ∫⁻ x, ‖G ω x‖ₑ ^ P ≤ ENNReal.ofReal C ^ P * ∫⁻ x, ‖F x‖ₑ ^ P := by
    filter_upwards [ae_generic] with ω hω
    exact lintegral_rpow_le_of_nr_le hP0 (memLp_synth _ _) (memLp_synth _ _) hC0 (hC _ hω c)
  have hpow : ENNReal.ofReal kappaG ^ (P - 1) * ENNReal.ofReal kappaG =
      ENNReal.ofReal kappaG ^ P := by
    have := ENNReal.rpow_add (P - 1) 1 hκ0 hκt
    rw [ENNReal.rpow_one, sub_add_cancel] at this
    exact this.symm
  have hκPt : ENNReal.ofReal kappaG ^ P ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hP0.le hκt
  have hκP1t : ENNReal.ofReal kappaG ^ (P - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hκt
  have hmain : ENNReal.ofReal kappaG ^ P * ∫⁻ x, ‖R x‖ₑ ^ P ≤
      ENNReal.ofReal kappaG ^ P * (ENNReal.ofReal C ^ P * ∫⁻ x, ‖F x‖ₑ ^ P) := by
    calc ENNReal.ofReal kappaG ^ P * ∫⁻ x, ‖R x‖ₑ ^ P
        = ∫⁻ x : UnitAddTorus ι, (ENNReal.ofReal kappaG * ‖R x‖ₑ) ^ P := by
          rw [← lintegral_const_mul' _ _ hκPt]
          congr 1; funext x
          rw [ENNReal.mul_rpow_of_nonneg _ _ hP0.le]
      _ ≤ ∫⁻ x : UnitAddTorus ι, (∫⁻ ω, a ω * ‖G ω x‖ₑ ∂gam ι) ^ P :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hP0.le
      _ ≤ ∫⁻ x : UnitAddTorus ι, ENNReal.ofReal kappaG ^ (P - 1) *
            ∫⁻ ω, a ω * ‖G ω x‖ₑ ^ P ∂gam ι := by
          refine lintegral_mono fun x => ?_
          rw [← ha]
          exact lintegral_mul_rpow_le ham.aemeasurable (hGx x).aemeasurable hP1
      _ = ENNReal.ofReal kappaG ^ (P - 1) * ∫⁻ ω, a ω * (∫⁻ x, ‖G ω x‖ₑ ^ P) ∂gam ι := by
          rw [lintegral_const_mul' _ _ hκP1t, lintegral_lintegral_swap]
          · congr 1
            refine lintegral_congr fun ω => ?_
            rw [lintegral_const_mul _ ((hGω ω).pow_const P)]
          · exact ((ham.comp measurable_snd).mul
              ((hGm.comp measurable_swap).enorm.pow_const P)).aemeasurable
      _ ≤ ENNReal.ofReal kappaG ^ (P - 1) *
            ∫⁻ ω, a ω * (ENNReal.ofReal C ^ P * ∫⁻ x, ‖F x‖ₑ ^ P) ∂gam ι := by
          refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
          filter_upwards [hgen] with ω hω
          exact mul_le_mul' le_rfl hω
      _ = ENNReal.ofReal kappaG ^ P * (ENNReal.ofReal C ^ P * ∫⁻ x, ‖F x‖ₑ ^ P) := by
          rw [lintegral_mul_const _ ham, ha, ← mul_assoc, hpow]
  have hκP0 : ENNReal.ofReal kappaG ^ P ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hκ, hP0, not_le.mpr hκ]
  have hRF := (ENNReal.mul_le_mul_iff_right hκP0 hκPt).mp hmain
  -- back to norms
  have hp0 : ENNReal.ofReal P ≠ 0 := by simpa using hP0
  have hpt' : ENNReal.ofReal P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hE : eLpNorm R (ENNReal.ofReal P) volume ≤
      ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal P) volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt'
        (memLp_synth (mult (rieszSym j) c) (ENNReal.ofReal P)).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt'
        (memLp_synth c (ENNReal.ofReal P)).aestronglyMeasurable,
      ENNReal.toReal_ofReal hP0.le]
    calc (∫⁻ x, ‖R x‖ₑ ^ P) ^ (1 / P)
        ≤ (ENNReal.ofReal C ^ P * ∫⁻ x, ‖F x‖ₑ ^ P) ^ (1 / P) :=
          ENNReal.rpow_le_rpow hRF (by positivity)
      _ = ENNReal.ofReal C * (∫⁻ x, ‖F x‖ₑ ^ P) ^ (1 / P) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, one_div,
            mul_inv_cancel₀ hP0.ne', ENNReal.rpow_one]
  unfold nr
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (memLp_synth c _).eLpNorm_ne_top) hE
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0] at this

end SharpLSI
