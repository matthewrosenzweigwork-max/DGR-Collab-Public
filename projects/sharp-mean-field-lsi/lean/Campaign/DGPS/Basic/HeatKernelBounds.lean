import DGPS.Analysis.PeriodicHeatKernel

/-!
# Periodized heat gradient bounds (LIP006)
-/

open MeasureTheory Set ProbabilityTheory
open scoped Real NNReal ENNReal RealInnerProductSpace ContDiff

namespace DGPS.Lipschitz

variable {d : ℕ}

theorem gauss1_eq_pdf {t : ℝ} (ht : 0 < t) :
    DGPS.gauss1 t = gaussianPDFReal 0 (2 * t).toNNReal := by
  funext s
  unfold DGPS.gauss1 gaussianPDFReal
  have h2 : (((2 * t).toNNReal : ℝ≥0) : ℝ) = 2 * t := Real.coe_toNNReal _ (by positivity)
  rw [h2, sub_zero]
  have h3 : (4 * π * t) ^ (-1 / 2 : ℝ) = (√(2 * π * (2 * t)))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by positivity),
      ← Real.sqrt_eq_rpow, show 4 * π * t = 2 * π * (2 * t) by ring]
  rw [h3]
  congr 2
  ring

theorem integral_gauss1 {t : ℝ} (ht : 0 < t) : ∫ s, DGPS.gauss1 t s = 1 := by
  rw [gauss1_eq_pdf ht]
  exact integral_gaussianPDFReal_eq_one 0 (by simp [ht])

theorem integrable_gauss1 {t : ℝ} (ht : 0 < t) : Integrable (DGPS.gauss1 t) := by
  rw [gauss1_eq_pdf ht]; exact integrable_gaussianPDFReal _ _

theorem integral_sq_gauss1 {t : ℝ} (ht : 0 < t) : ∫ s, s ^ 2 * DGPS.gauss1 t s = 2 * t := by
  have hv : (2 * t).toNNReal ≠ 0 := by simp [ht]
  have h := variance_fun_id_gaussianReal (μ := 0) (v := (2 * t).toNNReal)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simp only [integral_id_gaussianReal, sub_zero] at h
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  rw [gauss1_eq_pdf ht]
  simp only [smul_eq_mul, Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 * t)] at h
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)) h
  simp only [pow_two]; ring

theorem integral_Ioi_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ u in Ioi (0 : ℝ), u * Real.exp (-b * u ^ 2) = 1 / (2 * b) := by
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun u : ℝ => -(1 / (2 * b)) * Real.exp (-b * u ^ 2))
      (x * Real.exp (-b * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => -b * u ^ 2) (-b * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (-b))
    have h2 := (h1.exp).const_mul (-(1 / (2 * b)))
    convert h2 using 1
    field_simp
  have hint : IntegrableOn (fun u : ℝ => u * Real.exp (-b * u ^ 2)) (Ioi 0) := by
    have := (integrableOn_rpow_mul_exp_neg_mul_sq hb (s := 1) (by norm_num))
    simpa using this
  have ht : Filter.Tendsto (fun u : ℝ => -(1 / (2 * b)) * Real.exp (-b * u ^ 2)) Filter.atTop
      (nhds 0) := by
    have h0 : Filter.Tendsto (fun u : ℝ => b * u ^ 2) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hb (Filter.tendsto_pow_atTop (by norm_num))
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h0).const_mul (-(1 / (2 * b)))
    simpa [Function.comp_def, neg_mul] using this
  have := integral_Ioi_of_hasDerivAt_of_tendsto
    (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).continuousWithinAt hd hint ht
  rw [this]; simp

theorem integral_abs_mul_gauss1 {t : ℝ} (ht : 0 < t) :
    ∫ s, |s| * DGPS.gauss1 t s = 2 * t * (π * t) ^ (-(1 : ℝ) / 2) := by
  have hb : (0:ℝ) < 1 / (4 * t) := by positivity
  have e1 : ∀ s : ℝ, |s| * DGPS.gauss1 t s =
      (4 * π * t) ^ (-(1 : ℝ) / 2) * (fun u : ℝ => u * Real.exp (-(1 / (4 * t)) * u ^ 2)) |s| := by
    intro s
    unfold DGPS.gauss1
    have : -s ^ 2 / (4 * t) = -(1 / (4 * t)) * |s| ^ 2 := by rw [sq_abs]; ring
    rw [this]; ring
  simp_rw [e1]
  rw [integral_const_mul, integral_comp_abs (f := fun u : ℝ => u * Real.exp (-(1 / (4 * t)) * u ^ 2)),
    integral_Ioi_mul_exp hb]
  have h4 : (4 * π * t) ^ (-(1 : ℝ) / 2) = (1 / 2) * (π * t) ^ (-(1 : ℝ) / 2) := by
    rw [show 4 * π * t = 4 * (π * t) by ring, Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    rw [show (-(1 : ℝ) / 2) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num),
      show (4 : ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h4]; field_simp; norm_num

noncomputable def gE (t : ℝ) (v : Tangent d) : ℝ :=
  (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖v‖ ^ 2 / (4 * t))

theorem gE_eq_prod {t : ℝ} (ht : 0 < t) (b : OrthonormalBasis (Fin d) ℝ (Tangent d)) (v : Tangent d) :
    gE t v = ∏ j, DGPS.gauss1 t (⟪b j, v⟫) := by
  rw [← DGPS.gaussian_eq_prod ht]
  unfold gE
  congr 3
  rw [← b.sum_sq_norm_inner_right v]
  simp

theorem integral_basis_coords (b : OrthonormalBasis (Fin d) ℝ (Tangent d))
    (Φ : (Fin d → ℝ) → ℝ) : ∫ v : Tangent d, Φ (fun j => ⟪b j, v⟫) = ∫ y, Φ y := by
  let e : Tangent d ≃ᵐ (Fin d → ℝ) :=
    b.measurableEquiv.trans (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
  have h1 : MeasurePreserving e := by
    have := (PiLp.volume_preserving_ofLp (Fin d)).comp b.measurePreserving_repr
    exact this
  have := h1.integral_comp' (f := e) Φ
  rw [← this]
  congr 1
  funext v
  congr 1
  funext j
  simp [e, OrthonormalBasis.measurableEquiv, b.repr_apply_apply]

theorem integrable_basis_coords (b : OrthonormalBasis (Fin d) ℝ (Tangent d))
    (Φ : (Fin d → ℝ) → ℝ) : Integrable (fun v : Tangent d => Φ (fun j => ⟪b j, v⟫)) ↔ Integrable Φ := by
  let e : Tangent d ≃ᵐ (Fin d → ℝ) :=
    b.measurableEquiv.trans (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
  have h1 : MeasurePreserving e := by
    have := (PiLp.volume_preserving_ofLp (Fin d)).comp b.measurePreserving_repr
    exact this
  have := h1.integrable_comp_emb (f := e) e.measurableEmbedding (g := Φ)
  rw [← this]
  have h2 : (fun v : Tangent d => Φ (fun j => ⟪b j, v⟫)) = Φ ∘ e := by
    funext v
    simp only [Function.comp_apply]
    congr 1
    funext j
    simp [e, OrthonormalBasis.measurableEquiv, b.repr_apply_apply]
  rw [h2]

theorem prod_update_eq {t : ℝ} (i0 : Fin d) (h : ℝ → ℝ) (y : Fin d → ℝ) :
    h (y i0) * ∏ j, DGPS.gauss1 t (y j) =
      ∏ j, (fun (k : Fin d) => if k = i0 then (fun s => h s * DGPS.gauss1 t s)
        else DGPS.gauss1 t) j (y j) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun j => DGPS.gauss1 t (y j)) (Finset.mem_univ i0),
    ← Finset.mul_prod_erase Finset.univ (fun j => (fun (k : Fin d) => if k = i0
      then (fun s => h s * DGPS.gauss1 t s) else DGPS.gauss1 t) j (y j)) (Finset.mem_univ i0)]
  simp only [ite_true, mul_assoc]
  have : ∏ x ∈ Finset.univ.erase i0, (fun (k : Fin d) => if k = i0 then (fun s => h s * DGPS.gauss1 t s)
        else DGPS.gauss1 t) x (y x) = ∏ x ∈ Finset.univ.erase i0, DGPS.gauss1 t (y x) :=
    Finset.prod_congr rfl (fun j hj => by simp [Finset.ne_of_mem_erase hj])
  rw [this]

theorem integral_prod_update {t : ℝ} (ht : 0 < t) (i0 : Fin d) (h : ℝ → ℝ) :
    ∫ y : Fin d → ℝ, h (y i0) * ∏ j, DGPS.gauss1 t (y j) = ∫ s, h s * DGPS.gauss1 t s := by
  classical
  simp_rw [prod_update_eq i0 h]
  have := integral_fintype_prod_eq_prod (μ := fun _ : Fin d => (volume : Measure ℝ))
    (fun (j : Fin d) => if j = i0 then (fun s => h s * DGPS.gauss1 t s) else DGPS.gauss1 t)
  rw [show (volume : Measure (Fin d → ℝ)) = Measure.pi fun _ => volume from rfl, this]
  rw [Finset.prod_eq_single i0]
  · simp
  · intro j _ hj
    simp only [hj, ite_false]
    exact integral_gauss1 ht
  · simp

theorem integrable_prod_update {t : ℝ} (ht : 0 < t) (i0 : Fin d) {h : ℝ → ℝ}
    (hh : Integrable (fun s => h s * DGPS.gauss1 t s)) :
    Integrable (fun y : Fin d → ℝ => h (y i0) * ∏ j, DGPS.gauss1 t (y j)) := by
  classical
  simp_rw [prod_update_eq i0 h]
  exact Integrable.fintype_prod_dep (μ := fun _ : Fin d => (volume : Measure ℝ))
    (f := fun (j : Fin d) => if j = i0 then (fun s => h s * DGPS.gauss1 t s) else DGPS.gauss1 t)
    (fun j => by
      by_cases hj : j = i0
      · simpa [hj] using hh
      · simpa [hj] using integrable_gauss1 ht)

theorem gauss1_eq_exp (t s : ℝ) :
    DGPS.gauss1 t s = (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-(1 / (4 * t)) * s ^ 2) := by
  unfold DGPS.gauss1
  congr 2
  ring

theorem integrable_abs_mul_gauss1 {t : ℝ} (ht : 0 < t) :
    Integrable (fun s => |s| * DGPS.gauss1 t s) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := 1 / (4 * t)) (by positivity)).norm.const_mul
    ((4 * π * t) ^ (-(1 : ℝ) / 2))
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [gauss1_eq_exp, norm_mul, Real.norm_eq_abs, Real.exp_pos, abs_of_pos]
  ring

theorem integrable_sq_mul_gauss1 {t : ℝ} (ht : 0 < t) :
    Integrable (fun s => s ^ 2 * DGPS.gauss1 t s) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / (4 * t)) (by positivity)
    (s := 2) (by norm_num)).const_mul ((4 * π * t) ^ (-(1 : ℝ) / 2))
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [gauss1_eq_exp, Real.rpow_two]
  ring

theorem integral_inner_gE {t : ℝ} (ht : 0 < t) (b : OrthonormalBasis (Fin d) ℝ (Tangent d))
    (i0 : Fin d) (h : ℝ → ℝ) :
    ∫ v : Tangent d, h ⟪b i0, v⟫ * gE t v = ∫ s, h s * DGPS.gauss1 t s := by
  simp_rw [gE_eq_prod ht b]
  exact (integral_basis_coords b (fun y => h (y i0) * ∏ j, DGPS.gauss1 t (y j))).trans
    (integral_prod_update ht i0 h)

theorem integrable_inner_gE {t : ℝ} (ht : 0 < t) (b : OrthonormalBasis (Fin d) ℝ (Tangent d))
    (i0 : Fin d) {h : ℝ → ℝ} (hh : Integrable (fun s => h s * DGPS.gauss1 t s)) :
    Integrable (fun v : Tangent d => h ⟪b i0, v⟫ * gE t v) := by
  simp_rw [gE_eq_prod ht b]
  exact (integrable_basis_coords b (fun y => h (y i0) * ∏ j, DGPS.gauss1 t (y j))).mpr
    (integrable_prod_update ht i0 hh)

theorem exists_basis_of_unit {u : Tangent d} (hu : ‖u‖ = 1) (i0 : Fin d) :
    ∃ b : OrthonormalBasis (Fin d) ℝ (Tangent d), b i0 = u := by
  have hv : Orthonormal ℝ (({i0} : Set (Fin d)).domRestrict (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have : i = j := Subsingleton.elim (α := ({i0} : Set (Fin d))) i j
    subst this
    simp [Set.domRestrict, hu]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp) hv
  exact ⟨b, hb i0 rfl⟩

theorem integrable_abs_inner_gE {t : ℝ} (ht : 0 < t) (c : Tangent d) :
    Integrable (fun v : Tangent d => |⟪c, v⟫| * gE t v) := by
  by_cases hc : c = 0
  · subst hc; simp
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨i0⟩ : Nonempty (Fin d) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hc (Subsingleton.elim _ _)
  obtain ⟨b, hb⟩ := exists_basis_of_unit (u := ‖c‖⁻¹ • c) (by rw [norm_smul]; simp [hc'.ne']) i0
  have := (integrable_inner_gE ht b i0 (integrable_abs_mul_gauss1 ht)).const_mul ‖c‖
  refine this.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [hb, inner_smul_left, abs_mul]
  simp only [conj_trivial, abs_inv, abs_norm]
  field_simp

theorem integral_abs_inner_gE {t : ℝ} (ht : 0 < t) (c : Tangent d) :
    ∫ v : Tangent d, |⟪c, v⟫| * gE t v = ‖c‖ * (2 * t * (π * t) ^ (-(1 : ℝ) / 2)) := by
  by_cases hc : c = 0
  · subst hc; simp
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨i0⟩ : Nonempty (Fin d) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hc (Subsingleton.elim _ _)
  obtain ⟨b, hb⟩ := exists_basis_of_unit (u := ‖c‖⁻¹ • c) (by rw [norm_smul]; simp [hc'.ne']) i0
  have h1 := integral_inner_gE ht b i0 (fun s => |s|)
  rw [hb] at h1
  rw [integral_abs_mul_gauss1 ht] at h1
  have h2 : ∀ v : Tangent d, |⟪c, v⟫| * gE t v = ‖c‖ * (|⟪‖c‖⁻¹ • c, v⟫| * gE t v) := by
    intro v
    simp only [inner_smul_left, abs_mul]
    simp only [conj_trivial, abs_inv, abs_norm]
    field_simp
  simp_rw [h2]
  rw [integral_const_mul, h1]

theorem continuous_gE (t : ℝ) : Continuous (gE t : Tangent d → ℝ) := by
  unfold gE; fun_prop

theorem gE_pos {t : ℝ} (ht : 0 < t) (v : Tangent d) : 0 < gE t v := by
  unfold gE
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

theorem gE_nonneg {t : ℝ} (ht : 0 < t) (v : Tangent d) : 0 ≤ gE t v := (gE_pos ht v).le

theorem integrable_gE {t : ℝ} (ht : 0 < t) (hd : 0 < d) : Integrable (gE t : Tangent d → ℝ) := by
  have := integrable_inner_gE ht (EuclideanSpace.basisFun (Fin d) ℝ) ⟨0, hd⟩ (h := fun _ => 1)
    (by simpa using integrable_gauss1 ht)
  simpa using this

theorem integral_gE {t : ℝ} (ht : 0 < t) (hd : 0 < d) : ∫ v : Tangent d, gE t v = 1 := by
  have := integral_inner_gE ht (EuclideanSpace.basisFun (Fin d) ℝ) ⟨0, hd⟩ (fun _ => 1)
  simpa [integral_gauss1 ht] using this

theorem integrable_sq_gE {t : ℝ} (ht : 0 < t) :
    Integrable (fun v : Tangent d => ‖v‖ ^ 2 * gE t v) := by
  have h : ∀ v : Tangent d, ‖v‖ ^ 2 * gE t v =
      ∑ j, (⟪EuclideanSpace.basisFun (Fin d) ℝ j, v⟫ ^ 2 * gE t v) := by
    intro v
    rw [← Finset.sum_mul, ← (EuclideanSpace.basisFun (Fin d) ℝ).sum_sq_norm_inner_right v]
    simp
  simp_rw [h]
  refine integrable_finsetSum _ fun j _ => ?_
  exact integrable_inner_gE ht (EuclideanSpace.basisFun (Fin d) ℝ) j (h := fun s => s ^ 2)
    (integrable_sq_mul_gauss1 ht)

theorem integral_sq_gE {t : ℝ} (ht : 0 < t) :
    ∫ v : Tangent d, ‖v‖ ^ 2 * gE t v = 2 * t * d := by
  have h : ∀ v : Tangent d, ‖v‖ ^ 2 * gE t v =
      ∑ j, (⟪EuclideanSpace.basisFun (Fin d) ℝ j, v⟫ ^ 2 * gE t v) := by
    intro v
    rw [← Finset.sum_mul, ← (EuclideanSpace.basisFun (Fin d) ℝ).sum_sq_norm_inner_right v]
    simp
  simp_rw [h]
  rw [integral_finsetSum _ fun j _ => integrable_inner_gE ht (EuclideanSpace.basisFun (Fin d) ℝ) j
    (h := fun s => s ^ 2) (integrable_sq_mul_gauss1 ht)]
  have : ∀ j : Fin d, ∫ v : Tangent d, ⟪EuclideanSpace.basisFun (Fin d) ℝ j, v⟫ ^ 2 * gE t v = 2 * t :=
    fun j => by
      rw [integral_inner_gE ht (EuclideanSpace.basisFun (Fin d) ℝ) j (fun s => s ^ 2)]
      exact integral_sq_gauss1 ht
  rw [Finset.sum_congr rfl fun j _ => this j]
  simp; ring

theorem integrable_norm_gE {t : ℝ} (ht : 0 < t) (hd : 0 < d) :
    Integrable (fun v : Tangent d => ‖v‖ * gE t v) := by
  refine ((integrable_sq_gE ht).add (integrable_gE ht hd)).mono'
    ((continuous_norm.mul (continuous_gE t)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v => ?_)
  have h0 := gE_nonneg ht v
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) h0)]
  show ‖v‖ * gE t v ≤ ‖v‖ ^ 2 * gE t v + gE t v
  have : ‖v‖ ≤ ‖v‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖v‖ - 1/2), norm_nonneg v]
  nlinarith [mul_le_mul_of_nonneg_right this h0]

theorem integral_norm_gE_le {t : ℝ} (ht : 0 < t) (hd : 0 < d) :
    ∫ v : Tangent d, ‖v‖ * gE t v ≤ Real.sqrt (2 * t * d) := by
  set c := Real.sqrt (2 * t * d) with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hcc : c ^ 2 = 2 * t * d := Real.sq_sqrt (by positivity)
  have h1 : ∫ v : Tangent d, ‖v‖ * gE t v ≤ ∫ v : Tangent d, (1 / (2 * c)) * (‖v‖ ^ 2 * gE t v) +
      (c / 2) * gE t v := by
    refine integral_mono (integrable_norm_gE ht hd) (((integrable_sq_gE ht).const_mul _).add
      ((integrable_gE ht hd).const_mul _)) fun v => ?_
    have h0 := gE_nonneg ht v
    have : ‖v‖ ≤ (1 / (2 * c)) * ‖v‖ ^ 2 + c / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖v‖ - c)]
    show _ ≤ (1 / (2 * c)) * (‖v‖ ^ 2 * gE t v) + c / 2 * gE t v
    nlinarith [mul_le_mul_of_nonneg_right this h0]
  refine h1.trans (le_of_eq ?_)
  rw [integral_add ((integrable_sq_gE ht).const_mul _) ((integrable_gE ht hd).const_mul _),
    integral_const_mul, integral_const_mul, integral_sq_gE ht, integral_gE ht hd]
  field_simp
  rw [← hcc]; ring

/-- The integer lattice point `n ∈ ℤ^d` as a vector of `ℝ^d` (Euclidean). -/
noncomputable def nE (n : Fin d → ℤ) : Tangent d := WithLp.toLp 2 (fun j => (n j : ℝ))

theorem summable_gE_nE {s : ℝ} (hs : 0 < s) :
    Summable (fun n : Fin d → ℤ => gE s (nE n)) := by
  have h := (summable_prod_tsum_prod_fin d (fun _ (m : ℤ) => DGPS.gauss1 s (m : ℝ))
    (fun j m => DGPS.gauss1_nonneg s _ hs)
    (fun j => by simpa using DGPS.summable_gauss1_add_int hs 0)).1
  refine h.congr fun n => ?_
  rw [gE_eq_prod hs (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp [nE, EuclideanSpace.inner_single_left]

theorem gE_shift_le {s : ℝ} (hs : 0 < s) (R : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ x y : Tangent d, ‖x‖ ≤ R → gE s (x + y) ≤ B * gE (2 * s) y := by
  have hc : 0 < (4 * π * (2 * s)) ^ (-(d : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hc' : 0 < (4 * π * s) ^ (-(d : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨(4 * π * s) ^ (-(d : ℝ) / 2) * Real.exp (R ^ 2 / (4 * s)) /
    (4 * π * (2 * s)) ^ (-(d : ℝ) / 2), by positivity, fun x y hx => ?_⟩
  unfold gE
  have e : (4 * π * s) ^ (-(d : ℝ) / 2) * Real.exp (R ^ 2 / (4 * s)) /
      (4 * π * (2 * s)) ^ (-(d : ℝ) / 2) *
      ((4 * π * (2 * s)) ^ (-(d : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * (2 * s)))) =
      (4 * π * s) ^ (-(d : ℝ) / 2) *
      (Real.exp (R ^ 2 / (4 * s)) * Real.exp (-‖y‖ ^ 2 / (4 * (2 * s)))) := by
    field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hc'.le
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : ‖y‖ ≤ ‖x + y‖ + ‖x‖ := by
    calc ‖y‖ = ‖(x + y) - x‖ := by simp
      _ ≤ ‖x + y‖ + ‖x‖ := norm_sub_le _ _
  have h2 : ‖x‖ ^ 2 ≤ R ^ 2 := by
    have := norm_nonneg x
    nlinarith
  have h3 : ‖y‖ ^ 2 ≤ 2 * ‖x + y‖ ^ 2 + 2 * R ^ 2 := by
    have := norm_nonneg x
    have := norm_nonneg y
    have := norm_nonneg (x + y)
    nlinarith [sq_nonneg (‖x + y‖ - ‖x‖)]
  have : -‖x + y‖ ^ 2 / (4 * s) ≤ R ^ 2 / (4 * s) + -‖y‖ ^ 2 / (4 * (2 * s)) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [mul_pos hs hs]
  exact this

theorem norm_mul_gE_le {s : ℝ} (hs : 0 < s) :
    ∃ C, 0 ≤ C ∧ ∀ w : Tangent d, ‖w‖ * gE s w ≤ C * gE (2 * s) w := by
  have hc : 0 < (4 * π * (2 * s)) ^ (-(d : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hc' : 0 < (4 * π * s) ^ (-(d : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨(s + 2) * (4 * π * s) ^ (-(d : ℝ) / 2) /
    (4 * π * (2 * s)) ^ (-(d : ℝ) / 2), by positivity, fun w => ?_⟩
  unfold gE
  set r := ‖w‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg w
  set q := r ^ 2 / (8 * s) with hq
  have hq0 : 0 ≤ q := by positivity
  have e1 : -r ^ 2 / (4 * s) = -q + -q := by rw [hq]; ring
  have e2 : -r ^ 2 / (4 * (2 * s)) = -q := by rw [hq]; ring
  rw [e1, e2, Real.exp_add]
  have hE : 0 < Real.exp q := Real.exp_pos q
  have hE' : 0 < Real.exp (-q) := Real.exp_pos _
  have hle : r ≤ (s + 2) * Real.exp q := by
    have h := Real.add_one_le_exp q
    have : r ≤ s + 2 * q := by
      have e : s + 2 * q - r = (r - 2 * s) ^ 2 / (4 * s) := by
        rw [hq]; field_simp; ring
      have : 0 ≤ (r - 2 * s) ^ 2 / (4 * s) := by positivity
      linarith
    nlinarith
  have key : r * Real.exp (-q) ≤ s + 2 := by
    have h1 : r * Real.exp (-q) ≤ (s + 2) * Real.exp q * Real.exp (-q) :=
      mul_le_mul_of_nonneg_right hle hE'.le
    rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h1
  have e3 : (s + 2) * (4 * π * s) ^ (-(d : ℝ) / 2) /
      (4 * π * (2 * s)) ^ (-(d : ℝ) / 2) *
      ((4 * π * (2 * s)) ^ (-(d : ℝ) / 2) * Real.exp (-q)) =
      (4 * π * s) ^ (-(d : ℝ) / 2) * Real.exp (-q) * (s + 2) := by
    field_simp
  rw [e3]
  have e4 : r * ((4 * π * s) ^ (-(d : ℝ) / 2) * (Real.exp (-q) * Real.exp (-q))) =
      (4 * π * s) ^ (-(d : ℝ) / 2) * Real.exp (-q) * (r * Real.exp (-q)) := by ring
  rw [e4]
  exact mul_le_mul_of_nonneg_left key (by positivity)

/-- The heat kernel on `ℝ^d` (Euclidean), the periodic lift of `heatKernelT`. -/
noncomputable def Kh (t : ℝ) (v : Tangent d) : ℝ := SharpLSI.heatPL t v.ofLp

theorem Kh_eq_tsum {t : ℝ} (ht : 0 < t) (v : Tangent d) :
    Kh t v = ∑' n : Fin d → ℤ, gE t (v + nE n) := by
  unfold Kh
  rw [← DGPS.periodizedGaussian_eq_heatPL ht]
  unfold DGPS.periodizedGaussian gE
  refine tsum_congr fun n => ?_
  congr 3
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [nE]

theorem hasFDerivAt_gE {t : ℝ} (ht : 0 < t) (y : Tangent d) :
    HasFDerivAt (gE t) (-(gE t y / (2 * t)) • innerSL ℝ y) y := by
  have h1 : HasFDerivAt (fun v : Tangent d => ‖v‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have h2 := ((h1.const_mul (-(1 / (4 * t)))).exp).const_mul ((4 * π * t) ^ (-(d : ℝ) / 2))
  have hg : gE t = fun v : Tangent d => (4 * π * t) ^ (-(d : ℝ) / 2) *
      Real.exp (-(1 / (4 * t)) * ‖v‖ ^ 2) := by
    funext v; unfold gE; congr 2; ring
  rw [hg]
  refine h2.congr_fderiv ?_
  ext v
  simp
  field_simp
  norm_num

theorem dterm_majorant {t : ℝ} (ht : 0 < t) (R : ℝ) :
    ∃ u : (Fin d → ℤ) → ℝ, Summable u ∧ ∀ (n : Fin d → ℤ) (y : Tangent d), ‖y‖ ≤ R →
      ‖-(gE t (y + nE n) / (2 * t)) • innerSL ℝ (y + nE n)‖ ≤ u n := by
  obtain ⟨C, hC0, hC⟩ := norm_mul_gE_le (d := d) ht
  have h2t : 0 < 2 * t := by positivity
  obtain ⟨B, hB0, hB⟩ := gE_shift_le (d := d) h2t R
  have hsum := summable_gE_nE (d := d) (s := 2 * (2 * t)) (by positivity)
  refine ⟨fun n => C * B * gE (2 * (2 * t)) (nE n) / (2 * t),
    (hsum.mul_left (C * B)).div_const _, fun n y hy' => ?_⟩
  rw [norm_smul, innerSL_apply_norm, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (gE_pos ht _).le h2t.le)]
  have h1 := hC (y + nE n)
  have h2 := hB y (nE n) hy'
  rw [div_mul_eq_mul_div, mul_comm]
  refine div_le_div_of_nonneg_right ?_ h2t.le
  calc ‖y + nE n‖ * gE t (y + nE n) ≤ C * gE (2 * t) (y + nE n) := h1
    _ ≤ C * (B * gE (2 * (2 * t)) (nE n)) := mul_le_mul_of_nonneg_left h2 hC0
    _ = C * B * gE (2 * (2 * t)) (nE n) := by ring

theorem hasFDerivAt_Kh {t : ℝ} (ht : 0 < t) (x : Tangent d) :
    HasFDerivAt (Kh t)
      (∑' n : Fin d → ℤ, -(gE t (x + nE n) / (2 * t)) • innerSL ℝ (x + nE n)) x := by
  obtain ⟨u, hu, hub⟩ := dterm_majorant (d := d) ht (‖x‖ + 1)
  have hfun : Kh t = fun y => ∑' n : Fin d → ℤ, gE t (y + nE n) := funext (Kh_eq_tsum ht)
  rw [hfun]
  refine hasFDerivAt_tsum_of_isPreconnected (f := fun n y => gE t (y + nE n))
    (f' := fun n y => -(gE t (y + nE n) / (2 * t)) • innerSL ℝ (y + nE n))
    (u := u) (s := Metric.ball (0 : Tangent d) (‖x‖ + 1)) (x₀ := 0) hu
    Metric.isOpen_ball (convex_ball _ _).isPreconnected ?_ ?_ (Metric.mem_ball_self (by positivity))
    ?_ (Metric.mem_ball.mpr (by rw [dist_zero_right]; linarith))
  · intro n y _
    have := (hasFDerivAt_gE ht (y + nE n)).comp y ((hasFDerivAt_id y).add_const (nE n))
    refine this.congr_fderiv ?_
    ext v
    simp
  · intro n y hy
    exact hub n y (by simpa using (Metric.mem_ball.mp hy).le)
  · simpa using summable_gE_nE (d := d) ht

theorem summable_norm_dterm {t : ℝ} (ht : 0 < t) (x : Tangent d) :
    Summable fun n : Fin d → ℤ => ‖-(gE t (x + nE n) / (2 * t)) • innerSL ℝ (x + nE n)‖ := by
  obtain ⟨u, hu, hub⟩ := dterm_majorant (d := d) ht ‖x‖
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hub n x le_rfl) hu

theorem norm_fderiv_Kh_le {t : ℝ} (ht : 0 < t) (x : Tangent d) :
    ‖fderiv ℝ (Kh t) x‖ ≤ ∑' n : Fin d → ℤ, ‖x + nE n‖ * gE t (x + nE n) / (2 * t) := by
  rw [(hasFDerivAt_Kh ht x).fderiv]
  refine (norm_tsum_le_tsum_norm (summable_norm_dterm ht x)).trans (le_of_eq (tsum_congr fun n => ?_))
  rw [norm_smul, innerSL_apply_norm, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (gE_pos ht _).le (by positivity))]
  ring

theorem abs_fderiv_Kh_le {t : ℝ} (ht : 0 < t) (x a : Tangent d) :
    |fderiv ℝ (Kh t) x a| ≤ ∑' n : Fin d → ℤ, |⟪x + nE n, a⟫| * gE t (x + nE n) / (2 * t) := by
  have hs := summable_norm_dterm ht x
  have hs' : Summable fun n : Fin d → ℤ => -(gE t (x + nE n) / (2 * t)) • innerSL ℝ (x + nE n) :=
    hs.of_norm
  rw [(hasFDerivAt_Kh ht x).fderiv, tsum_apply hs']
  have hterm : ∀ n : Fin d → ℤ, ‖(-(gE t (x + nE n) / (2 * t)) • innerSL ℝ (x + nE n)) a‖ =
      |⟪x + nE n, a⟫| * gE t (x + nE n) / (2 * t) := by
    intro n
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, norm_mul,
      Real.norm_eq_abs, abs_neg, abs_div]
    rw [abs_of_pos (gE_pos ht _), abs_of_pos (by positivity : (0:ℝ) < 2 * t)]
    ring
  have hsa : Summable fun n : Fin d → ℤ =>
      ‖(-(gE t (x + nE n) / (2 * t)) • innerSL ℝ (x + nE n)) a‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hs.mul_right ‖a‖)
    exact (ContinuousLinearMap.le_opNorm _ _)
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hsa).trans (le_of_eq (tsum_congr hterm))

theorem contDiff_Kh {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (Kh (d := d) t) :=
  (SharpLSI.contDiff_heatPL ht).comp (EuclideanSpace.equiv (Fin d) ℝ).contDiff

theorem Kh_add_nE (t : ℝ) (v : Tangent d) (n : Fin d → ℤ) : Kh t (v + nE n) = Kh t v := by
  unfold Kh
  have : (v + nE n).ofLp = v.ofLp + SharpLSI.intVec n := rfl
  rw [this]
  exact SharpLSI.heatPL_add_intVec t _ n

theorem fderiv_Kh_add_nE (t : ℝ) (v : Tangent d) (n : Fin d → ℤ) :
    fderiv ℝ (Kh t) (v + nE n) = fderiv ℝ (Kh t) v := by
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := Kh (d := d) t) (x := v) (nE n)
  have hf : (fun x => Kh t (x + nE n)) = Kh t := funext fun x => Kh_add_nE t x n
  rw [hf] at h
  exact h.symm

/-- The Euclidean copy of the section `secT`. -/
noncomputable def secE (w : Torus d) : Tangent d := WithLp.toLp 2 (SharpLSI.secT w)

theorem measurable_secE : Measurable (secE (d := d)) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.comp SharpLSI.measurable_secT

theorem norm_secE_le (w : Torus d) : ‖secE w‖ ≤ d := by
  have h1 : ‖secE w‖ ^ 2 ≤ d := by
    rw [tangent_norm_sq]
    calc ∑ j, (secE w) j ^ 2 ≤ ∑ _j : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h := DGPS.secT_mem_Icc w
          have hj : (0 : ℝ) ≤ SharpLSI.secT w j ∧ SharpLSI.secT w j ≤ 1 := ⟨h.1 j, h.2 j⟩
          show SharpLSI.secT w j ^ 2 ≤ 1
          nlinarith [hj.1, hj.2]
      _ = d := by simp
  by_contra hlt
  push Not at hlt
  have hd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero d
  nlinarith [norm_nonneg (secE w), Nat.cast_nonneg (α := ℝ) d]

/-- The lifted heat semigroup on `ℝ^d`. -/
noncomputable def Hl (t : ℝ) (f : Torus d → ℝ) (v : Tangent d) : ℝ :=
  heatOp t f (torusLift v.ofLp)

theorem Hl_eq (t : ℝ) (f : Torus d → ℝ) (v : Tangent d) :
    Hl t f v = ∫ w, f w * Kh t (v - secE w) ∂haar d := by
  unfold Hl heatOp torusConv
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  show heatKernelT t (torusLift v.ofLp - w) * f w = _
  rw [mul_comm]
  congr 1
  conv_lhs => rw [← SharpLSI.liftT_secT w]
  rw [← SharpLSI.liftT_sub]
  exact SharpLSI.heatP_liftT t _

theorem hasFDerivAt_Hl {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    (v : Tangent d) :
    HasFDerivAt (Hl t f) (∫ w, f w • fderiv ℝ (Kh t) (v - secE w) ∂haar d) v := by
  have hKc : Continuous (Kh (d := d) t) := (contDiff_Kh ht).continuous
  have hKd : Continuous (fderiv ℝ (Kh (d := d) t)) :=
    (contDiff_Kh ht).continuous_fderiv (by simp)
  have hsub : ∀ x : Tangent d, Continuous fun w : Tangent d => x - w := fun x => by fun_prop
  have hmeas : ∀ x : Tangent d, Measurable fun w : Torus d => x - secE w :=
    fun x => measurable_const.sub measurable_secE
  have hball : ∀ x : Tangent d, x ∈ Metric.closedBall v 1 → ∀ w : Torus d,
      x - secE w ∈ Metric.closedBall (0 : Tangent d) (‖v‖ + 1 + d) := by
    intro x hx w
    have h1 := Metric.mem_closedBall.1 hx
    have h2 := norm_secE_le (d := d) w
    rw [mem_closedBall_zero_iff]
    calc ‖x - secE w‖ ≤ ‖x‖ + ‖secE w‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + 1 + d := by
        have : ‖x‖ ≤ ‖v‖ + 1 := by
          have := norm_le_norm_add_norm_sub' x v
          have h3 : ‖x - v‖ ≤ 1 := by simpa [dist_eq_norm] using h1
          linarith
        linarith
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : Tangent d) (‖v‖ + 1 + d)).exists_bound_of_continuousOn
    hKc.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Tangent d) (‖v‖ + 1 + d)).exists_bound_of_continuousOn
    hKd.continuousOn
  have hfun : Hl t f = fun x => ∫ w, f w * Kh t (x - secE w) ∂haar d := funext (Hl_eq t f)
  rw [hfun]
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := haar d) (x₀ := v)
    (F := fun x w => f w * Kh t (x - secE w))
    (F' := fun x w => f w • fderiv ℝ (Kh t) (x - secE w))
    (bound := fun w => ‖f w‖ * max M 0) (s := Metric.ball v 1) (Metric.ball_mem_nhds _ one_pos)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact key
  · refine Filter.Eventually.of_forall fun x => ?_
    exact hf.aestronglyMeasurable.mul
      ((hKc.measurable.comp (hmeas x)).aestronglyMeasurable)
  · refine Integrable.mono' (hf.norm.mul_const (max M0 0)) ?_ ?_
    · exact hf.aestronglyMeasurable.mul
        ((hKc.measurable.comp (hmeas v)).aestronglyMeasurable)
    · refine Filter.Eventually.of_forall fun w => ?_
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ((hM0 _ (hball v (by simp) w)).trans (le_max_left _ _)) (norm_nonneg _)
  · exact hf.aestronglyMeasurable.smul
      ((hKd.measurable.comp (hmeas v)).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall fun w x hx => ?_
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ((hM _ (hball x ?_ w)).trans (le_max_left _ _)) (norm_nonneg _)
    exact Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hx))
  · exact (hf.norm.mul_const _)
  · refine Filter.Eventually.of_forall fun w x _ => ?_
    have h1 : HasFDerivAt (fun x : Tangent d => x - secE w) (ContinuousLinearMap.id ℝ _) x :=
      (hasFDerivAt_id x).sub_const _
    have h2 := ((contDiff_Kh ht).differentiable (by simp) (x - secE w)).hasFDerivAt.comp x h1
    simpa using h2.const_mul (f w)

/-- Unfolding the integral over the unit box of a lattice sum. -/
theorem lintegral_unitBox_tsum (Φ : (Fin d → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ x in SharpLSI.unitBox (Fin d), ∑' m : Fin d → ℤ, Φ (x + SharpLSI.intVec m) =
      ∫⁻ x, Φ x := by
  rw [lintegral_tsum (f := fun (m : Fin d → ℤ) (x : Fin d → ℝ) => Φ (x + SharpLSI.intVec m))
    (fun m => (hΦ.comp (measurable_id.add_const _)).aemeasurable)]
  have hcover : (⋃ m : Fin d → ℤ, SharpLSI.shiftBox m) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨fun i => ⌈x i⌉ - 1, ?_⟩
    rw [SharpLSI.mem_shiftBox]
    intro i
    constructor
    · have := Int.ceil_lt_add_one (x i)
      have h2 := Int.lt_ceil.1 (show ((⌈x i⌉ - 1 : ℤ)) < ⌈x i⌉ by omega)
      push_cast at h2 ⊢
      linarith
    · have := Int.le_ceil (x i)
      push_cast
      linarith
  have hdisj : Pairwise (Function.onFun Disjoint fun m : Fin d → ℤ => SharpLSI.shiftBox m) := by
    intro m m' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    apply hne
    funext i
    rw [SharpLSI.shiftBox_eq_ceil hx i, SharpLSI.shiftBox_eq_ceil hx' i]
  calc ∑' m : Fin d → ℤ, ∫⁻ x in SharpLSI.unitBox (Fin d), Φ (x + SharpLSI.intVec m)
      = ∑' m : Fin d → ℤ, ∫⁻ x in SharpLSI.shiftBox m, Φ x := by
        refine tsum_congr fun m => ?_
        have hmp : MeasurePreserving (fun x : Fin d → ℝ => x - SharpLSI.intVec m) volume volume :=
          measurePreserving_sub_right volume _
        have := hmp.setLIntegral_comp_preimage (s := SharpLSI.unitBox (Fin d))
          (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
          (f := fun x => Φ (x + SharpLSI.intVec m)) (hΦ.comp (measurable_id.add_const _))
        simp only [sub_add_cancel] at this
        exact this.symm
    _ = ∫⁻ x in ⋃ m : Fin d → ℤ, SharpLSI.shiftBox m, Φ x :=
        (lintegral_iUnion (fun m => SharpLSI.measurableSet_shiftBox m) hdisj Φ).symm
    _ = ∫⁻ x, Φ x := by rw [hcover, Measure.restrict_univ]

theorem lintegral_sub_toLp (P : Tangent d → ℝ≥0∞) (hP : Measurable P) (v : Tangent d) :
    ∫⁻ y : Fin d → ℝ, P (v - WithLp.toLp 2 y) = ∫⁻ z, P z := by
  have h1 : Measurable fun z : Tangent d => P (v - z) := hP.comp (measurable_const.sub measurable_id)
  rw [(PiLp.volume_preserving_toLp (Fin d)).lintegral_comp h1]
  exact lintegral_sub_left_eq_self (μ := (volume : Measure (Tangent d))) P v

theorem secE_torusLift {x : Fin d → ℝ} (hx : x ∈ SharpLSI.unitBox (Fin d)) :
    secE (torusLift x) = WithLp.toLp 2 x := by
  unfold secE torusLift
  rw [SharpLSI.secT_liftT hx]

theorem lintegral_torus_fold (P : Tangent d → ℝ≥0∞) (hP : Measurable P) (v : Tangent d) :
    ∫⁻ w, ∑' n : Fin d → ℤ, P (v - secE w + nE n) ∂haar d = ∫⁻ z, P z := by
  have hH : Measurable fun w : Torus d => ∑' n : Fin d → ℤ, P (v - secE w + nE n) :=
    Measurable.tsum fun n =>
      hP.comp ((measurable_const.sub measurable_secE).add_const _)
  rw [haar_eq_map_unitBox, lintegral_map hH SharpLSI.measurable_liftT]
  have h2 : ∀ x ∈ SharpLSI.unitBox (Fin d),
      (∑' n : Fin d → ℤ, P (v - secE (torusLift x) + nE n)) =
        ∑' m : Fin d → ℤ, (fun y : Fin d → ℝ => P (v - WithLp.toLp 2 y)) (x + SharpLSI.intVec m) := by
    intro x hx
    rw [secE_torusLift hx]
    rw [← (Equiv.neg (Fin d → ℤ)).tsum_eq]
    refine tsum_congr fun m => ?_
    congr 1
    simp only [Equiv.neg_apply]
    have : (WithLp.toLp 2 (x + SharpLSI.intVec m) : Tangent d) =
        WithLp.toLp 2 x + nE m := rfl
    have h3 : nE (-m) = - nE m := by
      ext j; simp [nE]
    rw [this, h3]; abel
  have hmeas : Measurable fun y : Fin d → ℝ => P (v - WithLp.toLp 2 y) :=
    hP.comp (measurable_const.sub (PiLp.volume_preserving_toLp (Fin d)).measurable)
  have hmu : MeasurableSet (SharpLSI.unitBox (Fin d)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  refine (setLIntegral_congr_fun hmu h2).trans ?_
  rw [lintegral_unitBox_tsum _ hmeas]
  exact lintegral_sub_toLp P hP v

/-- The density used to bound the directional derivative of the kernel. -/
noncomputable def Pa (t : ℝ) (a z : Tangent d) : ℝ := |⟪z, a⟫| * gE t z / (2 * t)

theorem Pa_nonneg {t : ℝ} (ht : 0 < t) (a z : Tangent d) : 0 ≤ Pa t a z := by
  unfold Pa
  have := gE_nonneg ht z
  positivity

theorem measurable_Pa (t : ℝ) (a : Tangent d) : Measurable (Pa t a) := by
  unfold Pa
  have : Continuous (Pa t a) := by
    unfold Pa
    have := continuous_gE (d := d) t
    fun_prop
  exact this.measurable

theorem summable_Pa {t : ℝ} (ht : 0 < t) (x a : Tangent d) :
    Summable fun n : Fin d → ℤ => Pa t a (x + nE n) := by
  have hs := summable_norm_dterm ht x
  refine Summable.of_nonneg_of_le (fun n => Pa_nonneg ht a _) (fun n => ?_) (hs.mul_right ‖a‖)
  have h1 : ‖-(gE t (x + nE n) / (2 * t)) • innerSL ℝ (x + nE n)‖ =
      ‖x + nE n‖ * gE t (x + nE n) / (2 * t) := by
    rw [norm_smul, innerSL_apply_norm, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (gE_pos ht _).le (by positivity))]
    ring
  rw [h1]
  unfold Pa
  have h2 : |⟪x + nE n, a⟫| ≤ ‖x + nE n‖ * ‖a‖ := abs_real_inner_le_norm _ _
  have h3 := gE_pos ht (x + nE n)
  have h4 : (0:ℝ) < 2 * t := by positivity
  rw [div_le_iff₀ h4]
  have : ‖x + nE n‖ * gE t (x + nE n) / (2 * t) * ‖a‖ * (2 * t) =
      ‖x + nE n‖ * ‖a‖ * gE t (x + nE n) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right h2 h3.le

theorem ofReal_abs_fderiv_Kh_le {t : ℝ} (ht : 0 < t) (x a : Tangent d) :
    ENNReal.ofReal |fderiv ℝ (Kh t) x a| ≤ ∑' n : Fin d → ℤ, ENNReal.ofReal (Pa t a (x + nE n)) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => Pa_nonneg ht a _) (summable_Pa ht x a)]
  refine ENNReal.ofReal_le_ofReal ((abs_fderiv_Kh_le ht x a).trans (le_of_eq ?_))
  rfl

theorem integral_Pa {t : ℝ} (ht : 0 < t) (a : Tangent d) :
    ∫ z, Pa t a z = ‖a‖ * (π * t) ^ (-(1 : ℝ) / 2) := by
  have h : ∀ z : Tangent d, Pa t a z = (|⟪a, z⟫| * gE t z) / (2 * t) := by
    intro z; unfold Pa; rw [real_inner_comm]
  simp_rw [h]
  rw [integral_div, integral_abs_inner_gE ht a]
  field_simp

theorem integrable_Pa {t : ℝ} (ht : 0 < t) (a : Tangent d) : Integrable (Pa t a) := by
  have h : ∀ z : Tangent d, Pa t a z = (|⟪a, z⟫| * gE t z) / (2 * t) := by
    intro z; unfold Pa; rw [real_inner_comm]
  rw [show Pa t a = fun z => (|⟪a, z⟫| * gE t z) / (2 * t) from funext h]
  exact (integrable_abs_inner_gE ht a).div_const _

theorem lintegral_abs_fderiv_Kh_le {t : ℝ} (ht : 0 < t) (v a : Tangent d) :
    ∫⁻ w, ENNReal.ofReal |fderiv ℝ (Kh t) (v - secE w) a| ∂haar d ≤
      ENNReal.ofReal (‖a‖ * (π * t) ^ (-(1 : ℝ) / 2)) := by
  calc ∫⁻ w, ENNReal.ofReal |fderiv ℝ (Kh t) (v - secE w) a| ∂haar d
      ≤ ∫⁻ w, ∑' n : Fin d → ℤ, ENNReal.ofReal (Pa t a (v - secE w + nE n)) ∂haar d :=
        lintegral_mono fun w => ofReal_abs_fderiv_Kh_le ht _ a
    _ = ∫⁻ z, ENNReal.ofReal (Pa t a z) :=
        lintegral_torus_fold (fun z => ENNReal.ofReal (Pa t a z))
          (ENNReal.measurable_ofReal.comp (measurable_Pa t a)) v
    _ = ENNReal.ofReal (∫ z, Pa t a z) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_Pa ht a)
          (Filter.Eventually.of_forall fun z => Pa_nonneg ht a z)).symm
    _ = _ := by rw [integral_Pa ht]

theorem exists_bound_dKh {t : ℝ} (ht : 0 < t) (v : Tangent d) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ w : Torus d, ‖fderiv ℝ (Kh t) (v - secE w)‖ ≤ M0 := by
  have hKd : Continuous (fderiv ℝ (Kh (d := d) t)) :=
    (contDiff_Kh ht).continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Tangent d) (‖v‖ + d)).exists_bound_of_continuousOn
    hKd.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun w => (hM _ ?_).trans (le_max_left _ _)⟩
  rw [mem_closedBall_zero_iff]
  calc ‖v - secE w‖ ≤ ‖v‖ + ‖secE w‖ := norm_sub_le _ _
    _ ≤ ‖v‖ + d := by linarith [norm_secE_le (d := d) w]

theorem integrable_smul_dKh {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    (v : Tangent d) :
    Integrable (fun w => f w • fderiv ℝ (Kh t) (v - secE w)) (haar d) := by
  have hKd : Continuous (fderiv ℝ (Kh (d := d) t)) :=
    (contDiff_Kh ht).continuous_fderiv (by simp)
  obtain ⟨M0, hM0, hb⟩ := exists_bound_dKh ht v
  refine Integrable.mono' (hf.norm.mul_const M0) ?_ ?_
  · exact hf.aestronglyMeasurable.smul
      ((hKd.measurable.comp (measurable_const.sub measurable_secE)).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall fun w => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hb w) (norm_nonneg _)

theorem abs_fderiv_Hl_apply_le {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ w ∂haar d, |f w| ≤ M) (v a : Tangent d) :
    |fderiv ℝ (Hl t f) v a| ≤ M * (‖a‖ * (π * t) ^ (-(1 : ℝ) / 2)) := by
  have hD := hasFDerivAt_Hl ht hf v
  rw [hD.fderiv, ContinuousLinearMap.integral_apply (integrable_smul_dKh ht hf v) a]
  simp only [smul_apply, smul_eq_mul]
  have hc : 0 ≤ ‖a‖ * (π * t) ^ (-(1 : ℝ) / 2) := by positivity
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc ∫⁻ w, ENNReal.ofReal ‖f w * fderiv ℝ (Kh t) (v - secE w) a‖ ∂haar d
      ≤ ∫⁻ w, ENNReal.ofReal M * ENNReal.ofReal |fderiv ℝ (Kh t) (v - secE w) a| ∂haar d := by
        refine lintegral_mono_ae (hM.mono fun w hw => ?_)
        rw [Real.norm_eq_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hw) _
    _ = ENNReal.ofReal M * ∫⁻ w, ENNReal.ofReal |fderiv ℝ (Kh t) (v - secE w) a| ∂haar d :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (‖a‖ * (π * t) ^ (-(1 : ℝ) / 2)) :=
        mul_le_mul_right (lintegral_abs_fderiv_Kh_le ht v a) _
    _ = ENNReal.ofReal (M * (‖a‖ * (π * t) ^ (-(1 : ℝ) / 2))) := (ENNReal.ofReal_mul hM0).symm

theorem torusDist_sub_le (v v' : Tangent d) (z : Torus d) :
    torusDist (torusLift v.ofLp - z) (torusLift v'.ofLp - z) ≤ ‖v - v'‖ := by
  have hz : z = torusLift (SharpLSI.secT z) := (SharpLSI.liftT_secT z).symm
  rw [hz]
  have h1 : ∀ u : Tangent d, torusLift u.ofLp - torusLift (SharpLSI.secT z) =
      torusLift (u.ofLp - SharpLSI.secT z) := fun u => (SharpLSI.liftT_sub _ _).symm
  rw [h1, h1]
  refine (torusDist_liftT_le _ _).trans (le_of_eq ?_)
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Real.norm_eq_abs, sq_abs]

theorem continuous_of_torusLipschitz {L : ℝ} (hL : 0 ≤ L) {f : Torus d → ℝ}
    (hf : TorusLipschitzWith L f) : Continuous f := by
  have : LipschitzWith (Real.toNNReal (L * Real.sqrt d)) f := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq]
    refine (hf x y).trans ?_
    have := (torusDist_comparison x y).2
    rw [Real.coe_toNNReal _ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left this hL]
  exact this.continuous

theorem lipschitz_Hl {t : ℝ} (ht : 0 < t) {L : ℝ} (hL : 0 ≤ L) {f : Torus d → ℝ}
    (hf : TorusLipschitzWith L f) : LipschitzWith (Real.toNNReal L) (Hl t f) := by
  have hfc := continuous_of_torusLipschitz hL hf
  have hfi : Integrable f (haar d) := integrable_of_continuous_torus hfc
  have hK := continuous_heatKernelT (d := d) ht
  have hK0 : ∀ z, 0 ≤ heatKernelT (d := d) t z := fun z => (heatKernelT_pos ht z).le
  have hK1 := integral_heatKernelT (d := d) ht
  have hKi : Integrable (heatKernelT (d := d) t) (haar d) := integrable_of_continuous_torus hK
  have hrew : ∀ y : Torus d, torusConv (heatKernelT t) f y =
      ∫ z, heatKernelT t z * f (y - z) ∂haar d := by
    intro y
    unfold torusConv
    rw [← integral_sub_left_eq_self (fun z => heatKernelT t z * f (y - z)) (haar d) y]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp
  refine LipschitzWith.of_dist_le_mul fun v v' => ?_
  rw [Real.dist_eq, dist_eq_norm]
  unfold Hl heatOp
  rw [hrew, hrew, ← integral_sub]
  · have key : ‖∫ z, (heatKernelT t z * f (torusLift v.ofLp - z) -
        heatKernelT t z * f (torusLift v'.ofLp - z)) ∂haar d‖ ≤
        ∫ z, heatKernelT t z * (L * ‖v - v'‖) ∂haar d := by
      refine norm_integral_le_of_norm_le (hKi.mul_const _) (Filter.Eventually.of_forall fun z => ?_)
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hK0 z), Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ((hf _ _).trans ?_) (hK0 z)
      exact mul_le_mul_of_nonneg_left (torusDist_sub_le v v' z) hL
    rw [integral_mul_const, hK1, one_mul] at key
    rw [Real.coe_toNNReal _ hL]
    simpa [Real.norm_eq_abs] using key
  · exact integrable_of_continuous_torus (hK.mul (hfc.comp (continuous_sub_left _)))
  · exact integrable_of_continuous_torus (hK.mul (hfc.comp (continuous_sub_left _)))

theorem secE_sub (y w : Torus d) : ∃ n : Fin d → ℤ, secE (y - w) = secE y - secE w + nE n := by
  have h : torusLift (SharpLSI.secT y - SharpLSI.secT w) = y - w := by
    unfold torusLift
    rw [SharpLSI.liftT_sub, SharpLSI.liftT_secT, SharpLSI.liftT_secT]
  obtain ⟨m, hm⟩ := SharpLSI.secT_liftT_eq (ι := Fin d) (SharpLSI.secT y - SharpLSI.secT w)
  refine ⟨m, ?_⟩
  have h2 : SharpLSI.secT (y - w) = SharpLSI.secT y - SharpLSI.secT w + SharpLSI.intVec m := by
    rw [← hm]; unfold torusLift at h; rw [h]
  unfold secE
  rw [h2]
  rfl

/-- The norm of the kernel gradient, as a function on the torus. -/
noncomputable def Psi (t : ℝ) (w : Torus d) : ℝ := ‖fderiv ℝ (Kh t) (secE w)‖

theorem Psi_nonneg (t : ℝ) (w : Torus d) : 0 ≤ Psi t w := norm_nonneg _

theorem Psi_torusLift (t : ℝ) (x : Fin d → ℝ) :
    Psi t (torusLift x) = ‖fderiv ℝ (Kh t) (WithLp.toLp 2 x)‖ := by
  obtain ⟨m, hm⟩ := SharpLSI.secT_liftT_eq (ι := Fin d) x
  unfold Psi secE
  have : (WithLp.toLp 2 (SharpLSI.secT (torusLift x)) : Tangent d) = WithLp.toLp 2 x + nE m := by
    unfold torusLift; rw [hm]; rfl
  rw [this, fderiv_Kh_add_nE]

theorem continuous_Psi {t : ℝ} (ht : 0 < t) : Continuous (Psi (d := d) t) := by
  refine continuous_of_comp_torusLift ?_
  have hKd : Continuous (fderiv ℝ (Kh (d := d) t)) :=
    (contDiff_Kh ht).continuous_fderiv (by simp)
  have : (Psi (d := d) t ∘ torusLift) = fun x : Fin d → ℝ => ‖fderiv ℝ (Kh t) (WithLp.toLp 2 x)‖ :=
    funext (Psi_torusLift t)
  rw [this]
  exact (hKd.comp (PiLp.continuous_toLp 2 _)).norm

theorem norm_fderiv_Kh_sub (t : ℝ) (y w : Torus d) :
    ‖fderiv ℝ (Kh t) (secE y - secE w)‖ = Psi t (y - w) := by
  obtain ⟨n, hn⟩ := secE_sub y w
  unfold Psi
  rw [hn, fderiv_Kh_add_nE]

theorem lintegral_torus_fold0 (P : Tangent d → ℝ≥0∞) (hP : Measurable P) :
    ∫⁻ w, ∑' n : Fin d → ℤ, P (secE w + nE n) ∂haar d = ∫⁻ z, P z := by
  have hH : Measurable fun w : Torus d => ∑' n : Fin d → ℤ, P (secE w + nE n) :=
    Measurable.tsum fun n => hP.comp (measurable_secE.add_const _)
  rw [haar_eq_map_unitBox, lintegral_map hH SharpLSI.measurable_liftT]
  have h2 : ∀ x ∈ SharpLSI.unitBox (Fin d),
      (∑' n : Fin d → ℤ, P (secE (torusLift x) + nE n)) =
        ∑' m : Fin d → ℤ, (fun y : Fin d → ℝ => P (WithLp.toLp 2 y)) (x + SharpLSI.intVec m) := by
    intro x hx
    rw [secE_torusLift hx]
    refine tsum_congr fun m => ?_
    rfl
  have hmeas : Measurable fun y : Fin d → ℝ => P (WithLp.toLp 2 y) :=
    hP.comp (PiLp.volume_preserving_toLp (Fin d)).measurable
  have hmu : MeasurableSet (SharpLSI.unitBox (Fin d)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  refine (setLIntegral_congr_fun hmu h2).trans ?_
  rw [lintegral_unitBox_tsum _ hmeas]
  exact (PiLp.volume_preserving_toLp (Fin d)).lintegral_comp hP

/-- Radial density bounding the norm of the kernel gradient. -/
noncomputable def Qn (t : ℝ) (z : Tangent d) : ℝ := ‖z‖ * gE t z / (2 * t)

theorem Qn_nonneg {t : ℝ} (ht : 0 < t) (z : Tangent d) : 0 ≤ Qn t z := by
  unfold Qn
  have := gE_nonneg ht z
  positivity

theorem measurable_Qn (t : ℝ) : Measurable (Qn (d := d) t) := by
  have : Continuous (Qn (d := d) t) := by
    unfold Qn
    have := continuous_gE (d := d) t
    fun_prop
  exact this.measurable

theorem summable_Qn {t : ℝ} (ht : 0 < t) (x : Tangent d) :
    Summable fun n : Fin d → ℤ => Qn t (x + nE n) := by
  refine (summable_norm_dterm ht x).congr fun n => ?_
  rw [norm_smul, innerSL_apply_norm, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (gE_pos ht _).le (by positivity))]
  unfold Qn
  ring

theorem integral_Qn_le {t : ℝ} (ht : 0 < t) (hd : 0 < d) :
    Integrable (Qn (d := d) t) ∧ ∫ z : Tangent d, Qn t z ≤ Real.sqrt (2 * t * d) / (2 * t) := by
  have h : Qn (d := d) t = fun z => (‖z‖ * gE t z) / (2 * t) := rfl
  rw [h]
  refine ⟨(integrable_norm_gE ht hd).div_const _, ?_⟩
  rw [integral_div]
  exact div_le_div_of_nonneg_right (integral_norm_gE_le ht hd) (by positivity)

theorem integral_Psi_le {t : ℝ} (ht : 0 < t) (hd : 0 < d) :
    ∫ w, Psi t w ∂haar d ≤ Real.sqrt (2 * t * d) / (2 * t) := by
  obtain ⟨hQi, hQ⟩ := integral_Qn_le (d := d) ht hd
  have hPi : Integrable (Psi (d := d) t) (haar d) :=
    integrable_of_continuous_torus (continuous_Psi ht)
  have hc : 0 ≤ Real.sqrt (2 * t * d) / (2 * t) := by positivity
  have h1 : ENNReal.ofReal (∫ w, Psi t w ∂haar d) ≤ ENNReal.ofReal (Real.sqrt (2 * t * d) / (2 * t)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hPi (Filter.Eventually.of_forall (Psi_nonneg t))]
    calc ∫⁻ w, ENNReal.ofReal (Psi t w) ∂haar d
        ≤ ∫⁻ w, ∑' n : Fin d → ℤ, ENNReal.ofReal (Qn t (secE w + nE n)) ∂haar d := by
          refine lintegral_mono fun w => ?_
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => Qn_nonneg ht _) (summable_Qn ht _)]
          refine ENNReal.ofReal_le_ofReal ((norm_fderiv_Kh_le ht (secE w)).trans (le_of_eq ?_))
          rfl
      _ = ∫⁻ z, ENNReal.ofReal (Qn t z) :=
          lintegral_torus_fold0 (fun z => ENNReal.ofReal (Qn t z))
            (ENNReal.measurable_ofReal.comp (measurable_Qn t))
      _ = ENNReal.ofReal (∫ z : Tangent d, Qn t z) :=
          (ofReal_integral_eq_lintegral_ofReal hQi
            (Filter.Eventually.of_forall fun z => Qn_nonneg ht z)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hQ
  exact (ENNReal.ofReal_le_ofReal_iff hc).1 h1

theorem coordPartial_heatOp {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    (j : Fin d) (y : Torus d) :
    coordPartial j (heatOp t f) y =
      ∫ w, f w * fderiv ℝ (Kh t) (secE y - secE w) (EuclideanSpace.single j 1) ∂haar d := by
  have hD := hasFDerivAt_Hl ht hf (secE y)
  have hT : HasFDerivAt (fun x : Fin d → ℝ => (WithLp.toLp 2 x : Tangent d))
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm : (Fin d → ℝ) →L[ℝ] Tangent d)
      (SharpLSI.secT y) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.hasFDerivAt
  have hc := HasFDerivAt.comp (SharpLSI.secT y) (show HasFDerivAt (Hl t f) _ (WithLp.toLp 2 (SharpLSI.secT y)) from hD) hT
  unfold coordPartial
  have hfun : (heatOp t f ∘ torusLift) = (Hl t f ∘ fun x : Fin d → ℝ => (WithLp.toLp 2 x : Tangent d)) := rfl
  rw [hfun, hc.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.integral_apply (integrable_smul_dKh ht hf (secE y))]
  simp only [smul_apply, smul_eq_mul]
  rfl

theorem abs_div_le {t : ℝ} (ht : 0 < t) {F : Torus d → Tangent d} (hF : Integrable F (haar d))
    (y : Torus d) :
    |∑ j, coordPartial j (heatOp t fun w => F w j) y| ≤
      torusConv (Psi t) (fun w => ‖F w‖) y := by
  have hfj : ∀ j : Fin d, Integrable (fun w => F w j) (haar d) := fun j =>
    (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).integrable_comp hF
  have hint : ∀ j : Fin d, Integrable (fun w => F w j *
      fderiv ℝ (Kh t) (secE y - secE w) (EuclideanSpace.single j 1)) (haar d) := fun j => by
    have := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1:ℝ) : Tangent d)).integrable_comp
      (integrable_smul_dKh ht (hfj j) (secE y))
    simpa using this
  simp_rw [coordPartial_heatOp ht (hfj _)]
  rw [← integral_finsetSum _ fun j _ => hint j]
  have hpt : ∀ w, ∑ j, F w j * fderiv ℝ (Kh t) (secE y - secE w) (EuclideanSpace.single j 1) =
      fderiv ℝ (Kh t) (secE y - secE w) (F w) := by
    intro w
    conv_rhs => rw [show F w = ∑ j, F w j • (EuclideanSpace.single j (1:ℝ) : Tangent d) from by
      ext i; simp [Pi.single_apply]]
    simp [map_sum]
  simp_rw [hpt]
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (integrable_conv_integrand (continuous_Psi ht) hF.norm y)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [← norm_fderiv_Kh_sub t y w]
  exact (fderiv ℝ (Kh t) (secE y - secE w)).le_opNorm (F w)

/-- The dominating probability kernel for the gradient of the heat kernel. -/
theorem exists_dom_kernel {t : ℝ} (ht : 0 < t) (hd : 0 < d) :
    ∃ K : Torus d → ℝ, Continuous K ∧ (∀ z, 0 ≤ K z) ∧ ∫ z, K z ∂haar d = 1 ∧
      ∀ z, Psi t z ≤ (Real.sqrt (2 * t * d) / (2 * t)) * K z := by
  set c0 := Real.sqrt (2 * t * d) / (2 * t) with hc0
  have hc0pos : 0 < c0 := by
    have : 0 < Real.sqrt (2 * t * d) := Real.sqrt_pos.2 (by positivity)
    positivity
  set m := ∫ w, Psi t w ∂haar d with hm
  have hmle : m ≤ c0 := integral_Psi_le ht hd
  have hm0 : 0 ≤ m := integral_nonneg (Psi_nonneg t)
  have hKc := continuous_heatKernelT (d := d) ht
  have hKi : Integrable (heatKernelT (d := d) t) (haar d) := integrable_of_continuous_torus hKc
  have hPi : Integrable (Psi (d := d) t) (haar d) := integrable_of_continuous_torus (continuous_Psi ht)
  have hcoef : 0 ≤ 1 - m / c0 := by
    rw [sub_nonneg, div_le_one hc0pos]; exact hmle
  refine ⟨fun z => Psi t z / c0 + (1 - m / c0) * heatKernelT t z, ?_, fun z => ?_, ?_, fun z => ?_⟩
  · exact ((continuous_Psi ht).div_const _).add (continuous_const.mul hKc)
  · exact add_nonneg (div_nonneg (Psi_nonneg t z) hc0pos.le)
      (mul_nonneg hcoef (heatKernelT_pos ht z).le)
  · rw [integral_add (hPi.div_const _) (hKi.const_mul _), integral_div, integral_const_mul,
      integral_heatKernelT ht]
    field_simp
    ring
  · have h1 : 0 ≤ c0 * ((1 - m / c0) * heatKernelT t z) :=
      mul_nonneg hc0pos.le (mul_nonneg hcoef (heatKernelT_pos ht z).le)
    have h2 : c0 * (Psi t z / c0 + (1 - m / c0) * heatKernelT t z) =
        Psi t z + c0 * ((1 - m / c0) * heatKernelT t z) := by
      field_simp
    rw [h2]
    linarith

theorem abs_div_le_conv {t : ℝ} (ht : 0 < t) {F : Torus d → Tangent d}
    (hF : Integrable F (haar d)) {K : Torus d → ℝ} (hK : Continuous K)
    (hKP : ∀ z, Psi t z ≤ (Real.sqrt (2 * t * d) / (2 * t)) * K z) (y : Torus d) :
    |∑ j, coordPartial j (heatOp t fun w => F w j) y| ≤
      (Real.sqrt (2 * t * d) / (2 * t)) * torusConv K (fun w => ‖F w‖) y := by
  refine (abs_div_le ht hF y).trans ?_
  unfold torusConv
  rw [← integral_const_mul]
  refine integral_mono (integrable_conv_integrand (continuous_Psi ht) hF.norm y)
    ((integrable_conv_integrand hK hF.norm y).const_mul _) fun w => ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hKP _) (norm_nonneg _)

theorem measurable_coordPartial_fun (j : Fin d) (φ : Torus d → ℝ) : Measurable (coordPartial j φ) := by
  unfold coordPartial
  exact ((measurable_fderiv ℝ (φ ∘ torusLift)).comp SharpLSI.measurable_secT).apply_continuousLinearMap
    (Pi.single j 1)

theorem aestronglyMeasurable_div (F : Torus d → Tangent d) (t : ℝ) :
    AEStronglyMeasurable (fun y => ∑ j, coordPartial j (heatOp t fun w => F w j) y) (haar d) :=
  (Finset.measurable_sum _ fun j _ => measurable_coordPartial_fun j _).aestronglyMeasurable

theorem div_bound {t : ℝ} (ht : 0 < t) (hd : 0 < d) {F : Torus d → Tangent d} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hF : MemLp F p (haar d)) :
    eLpNorm (fun y => ∑ j, coordPartial j (heatOp t fun w => F w j) y) p (haar d) ≤
      ENNReal.ofReal (Real.sqrt (2 * t * d) / (2 * t)) * eLpNorm F p (haar d) := by
  obtain ⟨K, hKc, hK0, hK1, hKP⟩ := exists_dom_kernel ht hd
  set c0 := Real.sqrt (2 * t * d) / (2 * t) with hc0
  have hc0pos : 0 < c0 := by
    have : 0 < Real.sqrt (2 * t * d) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hFi : Integrable F (haar d) := hF.integrable hp
  have hpt : ∀ y, ‖∑ j, coordPartial j (heatOp t fun w => F w j) y‖ ≤
      c0 * torusConv K (fun w => ‖F w‖) y := fun y => by
    rw [Real.norm_eq_abs]; exact abs_div_le_conv ht hFi hKc hKP y
  have hm := aestronglyMeasurable_div (t := t) F
  by_cases hp' : p = ⊤
  · subst hp'
    have hfin : eLpNorm F ⊤ (haar d) < ⊤ := hF.eLpNorm_lt_top
    set B := (eLpNorm F ⊤ (haar d)).toReal with hB
    have hBe : ENNReal.ofReal B = eLpNorm F ⊤ (haar d) := ENNReal.ofReal_toReal hfin.ne
    have hae : ∀ᵐ w ∂haar d, ‖F w‖ ≤ B := by
      have := enorm_ae_le_eLpNormEssSup F (haar d)
      filter_upwards [this] with w hw
      rw [← eLpNorm_exponent_top hF.aestronglyMeasurable, ← hBe] at hw
      rw [← ofReal_norm] at hw
      exact (ENNReal.ofReal_le_ofReal_iff (ENNReal.toReal_nonneg)).1 hw
    have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
    have hcongr : torusConv K (fun w => ‖F w‖) = torusConv K (fun w => min ‖F w‖ B) :=
      torusConv_congr_ae K (hae.mono fun w hw => (min_eq_left hw).symm)
    have hbd : ∀ y, ‖∑ j, coordPartial j (heatOp t fun w => F w j) y‖ ≤ c0 * B := fun y => by
      refine (hpt y).trans ?_
      rw [hcongr]
      refine mul_le_mul_of_nonneg_left ?_ hc0pos.le
      refine (le_abs_self _).trans (abs_torusConv_le hKc hK0 hK1 (B := B) (fun x => ?_) y)
      rw [abs_of_nonneg (le_min (norm_nonneg _) hB0)]
      exact min_le_right _ _
    rw [eLpNorm_exponent_top hm]
    refine (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hbd)).trans ?_
    rw [ENNReal.ofReal_mul hc0pos.le, hBe]
  · have hg : MemLp (fun w => ‖F w‖) p (haar d) := hF.norm
    calc eLpNorm (fun y => ∑ j, coordPartial j (heatOp t fun w => F w j) y) p (haar d)
        ≤ eLpNorm (fun y => c0 * torusConv K (fun w => ‖F w‖) y) p (haar d) := by
          refine eLpNorm_mono hm fun y => ?_
          refine (hpt y).trans ?_
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc0pos.le
            (torusConv_nonneg hK0 (Filter.Eventually.of_forall fun w => norm_nonneg _) y))]
      _ = ENNReal.ofReal c0 * eLpNorm (torusConv K (fun w => ‖F w‖)) p (haar d) := by
          have := eLpNorm_const_smul (μ := haar d) (p := p) c0 (torusConv K (fun w => ‖F w‖))
          rw [Real.enorm_eq_ofReal hc0pos.le] at this
          exact this
      _ ≤ ENNReal.ofReal c0 * eLpNorm (fun w => ‖F w‖) p (haar d) := by
          exact mul_le_mul_right (eLpNorm_torusConv_le hKc hK0 hK1 hp hp' hg) _
      _ = _ := by rw [eLpNorm_norm F hF.aestronglyMeasurable]

theorem sqrt_const_eq {t : ℝ} (ht : 0 < t) (d : ℕ) :
    Real.sqrt (2 * t * d) / (2 * t) = Real.sqrt (d / 2) * t ^ (-(1 : ℝ) / 2) := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h1 : Real.sqrt (2 * t * d) = 2 * Real.sqrt (d / 2) * Real.sqrt t := by
    rw [show 2 * t * (d : ℝ) = (2 * Real.sqrt (d / 2) * Real.sqrt t) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt ht.le]; ring]
    exact Real.sqrt_sq (by positivity)
  have h2 : t ^ (-(1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le]; congr 1; ring
  have h3 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  rw [h1, h2]
  generalize Real.sqrt t = s at *
  subst h3
  field_simp

/-- **LIP006.** Gradient bounds for the periodized heat semigroup `H_t = e^{tΔ}` on `𝕋^d`,
for `t > 0`.  The gradient is the Fréchet derivative of the lift `v ↦ (H_t g)(v mod ℤ^d)` to
`ℝ^d = Tangent d`, with the Euclidean operator norm.

* (i) if `g` is measurable with `|g| ≤ M` a.e., then `H_t g` is differentiable with
  `‖∇ H_t g‖ ≤ (π t)^{-1/2} M`;
* (ii) if `f` is `L`-Lipschitz for the torus distance (`0 ≤ L`), then `H_t f` is differentiable
  with `‖∇ H_t f‖ ≤ L`;
* (iii) for a vector field `F ∈ Lᵖ(𝕋^d; ℝ^d)`, `p ∈ [1, ∞]` (in particular `p ∈ {1, 2, ∞}`),
  `‖div H_t F‖_{Lᵖ} ≤ √(d/2) t^{-1/2} ‖F‖_{Lᵖ}`, where
  `div H_t F = ∑ⱼ ∂ⱼ (H_t Fⱼ)`. -/
theorem periodized_heat_gradient_bounds {t : ℝ} (ht : 0 < t) :
    (∀ {g : Torus d → ℝ} {M : ℝ}, AEStronglyMeasurable g (haar d) →
      (∀ᵐ w ∂haar d, |g w| ≤ M) → ∀ v : Tangent d,
        DifferentiableAt ℝ (fun u : Tangent d => heatOp t g (torusLift u.ofLp)) v ∧
        ‖fderiv ℝ (fun u : Tangent d => heatOp t g (torusLift u.ofLp)) v‖ ≤
          (π * t) ^ (-(1 : ℝ) / 2) * M) ∧
    (∀ {f : Torus d → ℝ} {L : ℝ}, 0 ≤ L → TorusLipschitzWith L f → ∀ v : Tangent d,
        DifferentiableAt ℝ (fun u : Tangent d => heatOp t f (torusLift u.ofLp)) v ∧
        ‖fderiv ℝ (fun u : Tangent d => heatOp t f (torusLift u.ofLp)) v‖ ≤ L) ∧
    (∀ {F : Torus d → Tangent d} {p : ℝ≥0∞}, 1 ≤ p → MemLp F p (haar d) →
        eLpNorm (fun y => ∑ j, coordPartial j (heatOp t fun w => F w j) y) p (haar d) ≤
          ENNReal.ofReal (Real.sqrt (d / 2) * t ^ (-(1 : ℝ) / 2)) * eLpNorm F p (haar d)) := by
  refine ⟨fun {g M} hg hM v => ?_, fun {f L} hL hf v => ?_, fun {F p} hp hF => ?_⟩
  · have hM0 : 0 ≤ M := by
      obtain ⟨w, hw⟩ := hM.exists
      exact (abs_nonneg _).trans hw
    have hgi : Integrable g (haar d) := Integrable.of_bound hg M (hM.mono fun w hw => by
      rwa [Real.norm_eq_abs])
    refine ⟨(hasFDerivAt_Hl ht hgi v).differentiableAt, ?_⟩
    have hc : 0 ≤ (π * t) ^ (-(1 : ℝ) / 2) := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
    rw [Real.norm_eq_abs]
    refine (abs_fderiv_Hl_apply_le ht hgi hM0 hM v a).trans (le_of_eq ?_)
    ring
  · have hfc := continuous_of_torusLipschitz hL hf
    have hfi : Integrable f (haar d) := integrable_of_continuous_torus hfc
    refine ⟨(hasFDerivAt_Hl ht hfi v).differentiableAt, ?_⟩
    have := norm_fderiv_le_of_lipschitz ℝ (lipschitz_Hl ht hL hf) (x₀ := v)
    rwa [Real.coe_toNNReal _ hL] at this
  · rw [← sqrt_const_eq ht]
    rcases Nat.eq_zero_or_pos d with h0 | hd
    · subst h0
      simp
    · exact div_bound ht hd hp hF

end DGPS.Lipschitz
