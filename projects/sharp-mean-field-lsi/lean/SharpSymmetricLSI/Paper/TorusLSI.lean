import SharpSymmetricLSI.Paper.CircleLSIExt
import SharpSymmetricLSI.Paper.CosineFiber
import SharpSymmetricLSI.Infra.EntropyTensor

/-!
# The sharp logarithmic Sobolev inequality on `𝕋^ι` (Phase 3, lane C; for `cosine_defective`)

`Ent_m(h²) ≤ (2/a) ∫ |∇h|² dm` on `𝕋^ι`, `a = 4π²`.
* Circle: from Lemma 3.2, `H ≤ 6 log(1 + I/(12a)) ≤ I/(2a)`, applied to `ρ = φ²/∫φ²`.
* Tensorization (Gross) by induction on `card ι`, splitting off one coordinate (`splitT`) and
  using the subadditivity `entR_prod_le`; first for smooth positive periodic lifts.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI

/-! ### Integrals over a one-coordinate torus -/

theorem integral_unique_coord {ι : Type*} [Unique ι] (g : UnitAddCircle → ℝ) :
    ∫ y : UnitAddTorus ι, g (y default) = ∫ t in Ioc (0 : ℝ) 1, g t := by
  have h := (volume_preserving_funUnique ι UnitAddCircle).integral_comp' (g := g)
  simp only [MeasurableEquiv.funUnique_apply] at h
  calc ∫ y : UnitAddTorus ι, g (y default) = ∫ y : UnitAddCircle, g y := h
    _ = _ := by rw [← UnitAddCircle.integral_preimage 0 g, zero_add]

theorem integral_unique_secT {ι : Type*} [Unique ι] (g : ℝ → ℝ) :
    ∫ y : UnitAddTorus ι, g (secT y default) = ∫ t in Ioc (0 : ℝ) 1, g t := by
  have := integral_unique_coord (ι := ι) (fun z => g ((AddCircle.equivIoc 1 0 z : ℝ)))
  rw [show (fun y : UnitAddTorus ι => g (secT y default)) =
    fun y => g ((AddCircle.equivIoc 1 0 (y default) : ℝ)) from rfl, this]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  congr 1
  have : AddCircle.equivIoc 1 0 (t : UnitAddCircle) = ⟨t, by simpa using ht⟩ :=
    AddCircle.equivIoc_coe_eq (by simpa using ht)
  rw [this]

/-! ### The circle inequality for smooth positive periodic functions -/

theorem periodic_int' {φ : ℝ → ℝ} (hper : ∀ t, φ (t + 1) = φ t) (t : ℝ) (n : ℤ) :
    φ (t + n) = φ t := periodic_int hper n t

/-- `∫₀¹ φ² log φ² - Z log Z ≤ (2/a) ∫₀¹ φ'²`, `Z = ∫₀¹ φ²`, for smooth positive `1`-periodic `φ`. -/
theorem lsi_interval {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hper : ∀ t, φ (t + 1) = φ t)
    (hpos : ∀ t, 0 < φ t) :
    (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2 * Real.log (φ t ^ 2)) -
        (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) * Real.log (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) ≤
      2 / aCos * ∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2 := by
  have hc : Continuous φ := hφ.continuous
  have hdc : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  set Z := ∫ t in Ioc (0 : ℝ) 1, φ t ^ 2 with hZ
  have hZ0 : 0 < Z := by
    rw [hZ, ← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on ((hc.pow 2).intervalIntegrable 0 1)
      (fun t _ => pow_pos (hpos t) 2) zero_lt_one
  have ha0 : 0 < aCos := by unfold aCos; positivity
  -- the density on `𝕋`
  set v : Torus 1 → ℝ := fun z => φ (secT z 0) / Real.sqrt Z with hv
  set ρ : Torus 1 → ℝ := fun z => φ (secT z 0) ^ 2 / Z with hρdef
  have hρ0 : ∀ z, 0 ≤ ρ z := fun z => by positivity
  have hρ1 : ∫ z, ρ z ∂haar 1 = 1 := by
    simp only [hρdef]
    rw [integral_div, integral_torus1_secT (fun t => φ t ^ 2), ← hZ, div_self hZ0.ne']
  have hsq : (fun z => Real.sqrt (ρ z)) = v := funext fun z => by
    simp only [hρdef, hv]
    rw [Real.sqrt_div' _ hZ0.le, Real.sqrt_sq (hpos _).le]
  have hvlift : v ∘ liftT = fun x => φ (x 0) / Real.sqrt Z := by
    funext x
    obtain ⟨m, hm⟩ := secT_liftT_eq x
    simp only [Function.comp_apply, hv, hm, Pi.add_apply, intVec]
    rw [periodic_int' hper]
  have hvs : ContDiff ℝ ∞ (v ∘ liftT) := by
    rw [hvlift]; exact (hφ.comp (contDiff_apply ℝ ℝ (0 : Fin 1))).div_const _
  have hH1 : MemH1 (haar 1) (fun z => Real.sqrt (ρ z)) := by rw [hsq]; exact memH1_of_contDiff hvs
  have aux := circle_quantitative_lsi_aux hρ0 hρ1 hH1
  -- the Fisher information
  have hgrad : ∀ x : Fin 1 → ℝ, fderiv ℝ (v ∘ liftT) x (Pi.single 0 1) = deriv φ (x 0) / Real.sqrt Z := by
    intro x
    rw [hvlift]
    have h1 : HasDerivAt (fun s => φ s / Real.sqrt Z) (deriv φ (x 0) / Real.sqrt Z) (x 0) :=
      (hφ.differentiable (by simp) (x 0)).hasDerivAt.div_const _
    have hd := h1.comp_hasFDerivAt x (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) x)
    rw [show (fun x : Fin 1 → ℝ => φ (x 0) / Real.sqrt Z) =
      (fun s => φ s / Real.sqrt Z) ∘ (fun f : Fin 1 → ℝ => f 0) from rfl, hd.fderiv]
    simp
  have hfi : (fisherInfo (densMeasure ρ) (haar 1)).toReal =
      4 / Z * ∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2 := by
    rw [fisherInfo_densMeasure_eq hρ0 hρ1 hH1, hsq]
    have hw := weakGrad_ae_eq_of_contDiff (hvs.of_le (by simp))
    have : ∫ x, weakGrad v x 0 ^ 2 ∂haar 1 = ∫ x, (deriv φ (secT x 0) / Real.sqrt Z) ^ 2 ∂haar 1 :=
      integral_congr_ae (hw.mono fun x hx => by simp only [hx, hgrad])
    rw [this, integral_torus1_secT (fun t => (deriv φ t / Real.sqrt Z) ^ 2)]
    simp_rw [div_pow, Real.sq_sqrt hZ0.le]
    rw [integral_div, ENNReal.toReal_ofReal (by positivity)]
    ring
  -- the entropy
  have hkl : (klDiv (densMeasure ρ) (haar 1)).toReal =
      ((∫ t in Ioc (0 : ℝ) 1, φ t ^ 2 * Real.log (φ t ^ 2)) - Z * Real.log Z) / Z := by
    have hmeas : AEStronglyMeasurable (fun z => klFun (ρ z)) (haar 1) :=
      continuous_klFun.comp_aestronglyMeasurable
        (((hc.measurable.comp ((measurable_pi_apply 0).comp measurable_secT)).pow_const 2).div_const
          Z).aestronglyMeasurable
    rw [klDiv_densMeasure hρ0 hρ1, ← integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun z => klFun_nonneg (hρ0 z)) hmeas]
    simp only [hρdef]
    rw [integral_torus1_secT (fun t => klFun (φ t ^ 2 / Z))]
    have e : ∀ t, klFun (φ t ^ 2 / Z) = (φ t ^ 2 * Real.log (φ t ^ 2) - φ t ^ 2 * Real.log Z) / Z +
        1 - φ t ^ 2 / Z := fun t => by
      rw [klFun_apply, Real.log_div (pow_ne_zero 2 (hpos t).ne') hZ0.ne']; ring
    simp_rw [e]
    have i1 : IntegrableOn (fun t => φ t ^ 2 * Real.log (φ t ^ 2)) (Ioc 0 1) :=
      ((hc.pow 2).mul ((hc.pow 2).log fun t => pow_ne_zero 2 (hpos t).ne')).integrableOn_Ioc
    have i2 : IntegrableOn (fun t => φ t ^ 2) (Ioc 0 1) := (hc.pow 2).integrableOn_Ioc
    have i3 : IntegrableOn (fun t => (φ t ^ 2 * Real.log (φ t ^ 2) - φ t ^ 2 * Real.log Z) / Z)
        (Ioc 0 1) := (i1.sub (i2.mul_const _)).div_const Z
    have i4 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 1) := integrableOn_const (by simp) (by simp)
    have i5 : IntegrableOn (fun t => (φ t ^ 2 * Real.log (φ t ^ 2) - φ t ^ 2 * Real.log Z) / Z + 1)
        (Ioc 0 1) := i3.add i4
    have i6 : IntegrableOn (fun t => φ t ^ 2 / Z) (Ioc 0 1) := i2.div_const Z
    rw [integral_sub (μ := (volume : Measure ℝ).restrict (Ioc 0 1))
        (f := fun t => (φ t ^ 2 * Real.log (φ t ^ 2) - φ t ^ 2 * Real.log Z) / Z + 1)
        (g := fun t => φ t ^ 2 / Z) i5 i6,
      integral_add (μ := (volume : Measure ℝ).restrict (Ioc 0 1))
        (f := fun t => (φ t ^ 2 * Real.log (φ t ^ 2) - φ t ^ 2 * Real.log Z) / Z)
        (g := fun _ => (1 : ℝ)) i3 i4, integral_div,
      integral_sub (μ := (volume : Measure ℝ).restrict (Ioc 0 1))
        (f := fun t => φ t ^ 2 * Real.log (φ t ^ 2)) (g := fun t => φ t ^ 2 * Real.log Z)
        i1 (i2.mul_const _), integral_mul_const, integral_div, ← hZ]
    simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
      Real.volume_real_Ioc, sub_zero, smul_eq_mul, mul_one, max_eq_left zero_le_one]
    field_simp
    ring
  -- `H ≤ I/(2a)`
  have h310 := aux.2.2.1
  have hlog : Real.log (1 + (fisherInfo (densMeasure ρ) (haar 1)).toReal / (12 * aCos)) ≤
      (fisherInfo (densMeasure ρ) (haar 1)).toReal / (12 * aCos) := by
    have h0 : 0 ≤ (fisherInfo (densMeasure ρ) (haar 1)).toReal / (12 * aCos) :=
      div_nonneg ENNReal.toReal_nonneg (by positivity)
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + (fisherInfo (densMeasure ρ) (haar 1)).toReal / (12 * aCos))
    linarith
  have hH : (klDiv (densMeasure ρ) (haar 1)).toReal ≤
      (fisherInfo (densMeasure ρ) (haar 1)).toReal / (2 * aCos) := by
    have := h310.trans (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 6))
    rw [show 6 * ((fisherInfo (densMeasure ρ) (haar 1)).toReal / (12 * aCos)) =
      (fisherInfo (densMeasure ρ) (haar 1)).toReal / (2 * aCos) by field_simp; ring] at this
    exact this
  rw [hkl, hfi] at hH
  have := mul_le_mul_of_nonneg_left hH hZ0.le
  rw [mul_div_cancel₀ _ hZ0.ne'] at this
  have h4 : Z * ((4 / Z * ∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2) / (2 * aCos)) =
      2 / aCos * ∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2 := by field_simp; ring
  rw [h4] at this
  exact this

/-! ### The smooth positive inequality on `𝕋^ι` -/

/-- The smooth-positive LSI on `𝕋^ι`, at the level of periodic lifts. -/
def LSILift (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ Φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ Φ → IsPer Φ → (∀ x, 0 < Φ x) →
    entR volume (fun y : UnitAddTorus ι => Φ (secT y) ^ 2) ≤
      2 / aCos * ∫ y : UnitAddTorus ι, ∑ k, Dk Φ k (secT y) ^ 2

theorem lsiLift_empty (ι : Type) [Fintype ι] [DecidableEq ι] [IsEmpty ι] : LSILift ι := by
  intro Φ _ _ _
  have hu : ∀ F : UnitAddTorus ι → ℝ, ∫ y, F y = F default := fun F => by
    rw [MeasureTheory.integral_unique]; simp only [probReal_univ, one_smul]
    exact congrArg F (Subsingleton.elim _ _)
  unfold entR
  rw [hu, hu, hu]
  simp

theorem lsiLift_unique (ι : Type) [inst : Fintype ι] [DecidableEq ι] [Unique ι] : LSILift ι := by
  have h := Subsingleton.elim inst (@Unique.fintype ι _)
  subst h
  intro Φ hΦ hper hpos
  set c : ℝ → (ι → ℝ) := fun t _ => t with hcdef
  have hc : ContDiff ℝ ∞ c := contDiff_pi.2 fun _ => contDiff_id
  set φ : ℝ → ℝ := fun t => Φ (c t) with hφdef
  have hφ : ContDiff ℝ ∞ φ := hΦ.comp hc
  have hφper : ∀ t, φ (t + 1) = φ t := fun t => by
    have := hper (fun _ => 1) (c t)
    simp only [hφdef]
    rw [← this]; congr 1; funext i; simp [hcdef, intVec]
  have hφpos : ∀ t, 0 < φ t := fun t => hpos _
  have hsec : ∀ y : UnitAddTorus ι, secT y = c (secT y default) := fun y => by
    funext i; rw [Unique.eq_default i]
  have hD : ∀ x : ι → ℝ, x = c (x default) → Dk Φ default x = deriv φ (x default) := by
    intro x hx
    have h1 : HasDerivAt c (fun _ => 1) (x default) := hasDerivAt_pi.2 fun _ => hasDerivAt_id' _
    have h2 := (hΦ.differentiable (by simp) (c (x default))).hasFDerivAt.comp_hasDerivAt
      (x default) h1
    have h3 : deriv φ (x default) = fderiv ℝ Φ (c (x default)) (fun _ => 1) := h2.deriv
    rw [h3, Dk, ← hx]
    congr 1; funext i; rw [Unique.eq_default i]; simp
  have hlhs : entR volume (fun y : UnitAddTorus ι => Φ (secT y) ^ 2) =
      (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2 * Real.log (φ t ^ 2)) -
        (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) * Real.log (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) := by
    have hΦs : ∀ y : UnitAddTorus ι, Φ (secT y) = φ (secT y default) := fun y => by
      conv_lhs => rw [hsec y]
    unfold entR
    simp_rw [hΦs]
    rw [integral_unique_secT (ι := ι) (fun t => φ t ^ 2 * Real.log (φ t ^ 2)),
      integral_unique_secT (ι := ι) (fun t => φ t ^ 2)]
  have hrhs : ∫ y : UnitAddTorus ι, ∑ k, Dk Φ k (secT y) ^ 2 =
      ∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2 := by
    simp_rw [Fintype.sum_unique]
    have : ∀ y : UnitAddTorus ι, Dk Φ default (secT y) ^ 2 = deriv φ (secT y default) ^ 2 :=
      fun y => by rw [hD _ (hsec y)]
    simp_rw [this]
    exact integral_unique_secT (ι := ι) (fun t => deriv φ t ^ 2)
  rw [hlhs, hrhs]
  exact lsi_interval hφ hφper hφpos

section Fiber

variable {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι}

theorem mergeR_add_single_left (a : {i // i ≠ p} → ℝ) (b : SpT p → ℝ) (k : {i // i ≠ p}) (t : ℝ) :
    mergeR p (a + t • Pi.single k 1) b = mergeR p a b + t • Pi.single k.val 1 := by
  funext i
  by_cases h : i ≠ p
  · simp only [mergeR, dif_pos h, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hik : i = k.val
    · subst hik; simp
    · rw [Pi.single_eq_of_ne (fun h' => hik (congrArg Subtype.val h')),
        Pi.single_eq_of_ne hik]
  · have hi : i = p := not_not.mp h
    subst hi
    simp only [mergeR, dif_neg h, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Pi.single_eq_of_ne (fun h' => k.2 h'.symm)]; ring

theorem contDiff_mergeR_left (b : SpT p → ℝ) : ContDiff ℝ ∞ (fun a => mergeR p a b) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : i ≠ p
  · simp only [mergeR, dif_pos h]; exact contDiff_apply ℝ ℝ _
  · simp only [mergeR, dif_neg h]; exact contDiff_const

theorem Dk_fiber_left {Φ : (ι → ℝ) → ℝ} (hΦ : Differentiable ℝ Φ) (a : {i // i ≠ p} → ℝ)
    (b : SpT p → ℝ) (k : {i // i ≠ p}) :
    Dk (fun a => Φ (mergeR p a b)) k a = Dk Φ k.val (mergeR p a b) := by
  have hd : DifferentiableAt ℝ (fun a => Φ (mergeR p a b)) a :=
    (hΦ _).comp a ((contDiff_mergeR_left b).differentiable (by simp) a)
  refine fderiv_apply_of_line hd ?_
  simp_rw [mergeR_add_single_left]
  have h2 : HasDerivAt (fun t : ℝ => mergeR p a b + t • Pi.single k.val 1) (Pi.single k.val 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k.val (1 : ℝ))).const_add
      (mergeR p a b)
  exact (hΦ _).hasFDerivAt.comp_hasDerivAt_of_eq 0 h2 (by simp)

theorem IsPer.fiber_left {Φ : (ι → ℝ) → ℝ} (hp : IsPer Φ) (b : SpT p → ℝ) :
    IsPer (fun a => Φ (mergeR p a b)) := fun m a => by
  have : mergeR p (a + intVec m) b =
      mergeR p a b + intVec (fun i => if h : i ≠ p then m ⟨i, h⟩ else 0) := by
    funext i; by_cases h : i ≠ p <;> simp [mergeR, h, intVec]
  simp only [this, hp _ _]

end Fiber

theorem continuous_mergeR {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι) :
    Continuous (fun q : ({i // i ≠ p} → ℝ) × (SpT p → ℝ) => mergeR p q.1 q.2) := by
  refine continuous_pi fun i => ?_
  by_cases h : i ≠ p
  · simp only [mergeR, dif_pos h]; exact (continuous_apply _).comp continuous_fst
  · simp only [mergeR, dif_neg h]; exact (continuous_apply _).comp continuous_snd

theorem measurable_mergeR_secT {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι) :
    Measurable (fun z : UnitAddTorus {i // i ≠ p} × UnitAddTorus (SpT p) =>
      mergeR p (secT z.1) (secT z.2)) :=
  (continuous_mergeR p).measurable.comp
    ((measurable_secT.comp measurable_fst).prodMk (measurable_secT.comp measurable_snd))

/-- The tensorization step: splitting off the coordinate `p`. -/
theorem lsiLift_step {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι)
    (IH : LSILift {i // i ≠ p}) : LSILift ι := by
  intro Φ hΦ hper hpos
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  obtain ⟨xM, xm, hmm⟩ := periodic_max_min hΦ.continuous hper
  have hm0 : 0 < Φ xm := hpos xm
  set μ2 : Measure (UnitAddTorus {i // i ≠ p} × UnitAddTorus (SpT p)) :=
    (volume : Measure (UnitAddTorus {i // i ≠ p})).prod volume with hμ2
  have hmp : MeasurePreserving (splitT p).symm μ2 volume :=
    (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => UnitAddCircle) (fun i => i ≠ p)).symm
  have htrans : ∀ G : UnitAddTorus ι → ℝ, ∫ y, G y = ∫ z, G ((splitT p).symm z) ∂μ2 :=
    fun G => (hmp.integral_comp' G).symm
  have hsplit : ∀ z, secT ((splitT p).symm z) = mergeR p (secT z.1) (secT z.2) := fun z => by
    obtain ⟨a, b⟩ := z; exact secT_split a b
  set F : UnitAddTorus {i // i ≠ p} × UnitAddTorus (SpT p) → ℝ :=
    fun z => Φ (mergeR p (secT z.1) (secT z.2)) ^ 2 with hFdef
  have hFm : Measurable F :=
    (hΦ.continuous.measurable.comp (measurable_mergeR_secT p)).pow_const 2
  have hFc : ∀ z, Φ xm ^ 2 ≤ F z := fun z => pow_le_pow_left₀ hm0.le (hmm _).1 2
  have hFC : ∀ z, F z ≤ Φ xM ^ 2 := fun z => pow_le_pow_left₀ (hpos _).le (hmm _).2 2
  have hent : entR volume (fun y : UnitAddTorus ι => Φ (secT y) ^ 2) = entR μ2 F := by
    unfold entR
    rw [htrans, htrans (fun y => Φ (secT y) ^ 2)]
    simp only [hsplit, hFdef]
  have hP := entR_prod_le (μ := (volume : Measure (UnitAddTorus {i // i ≠ p})))
    (ν := (volume : Measure (UnitAddTorus (SpT p)))) hFm (pow_pos hm0 2) hFc hFC
  -- the gradient pieces
  set gp : UnitAddTorus {i // i ≠ p} × UnitAddTorus (SpT p) → ℝ :=
    fun z => Dk Φ p (mergeR p (secT z.1) (secT z.2)) ^ 2 with hgp
  set gq : UnitAddTorus {i // i ≠ p} × UnitAddTorus (SpT p) → ℝ :=
    fun z => ∑ k : {i // i ≠ p}, Dk Φ k.val (mergeR p (secT z.1) (secT z.2)) ^ 2 with hgq
  have hbdd : ∀ k, ∃ C, ∀ x, |Dk Φ k x| ≤ C := fun k => by
    obtain ⟨C, hC⟩ := periodic_bounded (contDiff_Dk hΦ k).continuous (hper.Dk k)
    exact ⟨C, fun x => by rw [← Real.norm_eq_abs]; exact hC x⟩
  choose CD hCD using hbdd
  have hgpi : Integrable gp μ2 := Integrable.of_bound
    ((((contDiff_Dk hΦ p).continuous.measurable.comp (measurable_mergeR_secT p)).pow_const
      2).aestronglyMeasurable) (CD p ^ 2) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := pow_le_pow_left₀ (abs_nonneg _) (hCD p (mergeR p (secT z.1) (secT z.2))) 2
      rwa [sq_abs] at h)
  have hgqi : Integrable gq μ2 := by
    simp only [hgq]
    refine integrable_finset_sum _ fun k _ => Integrable.of_bound
      ((((contDiff_Dk hΦ k.val).continuous.measurable.comp (measurable_mergeR_secT p)).pow_const
        2).aestronglyMeasurable) (CD k.val ^ 2) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg _) (hCD k.val (mergeR p (secT z.1) (secT z.2))) 2
    rwa [sq_abs] at h
  -- the fibre inequalities
  have h1 : ∀ a, entR volume (fun b => F (a, b)) ≤ 2 / aCos * ∫ b, gp (a, b) := by
    intro a
    have := lsiLift_unique (SpT p) (fun b' => Φ (mergeR p (secT a) b'))
      (hΦ.comp (contDiff_mergeR _)) (hper.fiber _) (fun _ => hpos _)
    simp only [Fintype.sum_unique, Dk_fiber hΦd] at this
    exact this
  have h2 : ∀ b, entR volume (fun a => F (a, b)) ≤ 2 / aCos * ∫ a, gq (a, b) := by
    intro b
    have := IH (fun a' => Φ (mergeR p a' (secT b))) (hΦ.comp (contDiff_mergeR_left _))
      (hper.fiber_left _) (fun _ => hpos _)
    simp only [Dk_fiber_left hΦd] at this
    exact this
  have hI1 : ∫ a, entR volume (fun b => F (a, b)) ≤ 2 / aCos * ∫ z, gp z ∂μ2 := by
    rw [integral_prod gp hgpi, ← integral_const_mul]
    exact integral_mono (integrable_entR_left hFm (pow_pos hm0 2) hFc hFC)
      (hgpi.integral_prod_left.const_mul _) h1
  have hI2 : ∫ b, entR volume (fun a => F (a, b)) ≤ 2 / aCos * ∫ z, gq z ∂μ2 := by
    rw [integral_prod_symm gq hgqi, ← integral_const_mul]
    exact integral_mono (integrable_entR_right hFm (pow_pos hm0 2) hFc hFC)
      (hgqi.integral_prod_right.const_mul _) h2
  have hsum : ∫ y : UnitAddTorus ι, ∑ k, Dk Φ k (secT y) ^ 2 = ∫ z, gp z ∂μ2 + ∫ z, gq z ∂μ2 := by
    rw [htrans, ← integral_add hgpi hgqi]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hsplit, hgp, hgq]
    exact Fintype.sum_eq_add_sum_subtype_ne (fun k => Dk Φ k (mergeR p (secT z.1) (secT z.2)) ^ 2) p
  rw [hent, hsum]
  linarith

theorem lsiLift_all : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    LSILift ι := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ _ hn
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨p⟩⟩
    · exact lsiLift_empty ι
    · refine lsiLift_step p (ih _ ?_ {i // i ≠ p} rfl)
      rw [← hn]
      exact Fintype.card_subtype_lt (p := fun i => i ≠ p) (x := p) (by simp)

/-! ### Lower semicontinuity of `ent` -/

theorem ent_le_liminf {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {F : ℕ → α → ℝ} {f : α → ℝ} (hFi : ∀ n, Integrable (F n) P) (hfi : Integrable f P)
    (hae : ∀ᵐ x ∂P, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hint : Tendsto (fun n => ∫ x, F n x ∂P) atTop (𝓝 (∫ x, f x ∂P))) :
    ent P f ≤ liminf (fun n => ent P (F n)) atTop := by
  unfold ent
  rw [if_pos hfi]
  simp only [if_pos (hFi _)]
  set c := ∫ x, f x ∂P
  by_cases hc : c = 0
  · simp only [hc, zero_mul, ENNReal.ofReal_zero, lintegral_zero]
    exact zero_le
  have hpt : ∀ᵐ x ∂P, Tendsto (fun n => ENNReal.ofReal ((∫ y, F n y ∂P) *
      klFun (F n x / ∫ y, F n y ∂P))) atTop (𝓝 (ENNReal.ofReal (c * klFun (f x / c)))) := by
    filter_upwards [hae] with x hx
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    exact hint.mul ((continuous_klFun.tendsto _).comp (hx.div hint hc))
  calc ∫⁻ x, ENNReal.ofReal (c * klFun (f x / c)) ∂P
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal ((∫ y, F n y ∂P) *
          klFun (F n x / ∫ y, F n y ∂P))) atTop ∂P :=
        lintegral_congr_ae (hpt.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ _ := lintegral_liminf_le' fun n => (ENNReal.measurable_ofReal.comp_aemeasurable
        ((continuous_klFun.comp_aestronglyMeasurable
          ((hFi n).div_const _).aestronglyMeasurable).const_mul _).aemeasurable)

/-- For positive bounded `u`, `ent` is the real entropy. -/
theorem ent_eq_ofReal_entR {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {u : α → ℝ} (hu : Measurable u) {c C : ℝ} (hc : 0 < c) (huc : ∀ x, c ≤ u x)
    (huC : ∀ x, u x ≤ C) : ent P u = ENNReal.ofReal (entR P u) := by
  have hu0 : ∀ x, 0 < u x := fun x => lt_of_lt_of_le hc (huc x)
  have bdd : ∀ {F : α → ℝ}, Measurable F → ∀ B, (∀ x, |F x| ≤ B) → Integrable F P :=
    fun {F} hF B hB => Integrable.of_bound hF.aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hui : Integrable u P := bdd hu (|C| + |c|) fun x => by
    rw [abs_of_pos (hu0 x)]; have := huC x; have := le_abs_self C; have := abs_nonneg c; linarith
  obtain ⟨hmc, hmC⟩ := integral_mem_Icc (ρ := P) hu.aestronglyMeasurable huc huC
  set m := ∫ x, u x ∂P with hmdef
  have hm : 0 < m := lt_of_lt_of_le hc hmc
  have hul : Integrable (fun x => u x * Real.log (u x)) P :=
    bdd (hu.mul (Real.measurable_log.comp hu)) _ fun x => abs_mul_log_le hc (huc x) (huC x)
  unfold ent
  rw [if_pos hui]
  have e : ∀ x, m * klFun (u x / m) = u x * Real.log (u x) - u x * Real.log m - u x + m := fun x => by
    rw [klFun_apply, Real.log_div (hu0 x).ne' hm.ne']; field_simp; ring
  have hnn : ∀ x, 0 ≤ m * klFun (u x / m) := fun x =>
    mul_nonneg hm.le (klFun_nonneg (div_nonneg (hu0 x).le hm.le))
  have hint : Integrable (fun x => m * klFun (u x / m)) P := by
    simp_rw [e]
    exact ((hul.sub (hui.mul_const _)).sub hui).add (integrable_const m)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
  congr 1
  simp_rw [e]
  have i1 : Integrable (fun x => u x * Real.log (u x) - u x * Real.log m - u x) P :=
    (hul.sub (hui.mul_const _)).sub hui
  have i2 : Integrable (fun x => u x * Real.log (u x) - u x * Real.log m) P :=
    hul.sub (hui.mul_const _)
  rw [integral_add (f := fun x => u x * Real.log (u x) - u x * Real.log m - u x)
      (g := fun _ => m) i1 (integrable_const m),
    integral_sub (f := fun x => u x * Real.log (u x) - u x * Real.log m) (g := u) i2 hui,
    integral_sub (f := fun x => u x * Real.log (u x)) (g := fun x => u x * Real.log m) hul
      (hui.mul_const _), integral_mul_const]
  unfold entR
  rw [hmdef]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-! ### The inequality on `H¹(𝕋^ι)` -/

section H1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem integrable_sq_moll (n : ℕ) {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume) :
    Integrable (fun y => moll n u y ^ 2) volume := by
  have hc := (moll_comp_liftT_contDiff n hu).continuous
  have hp := isPer_lift (moll n u)
  have : (fun y => moll n u y ^ 2) = fun y => ((fun x => (moll n u ∘ liftT) x ^ 2) (secT y)) := by
    funext y; show moll n u y ^ 2 = moll n u (liftT (secT y)) ^ 2; rw [liftT_secT]
  rw [this]
  exact integrable_secT (hc.pow 2) (fun m x => by
    show (moll n u ∘ liftT) (x + intVec m) ^ 2 = (moll n u ∘ liftT) x ^ 2; rw [hp m x])

/-- `∫ (moll u)² ≤ ∫ u²`. -/
theorem integral_sq_moll_le (n : ℕ) {u : UnitAddTorus ι → ℝ} (hu : MemLp u 2 volume) :
    ∫ y, moll n u y ^ 2 ≤ ∫ y, u y ^ 2 := by
  have hi : Integrable u volume := hu.integrable one_le_two
  have h := lintegral_moll_sq_le n hi
  simp_rw [← ofReal_sq_eq_enorm_sq] at h
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sq_moll n hi)
      (Eventually.of_forall fun y => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hu.integrable_sq
      (Eventually.of_forall fun y => sq_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun y => sq_nonneg _)).mp h

theorem memLp_weakGrad_comp {h : UnitAddTorus ι → ℝ} (hh : MemH1 volume h) (k : ι) :
    MemLp (fun y => weakGrad h y k) 2 volume :=
  hh.2.2.of_le ((isWeakGrad_weakGrad hh.1).aestronglyMeasurable_grad k)
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ k)

theorem dirichlet_eq_ofReal {h : UnitAddTorus ι → ℝ} (hh : MemH1 volume h) :
    dirichlet volume h = ENNReal.ofReal (∫ y, sqNorm (weakGrad h y)) := by
  unfold dirichlet
  have hi : Integrable (fun y => sqNorm (weakGrad h y)) volume := by
    have := hh.2.2.integrable_sq
    refine this.congr (Eventually.of_forall fun y => ?_)
    exact Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun y => Finset.sum_nonneg fun k _ => sq_nonneg _)]

/-- The inequality for `√((moll_n h)² + ε)`. -/
theorem lsi_moll_step {h : UnitAddTorus ι → ℝ} (hh : MemH1 volume h) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ent volume (fun y => moll n h y ^ 2 + ε) ≤
      ENNReal.ofReal (2 / aCos * ∫ y, sqNorm (weakGrad h y)) := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  have hw := isWeakGrad_weakGrad hh.1
  have hi : Integrable h volume := hh.2.1.integrable one_le_two
  set Φ := moll n h ∘ liftT with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := moll_comp_liftT_contDiff n hi
  have hΦp : IsPer Φ := isPer_lift _
  set Ψ : (ι → ℝ) → ℝ := fun x => Real.sqrt (Φ x ^ 2 + ε) with hΨdef
  have hq0 : ∀ x, 0 < Φ x ^ 2 + ε := fun x => by positivity
  have hΨ : ContDiff ℝ ∞ Ψ := ((hΦ.pow 2).add contDiff_const).sqrt fun x => (hq0 x).ne'
  have hΨp : IsPer Ψ := fun m x => by simp only [hΨdef, hΦp m x]
  have hΨpos : ∀ x, 0 < Ψ x := fun x => Real.sqrt_pos.mpr (hq0 x)
  have hL := lsiLift_all _ ι rfl Ψ hΨ hΨp hΨpos
  -- `Ψ(secT y)² = (moll h)² + ε`
  have hval : ∀ y, Ψ (secT y) ^ 2 = moll n h y ^ 2 + ε := fun y => by
    simp only [hΨdef, hΦdef, Function.comp_apply, liftT_secT]
    rw [Real.sq_sqrt (by positivity)]
  simp_rw [hval] at hL
  -- the gradient
  have hDΨ : ∀ k x, Dk Ψ k x ^ 2 ≤ Dk Φ k x ^ 2 := fun k x => by
    have hq : HasFDerivAt (fun x => Φ x ^ 2 + ε) ((2 * Φ x) • fderiv ℝ Φ x) x := by
      have := ((hΦ.differentiable (by simp) x).hasFDerivAt.pow 2).add_const ε
      convert this using 1
      ext v; simp
    have hs := hq.sqrt (hq0 x).ne'
    have e : Dk Ψ k x = Φ x * Dk Φ k x / Ψ x := by
      rw [Dk, hs.fderiv, Dk]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hΨdef]
      field_simp
    rw [e, div_pow, mul_pow, Real.sq_sqrt (hq0 x).le]
    rw [div_le_iff₀ (hq0 x)]
    nlinarith [sq_nonneg (Dk Φ k x), sq_nonneg (Φ x), hε]
  have hDΦ : ∀ k y, Dk Φ k (secT y) = moll n (fun z => weakGrad h z k) y := fun k y => by
    rw [Dk, hΦdef, moll_comp_liftT]
    exact fderiv_mollL_of_isWeakGrad hw n (secT y) k
  -- integrals
  have hcΨ : Continuous fun x => ∑ k, Dk Ψ k x ^ 2 :=
    continuous_finset_sum _ fun k _ => (contDiff_Dk hΨ k).continuous.pow 2
  have hiΨ := integrable_secT hcΨ (fun m x => by simp only [(hΨp.Dk _) m x])
  have hgk := memLp_weakGrad_comp hh
  have hmi : ∀ k, Integrable (fun y => moll n (fun z => weakGrad h z k) y ^ 2) volume := fun k =>
    integrable_sq_moll n ((hgk k).integrable one_le_two)
  have hgrad : ∫ y, ∑ k, Dk Ψ k (secT y) ^ 2 ≤ ∫ y, sqNorm (weakGrad h y) := by
    calc ∫ y, ∑ k, Dk Ψ k (secT y) ^ 2 ≤ ∫ y, ∑ k, moll n (fun z => weakGrad h z k) y ^ 2 :=
          integral_mono hiΨ (integrable_finset_sum _ fun k _ => hmi k) fun y =>
            Finset.sum_le_sum fun k _ => by rw [← hDΦ]; exact hDΨ k _
      _ = ∑ k, ∫ y, moll n (fun z => weakGrad h z k) y ^ 2 :=
          integral_finset_sum _ fun k _ => hmi k
      _ ≤ ∑ k, ∫ y, weakGrad h y k ^ 2 :=
          Finset.sum_le_sum fun k _ => integral_sq_moll_le n (hgk k)
      _ = ∫ y, sqNorm (weakGrad h y) := by
          rw [← integral_finset_sum _ fun k _ => (hgk k).integrable_sq]; rfl
  -- `ent = entR`
  obtain ⟨B, hB⟩ := periodic_bounded hΦ.continuous hΦp
  have hmb : ∀ y, |moll n h y| ≤ B := fun y => by
    have := hB (secT y); rwa [Real.norm_eq_abs, hΦdef, Function.comp_apply, liftT_secT] at this
  have hmeas : Measurable fun y => moll n h y ^ 2 + ε :=
    ((measurable_moll n hi).pow_const 2).add_const ε
  rw [ent_eq_ofReal_entR (C := B ^ 2 + ε) hmeas hε (fun y => by nlinarith [sq_nonneg (moll n h y)])
    (fun y => by nlinarith [hmb y, abs_nonneg (moll n h y), sq_abs (moll n h y)])]
  exact ENNReal.ofReal_le_ofReal (hL.trans (mul_le_mul_of_nonneg_left hgrad (by positivity)))

/-- **Sharp LSI on `𝕋^ι`**: `Ent_m(h²) ≤ (2/a) ∫ |∇h|² dm` for `h ∈ H¹(m)`. -/
theorem lsi_torus_H1 {h : UnitAddTorus ι → ℝ} (hh : MemH1 volume h) :
    ent volume (fun y => h y ^ 2) ≤ ENNReal.ofReal (2 / aCos) * dirichlet volume h := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  have hi : Integrable h volume := hh.2.1.integrable one_le_two
  set D := ∫ y, sqNorm (weakGrad h y) with hD
  obtain ⟨ns, -, hae⟩ := exists_subseq_ae_of_tendsto_lintegral
    (fun n => (measurable_moll n hi).aestronglyMeasurable) hi.aestronglyMeasurable (tendsto_moll hi)
  set F : ℕ → UnitAddTorus ι → ℝ := fun k y => moll (ns k) h y ^ 2 + 1 / ((k : ℝ) + 1) with hF
  have hFi : ∀ k, Integrable (F k) volume := fun k =>
    (integrable_sq_moll (ns k) hi).add (integrable_const _)
  have hFae : ∀ᵐ y ∂(volume : Measure (UnitAddTorus ι)), Tendsto (fun k => F k y) atTop
      (𝓝 (h y ^ 2)) := by
    filter_upwards [hae] with y hy
    have := (hy.pow 2).add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at this
    exact this
  -- convergence of `∫ (moll h)²`
  have hsq : Tendsto (fun k => ∫ y, moll (ns k) h y ^ 2) atTop (𝓝 (∫ y, h y ^ 2)) := by
    set a : ℕ → ℝ≥0∞ := fun k => ∫⁻ y, ENNReal.ofReal (moll (ns k) h y ^ 2) with ha
    set A : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (h y ^ 2) with hA
    have haA : ∀ k, a k = ENNReal.ofReal (∫ y, moll (ns k) h y ^ 2) := fun k =>
      (ofReal_integral_eq_lintegral_ofReal (integrable_sq_moll (ns k) hi)
        (Eventually.of_forall fun y => sq_nonneg _)).symm
    have hAA : A = ENNReal.ofReal (∫ y, h y ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal hh.2.1.integrable_sq
        (Eventually.of_forall fun y => sq_nonneg _)).symm
    have hup : ∀ k, a k ≤ A := fun k => by
      rw [haA, hAA]; exact ENNReal.ofReal_le_ofReal (integral_sq_moll_le _ hh.2.1)
    have hlow : A ≤ liminf a atTop := by
      calc A = ∫⁻ y, liminf (fun k => ENNReal.ofReal (moll (ns k) h y ^ 2)) atTop :=
            lintegral_congr_ae (hae.mono fun y hy =>
              (((ENNReal.continuous_ofReal.comp (continuous_pow 2)).tendsto _).comp hy).liminf_eq.symm)
        _ ≤ liminf a atTop := lintegral_liminf_le' fun k =>
            (ENNReal.measurable_ofReal.comp ((measurable_moll _ hi).pow_const 2)).aemeasurable
    have hlim : Tendsto a atTop (𝓝 A) :=
      tendsto_of_le_liminf_of_limsup_le hlow (limsup_le_of_le (by isBoundedDefault)
        (Eventually.of_forall hup))
    have hAne : A ≠ ⊤ := by rw [hAA]; exact ENNReal.ofReal_ne_top
    have := (ENNReal.tendsto_toReal hAne).comp hlim
    simp only [Function.comp_def, haA, hAA] at this
    rw [ENNReal.toReal_ofReal (integral_nonneg fun y => sq_nonneg _)] at this
    exact this.congr fun k => ENNReal.toReal_ofReal (integral_nonneg fun y => sq_nonneg _)
  have hint : Tendsto (fun k => ∫ y, F k y) atTop (𝓝 (∫ y, h y ^ 2)) := by
    have := hsq.add tendsto_one_div_add_atTop_nhds_zero_nat
    simp only [add_zero] at this
    refine this.congr fun k => ?_
    simp only [hF]
    rw [integral_add (integrable_sq_moll (ns k) hi) (integrable_const _)]
    simp
  have hle := ent_le_liminf hFi hh.2.1.integrable_sq hFae hint
  have hbd : ∀ k, ent volume (F k) ≤ ENNReal.ofReal (2 / aCos * D) := fun k =>
    lsi_moll_step hh (ns k) (by positivity)
  calc ent volume (fun y => h y ^ 2) ≤ liminf (fun k => ent volume (F k)) atTop := hle
    _ ≤ ENNReal.ofReal (2 / aCos * D) :=
        liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall hbd))
    _ = ENNReal.ofReal (2 / aCos) * dirichlet volume h := by
        rw [dirichlet_eq_ofReal hh, ENNReal.ofReal_mul (by positivity)]

end H1

end SharpLSI
