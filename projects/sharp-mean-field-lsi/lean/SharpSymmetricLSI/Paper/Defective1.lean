import SharpSymmetricLSI.Paper.TorusLSI

/-!
# R03 (Proposition 2.2), part 1: the `η`-defective LSI on `𝕋^ι`

`Ent_m(h²) ≤ (2η/a) ∫ |∇h|² dm + 6 |ι| log(1/η) ∫ h² dm` for every `0 < η ≤ 1` (`elsi_torus_H1`):
on the circle from Lemma 3.2 (R10, `H ≤ 6 log(1 + I/(12a))`) and `log(1+x) ≤ ηx + log(1/η)`; then
tensorization with a mass term (Gross) and mollification, following `TorusLSI` (whose sharp version
is the case without mass term). This replaces the fixed-dimensional Sobolev embedding of the TeX for
the finitely many small `N`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI

/-- `∫₀¹ φ² log φ² - Z log Z ≤ (2ε/a) ∫₀¹ φ'² + 6 log(1/ε) Z`, `Z = ∫₀¹ φ²`, for smooth positive
`1`-periodic `φ` and `0 < ε ≤ 1`. -/
theorem lsiE_interval {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hper : ∀ t, φ (t + 1) = φ t) (hpos : ∀ t, 0 < φ t) :
    (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2 * Real.log (φ t ^ 2)) -
        (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) * Real.log (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) ≤
      2 * ε / aCos * (∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2) +
        6 * Real.log (1 / ε) * ∫ t in Ioc (0 : ℝ) 1, φ t ^ 2 := by
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
  -- `H ≤ ε I/(2a) + 6 log(1/ε)`
  have h310 := aux.2.2.1
  set I := (fisherInfo (densMeasure ρ) (haar 1)).toReal with hIdef
  have hI0 : 0 ≤ I := ENNReal.toReal_nonneg
  have hlog : Real.log (1 + I / (12 * aCos)) ≤ ε * (I / (12 * aCos)) + Real.log (1 / ε) := by
    have hx : 0 ≤ I / (12 * aCos) := div_nonneg hI0 (by positivity)
    have h1 : 1 + I / (12 * aCos) ≤ (1 + ε * (I / (12 * aCos))) / ε := by
      rw [le_div_iff₀ hε0]; nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div (by positivity) hε0.ne'] at h2
    have h3 := Real.log_le_sub_one_of_pos (show 0 < 1 + ε * (I / (12 * aCos)) by positivity)
    rw [one_div, Real.log_inv]
    linarith
  have hH : (klDiv (densMeasure ρ) (haar 1)).toReal ≤ ε * I / (2 * aCos) + 6 * Real.log (1 / ε) := by
    have := h310.trans (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 6))
    have e : 6 * (ε * (I / (12 * aCos)) + Real.log (1 / ε)) =
        ε * I / (2 * aCos) + 6 * Real.log (1 / ε) := by field_simp; ring
    linarith
  rw [hkl, hfi] at hH
  have := mul_le_mul_of_nonneg_left hH hZ0.le
  rw [mul_div_cancel₀ _ hZ0.ne'] at this
  have h4 : Z * (ε * (4 / Z * ∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2) / (2 * aCos) +
      6 * Real.log (1 / ε)) = 2 * ε / aCos * (∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2) +
        6 * Real.log (1 / ε) * Z := by field_simp; ring
  rw [h4] at this
  exact this

/-! ### The smooth positive inequality on `𝕋^ι` -/

/-- The `ε`-defective smooth-positive LSI on `𝕋^ι`, at the level of periodic lifts. -/
def ELSILift (ι : Type) [Fintype ι] [DecidableEq ι] (ε β : ℝ) : Prop :=
  ∀ Φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ Φ → IsPer Φ → (∀ x, 0 < Φ x) →
    entR volume (fun y : UnitAddTorus ι => Φ (secT y) ^ 2) ≤
      2 * ε / aCos * (∫ y : UnitAddTorus ι, ∑ k, Dk Φ k (secT y) ^ 2) +
        β * ∫ y : UnitAddTorus ι, Φ (secT y) ^ 2

theorem elsiLift_mono {ι : Type} [Fintype ι] [DecidableEq ι] {ε β β' : ℝ} (hββ : β ≤ β')
    (h : ELSILift ι ε β) : ELSILift ι ε β' := by
  intro Φ hΦ hper hpos
  refine (h Φ hΦ hper hpos).trans ?_
  have : 0 ≤ ∫ y : UnitAddTorus ι, Φ (secT y) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

theorem elsiLift_empty (ι : Type) [Fintype ι] [DecidableEq ι] [IsEmpty ι] {ε : ℝ} (hε : 0 ≤ ε) :
    ELSILift ι ε 0 := by
  intro Φ _ _ _
  have ha0 : 0 < aCos := by unfold aCos; positivity
  have hu : ∀ F : UnitAddTorus ι → ℝ, ∫ y, F y = F default := fun F => by
    rw [MeasureTheory.integral_unique]; simp only [probReal_univ, one_smul]
    exact congrArg F (Subsingleton.elim _ _)
  have h0 : entR volume (fun y : UnitAddTorus ι => Φ (secT y) ^ 2) = 0 := by
    unfold entR
    rw [hu, hu]
    simp
  rw [h0, zero_mul, add_zero]
  exact mul_nonneg (by positivity)
    (integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem elsiLift_unique (ι : Type) [inst : Fintype ι] [DecidableEq ι] [Unique ι] {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ELSILift ι ε (6 * Real.log (1 / ε)) := by
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
  have hΦs : ∀ y : UnitAddTorus ι, Φ (secT y) = φ (secT y default) := fun y => by
    conv_lhs => rw [hsec y]
  have hlhs : entR volume (fun y : UnitAddTorus ι => Φ (secT y) ^ 2) =
      (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2 * Real.log (φ t ^ 2)) -
        (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) * Real.log (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) := by
    unfold entR
    simp_rw [hΦs]
    rw [integral_unique_secT (ι := ι) (fun t => φ t ^ 2 * Real.log (φ t ^ 2)),
      integral_unique_secT (ι := ι) (fun t => φ t ^ 2)]
  have hmass : ∫ y : UnitAddTorus ι, Φ (secT y) ^ 2 = ∫ t in Ioc (0 : ℝ) 1, φ t ^ 2 := by
    simp_rw [hΦs]
    exact integral_unique_secT (ι := ι) (fun t => φ t ^ 2)
  have hrhs : ∫ y : UnitAddTorus ι, ∑ k, Dk Φ k (secT y) ^ 2 =
      ∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2 := by
    simp_rw [Fintype.sum_unique]
    have : ∀ y : UnitAddTorus ι, Dk Φ default (secT y) ^ 2 = deriv φ (secT y default) ^ 2 :=
      fun y => by rw [hD _ (hsec y)]
    simp_rw [this]
    exact integral_unique_secT (ι := ι) (fun t => deriv φ t ^ 2)
  rw [hlhs, hrhs, hmass]
  exact lsiE_interval hε0 hε1 hφ hφper hφpos

/-- The tensorization step: splitting off the coordinate `p`. -/
theorem elsiLift_step {ι : Type} [Fintype ι] [DecidableEq ι] {ε β' : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (p : ι) (IH : ELSILift {i // i ≠ p} ε β') :
    ELSILift ι ε (6 * Real.log (1 / ε) + β') := by
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
  have hFi : Integrable F μ2 := Integrable.of_bound hFm.aestronglyMeasurable (Φ xM ^ 2)
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hFC z)
  set L := 6 * Real.log (1 / ε)
  have h1 : ∀ a, entR volume (fun b => F (a, b)) ≤
      2 * ε / aCos * (∫ b, gp (a, b)) + L * ∫ b, F (a, b) := by
    intro a
    have := elsiLift_unique (SpT p) hε0 hε1 (fun b' => Φ (mergeR p (secT a) b'))
      (hΦ.comp (contDiff_mergeR _)) (hper.fiber _) (fun _ => hpos _)
    simp only [Fintype.sum_unique, Dk_fiber hΦd] at this
    exact this
  have h2 : ∀ b, entR volume (fun a => F (a, b)) ≤
      2 * ε / aCos * (∫ a, gq (a, b)) + β' * ∫ a, F (a, b) := by
    intro b
    have := IH (fun a' => Φ (mergeR p a' (secT b))) (hΦ.comp (contDiff_mergeR_left _))
      (hper.fiber_left _) (fun _ => hpos _)
    simp only [Dk_fiber_left hΦd] at this
    exact this
  have hI1 : ∫ a, entR volume (fun b => F (a, b)) ≤
      2 * ε / aCos * (∫ z, gp z ∂μ2) + L * ∫ z, F z ∂μ2 := by
    rw [integral_prod gp hgpi, integral_prod F hFi, ← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hgpi.integral_prod_left).const_mul _) ((hFi.integral_prod_left).const_mul _)]
    exact integral_mono (integrable_entR_left hFm (pow_pos hm0 2) hFc hFC)
      (((hgpi.integral_prod_left).const_mul _).add ((hFi.integral_prod_left).const_mul _)) h1
  have hI2 : ∫ b, entR volume (fun a => F (a, b)) ≤
      2 * ε / aCos * (∫ z, gq z ∂μ2) + β' * ∫ z, F z ∂μ2 := by
    rw [integral_prod_symm gq hgqi, integral_prod_symm F hFi, ← integral_const_mul,
      ← integral_const_mul,
      ← integral_add ((hgqi.integral_prod_right).const_mul _) ((hFi.integral_prod_right).const_mul _)]
    exact integral_mono (integrable_entR_right hFm (pow_pos hm0 2) hFc hFC)
      (((hgqi.integral_prod_right).const_mul _).add ((hFi.integral_prod_right).const_mul _)) h2
  have hsum : ∫ y : UnitAddTorus ι, ∑ k, Dk Φ k (secT y) ^ 2 = ∫ z, gp z ∂μ2 + ∫ z, gq z ∂μ2 := by
    rw [htrans, ← integral_add hgpi hgqi]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hsplit, hgp, hgq]
    exact Fintype.sum_eq_add_sum_subtype_ne (fun k => Dk Φ k (mergeR p (secT z.1) (secT z.2)) ^ 2) p
  have hmass : ∫ y : UnitAddTorus ι, Φ (secT y) ^ 2 = ∫ z, F z ∂μ2 := by
    rw [htrans]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only [hsplit, hFdef])
  rw [hent, hsum, hmass]
  nlinarith

theorem elsiLift_all {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
      ELSILift ι ε (n * (6 * Real.log (1 / ε))) := by
  have hL : 0 ≤ 6 * Real.log (1 / ε) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith))
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ _ hn
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨p⟩⟩
    · have : n = 0 := by rw [← hn]; exact Fintype.card_eq_zero
      subst this
      simpa using elsiLift_empty ι hε0.le
    · have hc : Fintype.card {i // i ≠ p} = n - 1 := by
        rw [← hn]; simp [Fintype.card_subtype_compl]
      have hlt : n - 1 < n := by
        have : 0 < n := by rw [← hn]; exact Fintype.card_pos_iff.mpr ⟨p⟩
        omega
      have h1 : 1 ≤ n := by
        have : 0 < n := by rw [← hn]; exact Fintype.card_pos_iff.mpr ⟨p⟩
        omega
      refine elsiLift_mono (le_of_eq ?_) (elsiLift_step hε0 hε1 p (ih _ hlt {i // i ≠ p} hc))
      rw [Nat.cast_sub h1]
      ring

section H1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The `η`-defective inequality for `√((moll_n h)² + ε)`. -/
theorem elsi_moll_step {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {h : UnitAddTorus ι → ℝ}
    (hh : MemH1 volume h) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ent volume (fun y => moll n h y ^ 2 + ε) ≤
      ENNReal.ofReal (2 * η / aCos * (∫ y, sqNorm (weakGrad h y)) +
        (Fintype.card ι * (6 * Real.log (1 / η))) * ((∫ y, h y ^ 2) + ε)) := by
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
  have hL := elsiLift_all hη0 hη1 _ ι rfl Ψ hΨ hΨp hΨpos
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
  have hβ : 0 ≤ (Fintype.card ι : ℝ) * (6 * Real.log (1 / η)) :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)))
  have hmass : ∫ y, (moll n h y ^ 2 + ε) ≤ (∫ y, h y ^ 2) + ε := by
    rw [integral_add (integrable_sq_moll n hi) (integrable_const ε)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith [integral_sq_moll_le n hh.2.1]
  refine ENNReal.ofReal_le_ofReal (hL.trans ?_)
  have := mul_le_mul_of_nonneg_left hgrad (show 0 ≤ 2 * η / aCos by positivity)
  have := mul_le_mul_of_nonneg_left hmass hβ
  linarith

/-- **`η`-defective LSI on `𝕋^ι`**:
`Ent_m(h²) ≤ (2η/a) ∫ |∇h|² dm + 6 |ι| log(1/η) ∫ h² dm` for `h ∈ H¹(m)`, `0 < η ≤ 1`. -/
theorem elsi_torus_H1 {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {h : UnitAddTorus ι → ℝ}
    (hh : MemH1 volume h) :
    ent volume (fun y => h y ^ 2) ≤ ENNReal.ofReal (2 * η / aCos) * dirichlet volume h +
      ENNReal.ofReal (Fintype.card ι * (6 * Real.log (1 / η))) *
        ∫⁻ y, ENNReal.ofReal (h y ^ 2) := by
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
  set β := (Fintype.card ι : ℝ) * (6 * Real.log (1 / η))
  have hβ : 0 ≤ β := mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (by norm_num) (Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)))
  set b : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (2 * η / aCos * D + β * ((∫ y, h y ^ 2) + 1 / ((k : ℝ) + 1)))
  have hbd : ∀ k, ent volume (F k) ≤ b k := fun k => elsi_moll_step hη0 hη1 hh (ns k) (by positivity)
  have hb : Tendsto b atTop (𝓝 (ENNReal.ofReal (2 * η / aCos * D + β * ∫ y, h y ^ 2))) := by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    have := (tendsto_const_nhds (x := 2 * η / aCos * D)).add ((tendsto_const_nhds (x := β)).mul
      ((tendsto_const_nhds (x := ∫ y, h y ^ 2)).add tendsto_one_div_add_atTop_nhds_zero_nat))
    simpa using this
  have hD0 : 0 ≤ D := integral_nonneg fun y => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ent volume (fun y => h y ^ 2) ≤ liminf (fun k => ent volume (F k)) atTop := hle
    _ ≤ liminf b atTop := liminf_le_liminf (Eventually.of_forall hbd)
    _ = ENNReal.ofReal (2 * η / aCos * D + β * ∫ y, h y ^ 2) := hb.liminf_eq
    _ = ENNReal.ofReal (2 * η / aCos) * dirichlet volume h +
        ENNReal.ofReal β * ∫⁻ y, ENNReal.ofReal (h y ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hβ (integral_nonneg fun y => sq_nonneg _)),
          dirichlet_eq_ofReal hh, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hβ,
          ofReal_integral_eq_lintegral_ofReal hh.2.1.integrable_sq
            (Eventually.of_forall fun y => sq_nonneg _)]
end H1

end SharpLSI
