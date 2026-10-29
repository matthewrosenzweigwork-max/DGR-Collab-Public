-- Ported-from: SharpSymmetricLSI.Paper.TorusLSI @ d880f61501024eacf8cdb0c6a7de5c821c02d412
import SharpSymmetricLSI.Paper.TorusLSI

/-!
# Tensorization of the logarithmic Sobolev inequality at an abstract one-site rate

Generalization of the legacy `SharpSymmetricLSI.Paper.TorusLSI` argument (Gross' tensorization by
induction on the number of coordinates, subadditivity of entropy on products, passage to `H¹` by
mollification, regularization `√(Φ² + ε)` and Fatou) from the fixed circle constant `a = 4π²`
(`SharpLSI.aCos`) to an arbitrary rate `r`: the one-site input is the interval form `CircleLSI r`
of the circle inequality for smooth positive periodic functions. All auxiliary lemmas that do not
involve the rate are imported from the legacy module in place.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace DGPS.Ported.TorusLSI

open SharpLSI

/-- The one-site (circle) inequality at rate `r`, for smooth positive `1`-periodic `φ`:
`∫₀¹ φ² log φ² - Z log Z ≤ (2/a) ∫₀¹ φ'²`, `Z = ∫₀¹ φ²`. -/
def CircleLSI (r : ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → (∀ t, φ (t + 1) = φ t) → (∀ t, 0 < φ t) →
    (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2 * Real.log (φ t ^ 2)) -
        (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) * Real.log (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) ≤
      2 / r * ∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2

/-! ### The smooth positive inequality on `𝕋^ι` -/

/-- The smooth-positive LSI on `𝕋^ι`, at the level of periodic lifts. -/
def LSILiftAt (r : ℝ) (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ Φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ Φ → IsPer Φ → (∀ x, 0 < Φ x) →
    entR volume (fun y : UnitAddTorus ι => Φ (secT y) ^ 2) ≤
      2 / r * ∫ y : UnitAddTorus ι, ∑ k, Dk Φ k (secT y) ^ 2

theorem lsiLiftAt_empty (r : ℝ) (ι : Type) [Fintype ι] [DecidableEq ι] [IsEmpty ι] :
    LSILiftAt r ι := by
  intro Φ _ _ _
  have hu : ∀ F : UnitAddTorus ι → ℝ, ∫ y, F y = F default := fun F => by
    rw [MeasureTheory.integral_unique]; simp only [probReal_univ, one_smul]
    exact congrArg F (Subsingleton.elim _ _)
  unfold entR
  rw [hu, hu, hu]
  simp

theorem lsiLiftAt_unique {r : ℝ} (hc : CircleLSI r) (ι : Type) [inst : Fintype ι] [DecidableEq ι]
    [Unique ι] : LSILiftAt r ι := by
  have h := Subsingleton.elim inst (@Unique.fintype ι _)
  subst h
  intro Φ hΦ hper hpos
  set c : ℝ → (ι → ℝ) := fun t _ => t with hcdef
  have hcc : ContDiff ℝ ∞ c := contDiff_pi.2 fun _ => contDiff_id
  set φ : ℝ → ℝ := fun t => Φ (c t) with hφdef
  have hφ : ContDiff ℝ ∞ φ := hΦ.comp hcc
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
  exact hc φ hφ hφper hφpos


/-- The tensorization step: splitting off the coordinate `p`. -/
theorem lsiLiftAt_step {r : ℝ} (hc : CircleLSI r) {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι)
    (IH : LSILiftAt r {i // i ≠ p}) : LSILiftAt r ι := by
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
    refine MeasureTheory.integrable_finsetSum _ fun k _ => Integrable.of_bound
      ((((contDiff_Dk hΦ k.val).continuous.measurable.comp (measurable_mergeR_secT p)).pow_const
        2).aestronglyMeasurable) (CD k.val ^ 2) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg _) (hCD k.val (mergeR p (secT z.1) (secT z.2))) 2
    rwa [sq_abs] at h
  -- the fibre inequalities
  have h1 : ∀ a, entR volume (fun b => F (a, b)) ≤ 2 / r * ∫ b, gp (a, b) := by
    intro a
    have := lsiLiftAt_unique hc (SpT p) (fun b' => Φ (mergeR p (secT a) b'))
      (hΦ.comp (contDiff_mergeR _)) (hper.fiber _) (fun _ => hpos _)
    simp only [Fintype.sum_unique, Dk_fiber hΦd] at this
    exact this
  have h2 : ∀ b, entR volume (fun a => F (a, b)) ≤ 2 / r * ∫ a, gq (a, b) := by
    intro b
    have := IH (fun a' => Φ (mergeR p a' (secT b))) (hΦ.comp (contDiff_mergeR_left _))
      (hper.fiber_left _) (fun _ => hpos _)
    simp only [Dk_fiber_left hΦd] at this
    exact this
  have hI1 : ∫ a, entR volume (fun b => F (a, b)) ≤ 2 / r * ∫ z, gp z ∂μ2 := by
    rw [integral_prod gp hgpi, ← integral_const_mul]
    exact integral_mono (integrable_entR_left hFm (pow_pos hm0 2) hFc hFC)
      (hgpi.integral_prod_left.const_mul _) h1
  have hI2 : ∫ b, entR volume (fun a => F (a, b)) ≤ 2 / r * ∫ z, gq z ∂μ2 := by
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

theorem lsiLiftAt_all {r : ℝ} (hc : CircleLSI r) : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    LSILiftAt r ι := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ _ hn
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨p⟩⟩
    · exact lsiLiftAt_empty r ι
    · refine lsiLiftAt_step hc p (ih _ ?_ {i // i ≠ p} rfl)
      rw [← hn]
      exact Fintype.card_subtype_lt (p := fun i => i ≠ p) (x := p) (by simp)


section H1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The inequality for `√((moll_n h)² + ε)`. -/
theorem lsi_moll_step {r : ℝ} (hr : 0 < r) (hc : CircleLSI r) {h : UnitAddTorus ι → ℝ} (hh : MemH1 volume h) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ent volume (fun y => moll n h y ^ 2 + ε) ≤
      ENNReal.ofReal (2 / r * ∫ y, sqNorm (weakGrad h y)) := by
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
  have hL := lsiLiftAt_all hc _ ι rfl Ψ hΨ hΨp hΨpos
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
      simp only [smul_apply, smul_eq_mul, hΨdef]
      field_simp
    rw [e, div_pow, mul_pow, Real.sq_sqrt (hq0 x).le]
    rw [div_le_iff₀ (hq0 x)]
    nlinarith [sq_nonneg (Dk Φ k x), sq_nonneg (Φ x), hε]
  have hDΦ : ∀ k y, Dk Φ k (secT y) = moll n (fun z => weakGrad h z k) y := fun k y => by
    rw [Dk, hΦdef, moll_comp_liftT]
    exact fderiv_mollL_of_isWeakGrad hw n (secT y) k
  -- integrals
  have hcΨ : Continuous fun x => ∑ k, Dk Ψ k x ^ 2 :=
    continuous_finsetSum _ fun k _ => (contDiff_Dk hΨ k).continuous.pow 2
  have hiΨ := integrable_secT hcΨ (fun m x => by simp only [(hΨp.Dk _) m x])
  have hgk := memLp_weakGrad_comp hh
  have hmi : ∀ k, Integrable (fun y => moll n (fun z => weakGrad h z k) y ^ 2) volume := fun k =>
    integrable_sq_moll n ((hgk k).integrable one_le_two)
  have hgrad : ∫ y, ∑ k, Dk Ψ k (secT y) ^ 2 ≤ ∫ y, sqNorm (weakGrad h y) := by
    calc ∫ y, ∑ k, Dk Ψ k (secT y) ^ 2 ≤ ∫ y, ∑ k, moll n (fun z => weakGrad h z k) y ^ 2 :=
          integral_mono hiΨ (MeasureTheory.integrable_finsetSum _ fun k _ => hmi k) fun y =>
            Finset.sum_le_sum fun k _ => by rw [← hDΦ]; exact hDΨ k _
      _ = ∑ k, ∫ y, moll n (fun z => weakGrad h z k) y ^ 2 :=
          MeasureTheory.integral_finsetSum _ fun k _ => hmi k
      _ ≤ ∑ k, ∫ y, weakGrad h y k ^ 2 :=
          Finset.sum_le_sum fun k _ => integral_sq_moll_le n (hgk k)
      _ = ∫ y, sqNorm (weakGrad h y) := by
          rw [← MeasureTheory.integral_finsetSum _ fun k _ => (hgk k).integrable_sq]; rfl
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
theorem lsi_torus_H1 {r : ℝ} (hr : 0 < r) (hc : CircleLSI r) {h : UnitAddTorus ι → ℝ} (hh : MemH1 volume h) :
    ent volume (fun y => h y ^ 2) ≤ ENNReal.ofReal (2 / r) * dirichlet volume h := by
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
  have hbd : ∀ k, ent volume (F k) ≤ ENNReal.ofReal (2 / r * D) := fun k =>
    lsi_moll_step hr hc hh (ns k) (by positivity)
  calc ent volume (fun y => h y ^ 2) ≤ liminf (fun k => ent volume (F k)) atTop := hle
    _ ≤ ENNReal.ofReal (2 / r * D) :=
        liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall hbd))
    _ = ENNReal.ofReal (2 / r) * dirichlet volume h := by
        rw [dirichlet_eq_ofReal hh, ENNReal.ofReal_mul (by positivity)]


end H1

end DGPS.Ported.TorusLSI

