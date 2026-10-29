import FullLabeledLSI.Paper.HybridLSIAltB

/-!
# Hybrid tilted log-Sobolev inequality (alternative route), part C: the core inequality on the
# flat Gaussian space

Abstract setting: `X = (𝕋^d)^N` with `P = μ^{⊗N}`, a Gaussian block `ν = gpi M`, a smooth quadratic-like
`u : ℝ^M → ℝ` of temperate growth, `κ > 0`, the tilted measure `Q = ν.withDensity (e^{-u}/κ)`, and
`h(x,g) = √κ e^{u(g)/2} ∑_i c_i Y_i(g) X_i(x)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace SharpLSI.FL.HLA

open SharpLSI

/-! ### Densities -/

section dens
variable {β : Type*} [MeasurableSpace β] {ν : Measure β} {w : β → ℝ}

theorem integrable_wd (hw : Measurable w) (hw0 : ∀ b, 0 ≤ w b) {f : β → ℝ} :
    Integrable f (ν.withDensity fun b => ENNReal.ofReal (w b)) ↔
      Integrable (fun b => w b * f b) ν := by
  rw [integrable_withDensity_iff_integrable_smul' (f := fun b => ENNReal.ofReal (w b))
    (ENNReal.measurable_ofReal.comp hw)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]

theorem integral_wd (hw : Measurable w) (hw0 : ∀ b, 0 ≤ w b) (f : β → ℝ) :
    ∫ b, f b ∂(ν.withDensity fun b => ENNReal.ofReal (w b)) = ∫ b, w b * f b ∂ν := by
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun b => ENNReal.ofReal (w b))
    (ENNReal.measurable_ofReal.comp hw)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]

end dens

theorem integral_le_of_le_nonneg {β : Type*} [MeasurableSpace β] {ν : Measure β} {f g : β → ℝ}
    (hg : Integrable g ν) (hg0 : 0 ≤ g) (h : ∀ b, f b ≤ g b) : ∫ b, f b ∂ν ≤ ∫ b, g b ∂ν := by
  by_cases hf : Integrable f ν
  · exact integral_mono hf hg h
  · rw [integral_undef hf]; exact integral_nonneg hg0

theorem abs_mul_log_le_sq_add_one {s : ℝ} (hs : 0 ≤ s) : |s * Real.log s| ≤ s ^ 2 + 1 := by
  rcases hs.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [abs_le]
    have h1 := Real.log_le_sub_one_of_pos h
    have h2 := Real.one_sub_inv_le_log_of_pos h
    have e1 : s * (1 - s⁻¹) = s - 1 := by field_simp
    have a1 := mul_le_mul_of_nonneg_left h1 hs
    have a2 := mul_le_mul_of_nonneg_left h2 hs
    constructor <;> nlinarith [sq_nonneg (s - 1)]


/-! ### Measurability and integrability on the product -/

section meas
open SharpLSI.FL.Gross
variable {N d M : ℕ} {ι : Type*} [Fintype ι]
  {c : ι → ℝ} {Y : ι → (Fin M → ℝ) → ℝ} {Xj : ι → Config N d → ℝ} {u : (Fin M → ℝ) → ℝ} {κ : ℝ}
  (hY : ∀ i, (Y i).HasTemperateGrowth) (hu : u.HasTemperateGrowth) (hX : ∀ i, C1C (Xj i))

omit hu in
include hY hX in
theorem meas_aF : Measurable (fun z : Config N d × (Fin M → ℝ) => aF c Y Xj z.1 z.2) := by
  unfold aF
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_const.mul ((hY i).1.continuous.measurable.comp measurable_snd)).mul
    ((hX i).measurable.comp measurable_fst)

include hu in
theorem meas_sF : Measurable (sF u κ) := by
  unfold sF
  exact measurable_const.mul (hu.1.continuous.div_const 2 |>.rexp).measurable

include hY hu hX in
theorem meas_hh : Measurable (fun z : Config N d × (Fin M → ℝ) => hh c Y Xj u κ z.1 z.2) := by
  have : (fun z : Config N d × (Fin M → ℝ) => hh c Y Xj u κ z.1 z.2) =
      fun z => sF u κ z.2 * aF c Y Xj z.1 z.2 := funext fun z => hh_eq z.1 z.2
  rw [this]
  exact ((meas_sF (κ := κ) hu).comp measurable_snd).mul (meas_aF hY hX)

omit hu in
include hY hX in
theorem meas_daF (k : Fin M) :
    Measurable (fun z : Config N d × (Fin M → ℝ) => daF c Y Xj z.1 z.2 k) := by
  unfold daF
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_const.mul ((hX i).measurable.comp measurable_fst)).mul
    ((((hY i).1.continuous_fderiv (by simp)).clm_apply continuous_const).measurable.comp
      measurable_snd)

include hu in
theorem meas_duF (k : Fin M) : Measurable (fun g : Fin M → ℝ => duF u g k) :=
  ((hu.1.continuous_fderiv (by simp)).clm_apply continuous_const).measurable

include hY hu hX in
theorem meas_Ey0 (lam' : Fin M → ℝ) :
    Measurable (fun z : Config N d × (Fin M → ℝ) => Ey0 c Y Xj u lam' z.1 z.2) := by
  unfold Ey0
  refine Finset.measurable_sum _ fun k _ => ?_
  refine measurable_const.mul (Measurable.pow_const ?_ 2)
  exact (meas_daF hY hX k).add (((meas_aF hY hX).mul ((meas_duF hu k).comp measurable_snd)).div_const 2)

omit hu in
include hY hX in
theorem meas_Ex0 : Measurable (fun z : Config N d × (Fin M → ℝ) => Ex0 c Y Xj z.1 z.2) := by
  unfold Ex0
  refine Finset.measurable_sum _ fun p _ => Measurable.pow_const ?_ 2
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_const.mul ((hY i).1.continuous.measurable.comp measurable_snd)).mul
    (((hX i).dT_measurable p).comp (measurable_flat.comp measurable_fst))


theorem integrable_prod_PBu {α : Type*} [MeasurableSpace α] {M : ℕ} {P : Measure α}
    [IsFiniteMeasure P] {f : α → (Fin M → ℝ) → ℝ}
    (hm : AEStronglyMeasurable (fun z : α × (Fin M → ℝ) => f z.1 z.2) (P.prod (gpi M)))
    (hf : PBu f) : Integrable (fun z : α × (Fin M → ℝ) => f z.1 z.2) (P.prod (gpi M)) := by
  obtain ⟨k, C, hC, h⟩ := hf
  refine Integrable.mono' (((integrable_one_add_norm_pow M k).const_mul C).comp_snd P) hm
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]; exact h z.1 z.2

theorem integrable_slice_PBu {α : Type*} {M : ℕ} {f : α → (Fin M → ℝ) → ℝ}
    (hm : ∀ x, AEStronglyMeasurable (f x) (gpi M)) (hf : PBu f) (x : α) :
    Integrable (f x) (gpi M) := by
  obtain ⟨k, C, hC, h⟩ := hf
  exact integrable_of_poly (hm x) C k (h x)

end meas

/-! ### The tilted Gaussian measure and the integrability of the entropy integrands -/

variable {N d M : ℕ} {ι : Type*} [Fintype ι]
  {c : ι → ℝ} {Y : ι → (Fin M → ℝ) → ℝ} {Xj : ι → Config N d → ℝ} {u : (Fin M → ℝ) → ℝ} {κ : ℝ}

/-- The tilted Gaussian `e^{-u}/κ dγ_M`. -/
def tPt (u : (Fin M → ℝ) → ℝ) (κ : ℝ) : Measure (Fin M → ℝ) :=
  (gpi M).withDensity fun g => ENNReal.ofReal (wd u κ g)

theorem measurable_wd (hu : u.HasTemperateGrowth) (κ : ℝ) : Measurable (wd u κ) := by
  unfold wd
  exact (hu.1.continuous.neg.rexp.div_const κ).measurable

section integ
open SharpLSI.FL.Gross
variable (hY : ∀ i, (Y i).HasTemperateGrowth) (hu : u.HasTemperateGrowth) (hX : ∀ i, C1C (Xj i))
  (hκ : 0 < κ) {mu : Measure (Torus d)} [IsProbabilityMeasure mu]

omit hY hX hκ in
include hu in
/-- Product measure with the tilted Gaussian is a density over the product with the Gaussian. -/
theorem prod_tPt_eq (P : Measure (Config N d)) [SFinite P] :
    P.prod (tPt u κ) = (P.prod (gpi M)).withDensity
      (fun z => ENNReal.ofReal (wd u κ z.2)) := by
  unfold tPt
  rw [prod_withDensity_right]
  exact ENNReal.measurable_ofReal.comp (measurable_wd hu κ)

omit hκ in
include hY hu hX in
/-- `a² (log κ + u + log a²)` is integrable. -/
theorem integrable_entropy_density (P : Measure (Config N d)) [IsFiniteMeasure P] :
    Integrable (fun z : Config N d × (Fin M → ℝ) =>
      aF c Y Xj z.1 z.2 ^ 2 * (Real.log κ + u z.2 + Real.log (aF c Y Xj z.1 z.2 ^ 2)))
      (P.prod (gpi M)) := by
  have hma := meas_aF (c := c) hY hX
  have h1 : PBu (fun (x : Config N d) g => aF c Y Xj x g ^ 2 * (Real.log κ + u g)) :=
    ((pbu_aF hY hX).sq).mul ((PBu.const (Real.log κ)).add (PBu.of_tg hu))
  have h2 : PBu (fun (x : Config N d) (g : Fin M → ℝ) => (aF c Y Xj x g ^ 2) ^ 2 + 1) :=
    ((pbu_aF hY hX).sq.sq).add (PBu.const 1)
  have i1 := integrable_prod_PBu (P := P) (f := fun x g => aF c Y Xj x g ^ 2 * (Real.log κ + u g))
    (((hma.pow_const 2).mul ((measurable_const.add (hu.1.continuous.measurable.comp measurable_snd))))
      |>.aestronglyMeasurable) h1
  have i2 : Integrable (fun z : Config N d × (Fin M → ℝ) =>
      aF c Y Xj z.1 z.2 ^ 2 * Real.log (aF c Y Xj z.1 z.2 ^ 2)) (P.prod (gpi M)) := by
    have hi := integrable_prod_PBu (P := P) (f := fun x g => (aF c Y Xj x g ^ 2) ^ 2 + 1)
      (((hma.pow_const 2).pow_const 2).add_const 1 |>.aestronglyMeasurable) h2
    refine hi.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact (Real.continuous_mul_log.measurable.comp (hma.pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact abs_mul_log_le_sq_add_one (sq_nonneg _)
  refine (i1.add i2).congr (Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]; ring


omit hκ in
include hY hu hX in
/-- Slice version of `integrable_entropy_density`. -/
theorem integrable_entropy_slice (x : Config N d) :
    Integrable (fun g : Fin M → ℝ =>
      aF c Y Xj x g ^ 2 * (Real.log κ + u g + Real.log (aF c Y Xj x g ^ 2))) (gpi M) := by
  have hma : Measurable (fun g : Fin M → ℝ => aF c Y Xj x g) :=
    (meas_aF hY hX).comp (measurable_prodMk_left (x := x))
  have h1 : PBu (fun (x : Config N d) g => aF c Y Xj x g ^ 2 * (Real.log κ + u g)) :=
    ((pbu_aF hY hX).sq).mul ((PBu.const (Real.log κ)).add (PBu.of_tg hu))
  have h2 : PBu (fun (x : Config N d) (g : Fin M → ℝ) => (aF c Y Xj x g ^ 2) ^ 2 + 1) :=
    ((pbu_aF hY hX).sq.sq).add (PBu.const 1)
  have i1 := integrable_slice_PBu (f := fun x g => aF c Y Xj x g ^ 2 * (Real.log κ + u g))
    (fun x => ((((meas_aF hY hX).comp (measurable_prodMk_left (x := x))).pow_const 2).mul
      (measurable_const.add hu.1.continuous.measurable)).aestronglyMeasurable) h1 x
  have i2 : Integrable (fun g : Fin M → ℝ =>
      aF c Y Xj x g ^ 2 * Real.log (aF c Y Xj x g ^ 2)) (gpi M) := by
    have hi := integrable_slice_PBu (f := fun x g => (aF c Y Xj x g ^ 2) ^ 2 + 1)
      (fun x => ((((meas_aF hY hX).comp (measurable_prodMk_left (x := x))).pow_const 2).pow_const 2
        |>.add_const 1).aestronglyMeasurable) h2 x
    refine hi.mono' ?_ (Eventually.of_forall fun g => ?_)
    · exact (Real.continuous_mul_log.measurable.comp (hma.pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact abs_mul_log_le_sq_add_one (sq_nonneg _)
  refine (i1.add i2).congr (Eventually.of_forall fun g => ?_)
  simp only [Pi.add_apply]; ring

theorem contDiff_hh_slice (hY : ∀ i, (Y i).HasTemperateGrowth) (hu : u.HasTemperateGrowth)
    (x : Config N d) : ContDiff ℝ ∞ (fun g => hh c Y Xj u κ x g) := by
  have : (fun g => hh c Y Xj u κ x g) = fun g => sF u κ g * aF c Y Xj x g :=
    funext fun g => hh_eq x g
  rw [this]
  refine ContDiff.mul (contDiff_const.mul (hu.1.div_const 2).exp) ?_
  exact ContDiff.sum fun i _ => (contDiff_const.mul (hY i).1).mul contDiff_const


section ylice
variable (lam' : Fin M → ℝ) (hl0 : ∀ k, 0 ≤ lam' k) {ρ : ℝ} (hρ : 0 ≤ ρ)

/-- The Gaussian energy integrand. -/
def Eyy (f : (Fin M → ℝ) → ℝ) (g : Fin M → ℝ) : ℝ :=
  ∑ k, lam' k * fderiv ℝ f g (Pi.single k 1) ^ 2

theorem Eyy_nonneg (hl0 : ∀ k, 0 ≤ lam' k) (f : (Fin M → ℝ) → ℝ) (g : Fin M → ℝ) :
    0 ≤ Eyy lam' f g :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hl0 k) (sq_nonneg _)

theorem real_of_ofReal_le {p e I : ℝ} (hp : 0 ≤ p) (hI : 0 ≤ I)
    (h : ENNReal.ofReal p * ENNReal.ofReal e ≤ ENNReal.ofReal I) : p * e ≤ I := by
  rw [← ENNReal.ofReal_mul hp] at h
  exact (ENNReal.ofReal_le_ofReal_iff hI).1 h

omit hl0 hρ hY hX in
include hu hκ in
theorem Q_integrable_iff {f : (Fin M → ℝ) → ℝ} :
    Integrable f (tPt u κ) ↔ Integrable (fun g => wd u κ g * f g) (gpi M) :=
  integrable_wd (measurable_wd hu κ) (wd_nonneg hκ)

variable [hPt : IsProbabilityMeasure (tPt u κ)]
  (hgl : ∀ f : (Fin M → ℝ) → ℝ, ContDiff ℝ ∞ f → MemLp f 2 (tPt u κ) →
      Integrable (fun g => Eyy lam' f g) (tPt u κ) →
      ENNReal.ofReal (ρ / 2) * ent (tPt u κ) (fun g => f g ^ 2) ≤
        ENNReal.ofReal (∫ g, Eyy lam' f g ∂tPt u κ))

include hY hu hX hκ hl0 hρ hgl in
/-- The Gaussian-direction inequality for every slice `x`. -/
theorem yslice (x : Config N d) :
    ρ / 2 * entR (tPt u κ) (fun g => hh c Y Xj u κ x g ^ 2) ≤
      ∫ g, Eyy lam' (fun g' => hh c Y Xj u κ x g') g ∂tPt u κ := by
  have hma : Measurable (fun g : Fin M → ℝ => aF c Y Xj x g) :=
    (meas_aF hY hX).comp (measurable_prodMk_left (x := x))
  have hmeas_pb : ∀ x, AEStronglyMeasurable (fun g => aF c Y Xj x g ^ 2) (gpi M) := fun x =>
    (((meas_aF hY hX).comp (measurable_prodMk_left (x := x))).pow_const 2).aestronglyMeasurable
  have hsq1 : Integrable (fun g => hh c Y Xj u κ x g ^ 2) (tPt u κ) := by
    rw [Q_integrable_iff hu hκ]
    have := integrable_slice_PBu (f := fun x g => aF c Y Xj x g ^ 2) hmeas_pb
      ((pbu_aF hY hX).sq) x
    refine this.congr (Eventually.of_forall fun g => ?_)
    simp only
    rw [mul_comm (wd u κ g), hh_sq_mul_wd hκ]
  have hsq2 : Integrable (fun g => hh c Y Xj u κ x g ^ 2 * Real.log (hh c Y Xj u κ x g ^ 2))
      (tPt u κ) := by
    rw [Q_integrable_iff hu hκ]
    refine (integrable_entropy_slice (c := c) hY hu hX (κ := κ) x).congr (Eventually.of_forall fun g => ?_)
    simp only
    rw [mul_comm (wd u κ g), hh_sq_log_mul_wd hκ]
  have hcd := contDiff_hh_slice (c := c) (Y := Y) (Xj := Xj) (κ := κ) hY hu x
  have hL2 : MemLp (fun g => hh c Y Xj u κ x g) 2 (tPt u κ) :=
    (memLp_two_iff_integrable_sq hcd.continuous.aestronglyMeasurable).2 hsq1
  have hE : Integrable (fun g => Eyy lam' (fun g' => hh c Y Xj u κ x g') g) (tPt u κ) := by
    rw [Q_integrable_iff hu hκ]
    have := integrable_slice_PBu (f := fun x g => Ey0 c Y Xj u lam' x g)
      (fun x => ((meas_Ey0 hY hu hX lam').comp (measurable_prodMk_left (x := x))).aestronglyMeasurable)
      (pbu_Ey0 hY hu hX lam') x
    refine this.congr (Eventually.of_forall fun g => ?_)
    simp only
    rw [← wd_mul_energy hY hu hκ lam' x g]
    rfl
  have h1 := hgl _ hcd hL2 hE
  have hent : ent (tPt u κ) (fun g => hh c Y Xj u κ x g ^ 2) =
      ENNReal.ofReal (entR (tPt u κ) (fun g => hh c Y Xj u κ x g ^ 2)) :=
    ent_eq_formula (tPt u κ) _ (fun g => sq_nonneg _) hsq1 hsq2
  rw [hent] at h1
  exact real_of_ofReal_le (by positivity) (integral_nonneg fun g => Eyy_nonneg lam' hl0 _ g) h1


end ylice

section xslice
variable {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {ρ a0 : ℝ}

omit [Fintype ι] in
/-- A real inequality from the torus log-Sobolev inequality. -/
theorem half_mul_le {e J : ℝ} (hρ : 0 ≤ ρ) (hρa : ρ ≤ a0) (hJ : 0 ≤ J) (h : a0 * e ≤ 2 * J) :
    ρ / 2 * e ≤ J := by
  rcases le_total 0 e with he | he
  · nlinarith [mul_le_mul_of_nonneg_right hρa he]
  · nlinarith [mul_nonneg hρ (neg_nonneg.2 he)]

include hX in
theorem xslice (hac : mu ≪ volume) (ha0 : 0 < a0) (hrls : ENNReal.ofReal a0 ≤ rLS mu)
    (hρ : 0 ≤ ρ) (hρa : ρ ≤ a0) (g : Fin M → ℝ) :
    ρ / 2 * entR (Measure.pi fun _ : Fin N => mu) (fun x => hh c Y Xj u κ x g ^ 2) ≤
      ∫ x, gradPair (fun x' => hh c Y Xj u κ x' g) (fun x' => hh c Y Xj u κ x' g) x
        ∂(Measure.pi fun _ : Fin N => mu) :=
  half_mul_le hρ hρa (integral_nonneg fun x => gradPair_nonneg_self _ x)
    (torus_lsi_bdd hac ha0 hrls (C1C_hh hX g))

end xslice

section corelsi
variable {mu : Measure (Torus d)} [IsProbabilityMeasure mu]

omit [Fintype ι] in
theorem prob_prod_eq_withDensity (hu : u.HasTemperateGrowth) :
    (Measure.pi fun _ : Fin N => mu).prod (tPt u κ) =
      ((Measure.pi fun _ : Fin N => mu).prod (gpi M)).withDensity
        (fun z => ENNReal.ofReal (wd u κ z.2)) :=
  prod_tPt_eq hu _

/-- **Core inequality** on the flat Gaussian space. -/
theorem core_lsi
    (hY : ∀ i, (Y i).HasTemperateGrowth) (hu : u.HasTemperateGrowth) (hX : ∀ i, C1C (Xj i))
    (hκ : 0 < κ) (lam' : Fin M → ℝ) (hl0 : ∀ k, 0 ≤ lam' k)
    {ρ a0 : ℝ} (hρ : 0 ≤ ρ) (ha0 : 0 < a0) (hρa : ρ ≤ a0) (hac : mu ≪ volume)
    (hrls : ENNReal.ofReal a0 ≤ rLS mu) [hPt : IsProbabilityMeasure (tPt u κ)]
    (hgl : ∀ f : (Fin M → ℝ) → ℝ, ContDiff ℝ ∞ f → MemLp f 2 (tPt u κ) →
      Integrable (fun g => Eyy lam' f g) (tPt u κ) →
      ENNReal.ofReal (ρ / 2) * ent (tPt u κ) (fun g => f g ^ 2) ≤
        ENNReal.ofReal (∫ g, Eyy lam' f g ∂tPt u κ)) :
    ρ / 2 * (ent ((Measure.pi fun _ : Fin N => mu).prod (tPt u κ))
        (fun z => hh c Y Xj u κ z.1 z.2 ^ 2)).toReal ≤
      ∫ z, gradPair (fun x => hh c Y Xj u κ x z.2) (fun x => hh c Y Xj u κ x z.2) z.1
          ∂((Measure.pi fun _ : Fin N => mu).prod (tPt u κ)) +
      ∫ z, Eyy lam' (fun g => hh c Y Xj u κ z.1 g) z.2
          ∂((Measure.pi fun _ : Fin N => mu).prod (tPt u κ)) := by
  set P : Measure (Config N d) := Measure.pi fun _ : Fin N => mu with hP
  set Q := tPt u κ with hQ
  set Z := P.prod Q with hZ
  have hwm : Measurable fun z : Config N d × (Fin M → ℝ) => wd u κ z.2 :=
    (measurable_wd hu κ).comp measurable_snd
  have hw0 : ∀ z : Config N d × (Fin M → ℝ), 0 ≤ wd u κ z.2 := fun z => wd_nonneg hκ _
  have hZd : Z = (P.prod (gpi M)).withDensity (fun z => ENNReal.ofReal (wd u κ z.2)) :=
    prod_tPt_eq hu P
  have hZint : ∀ f : Config N d × (Fin M → ℝ) → ℝ, Integrable f Z ↔
      Integrable (fun z => wd u κ z.2 * f z) (P.prod (gpi M)) := fun f => by
    rw [hZd]; exact integrable_wd hwm hw0
  -- integrability facts
  have hma := meas_aF (c := c) hY hX
  have I1 : Integrable (fun z : Config N d × (Fin M → ℝ) => hh c Y Xj u κ z.1 z.2 ^ 2) Z := by
    rw [hZint]
    have := integrable_prod_PBu (P := P) (f := fun x g => aF c Y Xj x g ^ 2)
      (hma.pow_const 2).aestronglyMeasurable ((pbu_aF hY hX).sq)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [mul_comm (wd u κ z.2), hh_sq_mul_wd hκ]
  have I2 : Integrable (fun z : Config N d × (Fin M → ℝ) =>
      hh c Y Xj u κ z.1 z.2 ^ 2 * Real.log (hh c Y Xj u κ z.1 z.2 ^ 2)) Z := by
    rw [hZint]
    refine (integrable_entropy_density (c := c) hY hu hX (κ := κ) P).congr
      (Eventually.of_forall fun z => ?_)
    simp only
    rw [mul_comm (wd u κ z.2), hh_sq_log_mul_wd hκ]
  have IEy : Integrable (fun z : Config N d × (Fin M → ℝ) =>
      Eyy lam' (fun g => hh c Y Xj u κ z.1 g) z.2) Z := by
    rw [hZint]
    have := integrable_prod_PBu (P := P) (f := fun x g => Ey0 c Y Xj u lam' x g)
      (meas_Ey0 hY hu hX lam').aestronglyMeasurable (pbu_Ey0 hY hu hX lam')
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [← wd_mul_energy hY hu hκ lam' z.1 z.2]
    rfl
  have IEx : Integrable (fun z : Config N d × (Fin M → ℝ) =>
      gradPair (fun x => hh c Y Xj u κ x z.2) (fun x => hh c Y Xj u κ x z.2) z.1) Z := by
    rw [hZint]
    have := integrable_prod_PBu (P := P) (f := fun x g => Ex0 c Y Xj x g)
      (meas_Ex0 hY hX).aestronglyMeasurable (pbu_Ex0 hY hX)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [gradPair_hh hX, ← mul_assoc, mul_comm (wd u κ z.2), sF_sq_mul_wd hκ, one_mul]
  -- the entropy subadditivity
  have hS := ent_prod_le (P := P) (Q := Q)
    (g := fun z : Config N d × (Fin M → ℝ) => hh c Y Xj u κ z.1 z.2 ^ 2)
    ((meas_hh hY hu hX).pow_const 2) (fun z => sq_nonneg _) I1 I2
  -- the two slice integrals
  have hA : ρ / 2 * ∫ x, entR Q (fun y => hh c Y Xj u κ x y ^ 2) ∂P ≤
      ∫ z, Eyy lam' (fun g => hh c Y Xj u κ z.1 g) z.2 ∂Z := by
    rw [integral_prod _ IEy, ← integral_const_mul]
    refine integral_le_of_le_nonneg IEy.integral_prod_left
      (fun x => integral_nonneg fun g => Eyy_nonneg lam' hl0 _ g) fun x => ?_
    exact yslice hY hu hX hκ lam' hl0 hρ hgl x
  have hB : ρ / 2 * ∫ g, entR P (fun x => hh c Y Xj u κ x g ^ 2) ∂Q ≤
      ∫ z, gradPair (fun x => hh c Y Xj u κ x z.2) (fun x => hh c Y Xj u κ x z.2) z.1 ∂Z := by
    rw [integral_prod_symm _ IEx, ← integral_const_mul]
    refine integral_le_of_le_nonneg IEx.integral_prod_right
      (fun g => integral_nonneg fun x => gradPair_nonneg_self _ x) fun g => ?_
    exact xslice hX hac ha0 hrls hρ hρa g
  have hent : ent Z (fun z : Config N d × (Fin M → ℝ) => hh c Y Xj u κ z.1 z.2 ^ 2) =
      ENNReal.ofReal (entR Z (fun z : Config N d × (Fin M → ℝ) => hh c Y Xj u κ z.1 z.2 ^ 2)) :=
    ent_eq_formula Z _ (fun z => sq_nonneg _) I1 I2
  have hnn : 0 ≤ ∫ z, gradPair (fun x => hh c Y Xj u κ x z.2) (fun x => hh c Y Xj u κ x z.2) z.1 ∂Z
      + ∫ z, Eyy lam' (fun g => hh c Y Xj u κ z.1 g) z.2 ∂Z :=
    add_nonneg (integral_nonneg fun z => gradPair_nonneg_self _ _)
      (integral_nonneg fun z => Eyy_nonneg lam' hl0 _ _)
  rw [hent, ENNReal.toReal_ofReal']
  rcases le_total 0 (entR Z fun z : Config N d × (Fin M → ℝ) => hh c Y Xj u κ z.1 z.2 ^ 2) with he | he
  · rw [max_eq_left he]
    have : ρ / 2 * entR Z (fun z : Config N d × (Fin M → ℝ) => hh c Y Xj u κ z.1 z.2 ^ 2) ≤
        ρ / 2 * ((∫ x, entR Q (fun y => hh c Y Xj u κ x y ^ 2) ∂P) +
          ∫ g, entR P (fun x => hh c Y Xj u κ x g ^ 2) ∂Q) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    rw [mul_add] at this
    linarith
  · rw [max_eq_right he]; simpa using hnn

end corelsi

end integ

end SharpLSI.FL.HLA

end
