import DGPS.Equilibrium.Hessian

/-!
# Second variation of the free energy (DEF026b)

For interaction data `A`, a probability `μ = q · m` with `0 < c ≤ q ≤ C`, and a bounded measurable
`h` with `∫ h dμ = 0`, the real function `φ(t) = F((1 + t h) μ)` is twice differentiable at `0`
with `φ''(0) = ∫ h² dμ + ∬ W h⊗h dμ²`, which is `⟨h, H_μ h⟩` for the density Hessian `H_μ`.
-/

open MeasureTheory Topology
open scoped ENNReal

namespace DGPS

variable {d : ℕ}

/-- Data of a tilt: a bounded-below density `q` of the base probability and a bounded
perturbation `h` with `∫ h q dm = 0`. -/
structure TiltData (q h : Torus d → ℝ) (c C M : ℝ) : Prop where
  q_meas : Measurable q
  h_meas : Measurable h
  c_pos : 0 < c
  c_le : ∀ x, c ≤ q x
  q_le : ∀ x, q x ≤ C
  h_le : ∀ x, |h x| ≤ M
  int_q : ∫ x, q x ∂(haar d) = 1
  int_qh : ∫ x, q x * h x ∂(haar d) = 0

/-- The tilted density `q (1 + t h)`. -/
noncomputable def tiltDensity (q h : Torus d → ℝ) (t : ℝ) (x : Torus d) : ℝ :=
  q x * (1 + t * h x)

/-- The tilted measure `(1 + t h) q m` (a measure for every `t`). -/
noncomputable def tiltMeasure (q h : Torus d → ℝ) (t : ℝ) : Measure (Torus d) :=
  (haar d).withDensity fun x => ENNReal.ofReal (tiltDensity q h t x)

/-- The radius of the safe interval `|t| < 1 / (2 (M + 1))`, on which `|t h| ≤ 1/2`. -/
noncomputable def tiltRadius (M : ℝ) : ℝ := 1 / (2 * (M + 1))

theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {P : Measure α} [IsFiniteMeasure P]
    {f : α → ℝ} (hf : Measurable f) (B : ℝ) (h : ∀ x, |f x| ≤ B) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ fun x => by simpa using h x)

end DGPS

namespace DGPS.TiltData

variable {d : ℕ}

variable {q h : Torus d → ℝ} {c C M : ℝ} (H : TiltData q h c C M)
include H

theorem M_nonneg : 0 ≤ M :=
  (abs_nonneg _).trans (H.h_le default)

theorem C_pos : 0 < C := H.c_pos.trans_le ((H.c_le default).trans (H.q_le default))

theorem q_pos (x : Torus d) : 0 < q x := H.c_pos.trans_le (H.c_le x)

theorem integrable_q : Integrable q (haar d) :=
  integrable_of_abs_le H.q_meas C fun x => by
    rw [abs_of_pos (H.q_pos x)]; exact H.q_le x

theorem integrable_h : Integrable h (haar d) := integrable_of_abs_le H.h_meas M H.h_le

theorem integrable_qh : Integrable (fun x => q x * h x) (haar d) :=
  integrable_of_abs_le (H.q_meas.mul H.h_meas) (C * M) fun x => by
    rw [abs_mul, abs_of_pos (H.q_pos x)]
    exact mul_le_mul (H.q_le x) (H.h_le x) (abs_nonneg _) H.C_pos.le

theorem tiltRadius_pos : 0 < tiltRadius M := by
  have := H.M_nonneg
  unfold tiltRadius; positivity

theorem abs_mul_le_half {t : ℝ} (ht : |t| < tiltRadius M) (x : Torus d) : |t * h x| ≤ 1 / 2 := by
  have hM := H.M_nonneg
  rw [abs_mul]
  have h1 : |t| * M ≤ tiltRadius M * M := mul_le_mul_of_nonneg_right ht.le hM
  have h2 : tiltRadius M * M ≤ 1 / 2 := by
    unfold tiltRadius
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  exact (mul_le_mul_of_nonneg_left (H.h_le x) (abs_nonneg _)).trans (h1.trans h2)

theorem one_add_mem {t : ℝ} (ht : |t| < tiltRadius M) (x : Torus d) :
    1 / 2 ≤ 1 + t * h x ∧ 1 + t * h x ≤ 3 / 2 := by
  have := abs_le.mp (H.abs_mul_le_half ht x)
  constructor <;> linarith [this.1, this.2]

theorem tiltDensity_bounds {t : ℝ} (ht : |t| < tiltRadius M) (x : Torus d) :
    c / 2 ≤ tiltDensity q h t x ∧ tiltDensity q h t x ≤ 3 * C / 2 := by
  obtain ⟨h1, h2⟩ := H.one_add_mem ht x
  have hq := H.q_pos x
  unfold tiltDensity
  constructor
  · nlinarith [H.c_le x]
  · nlinarith [H.q_le x]

theorem tiltDensity_pos {t : ℝ} (ht : |t| < tiltRadius M) (x : Torus d) :
    0 < tiltDensity q h t x :=
  (half_pos H.c_pos).trans_le (H.tiltDensity_bounds ht x).1

theorem measurable_tiltDensity (t : ℝ) : Measurable (tiltDensity q h t) :=
  H.q_meas.mul (measurable_const.add (measurable_const.mul H.h_meas))

theorem integral_tiltDensity (t : ℝ) : ∫ x, tiltDensity q h t x ∂(haar d) = 1 := by
  have : ∀ x, tiltDensity q h t x = q x + t * (q x * h x) := fun x => by
    unfold tiltDensity; ring
  simp_rw [this]
  rw [integral_add H.integrable_q (H.integrable_qh.const_mul t), integral_const_mul, H.int_q,
    H.int_qh]
  ring

theorem one_add_nonneg {t : ℝ} (ht : |t| * M < 1) (x : Torus d) : 0 ≤ 1 + t * h x := by
  have h1 : |t * h x| ≤ |t| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (H.h_le x) (abs_nonneg _)
  have h3 : -(|t| * M) ≤ t * h x := by linarith [(abs_le.mp h1).1]
  linarith

theorem tiltDensity_nonneg {t : ℝ} (ht : |t| * M < 1) (x : Torus d) :
    0 ≤ tiltDensity q h t x :=
  mul_nonneg (H.q_pos x).le (H.one_add_nonneg ht x)

theorem isProbabilityMeasure_tiltMeasure {t : ℝ} (ht : |t| * M < 1) :
    IsProbabilityMeasure (tiltMeasure q h t) := by
  constructor
  rw [tiltMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [H.integral_tiltDensity]; simp
  · exact integrable_of_abs_le (H.measurable_tiltDensity t) (C * (1 + |t| * M)) fun x => by
      rw [abs_of_nonneg (H.tiltDensity_nonneg ht x)]
      unfold tiltDensity
      have h1 : |t * h x| ≤ |t| * M := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (H.h_le x) (abs_nonneg _)
      have h2 : 1 + t * h x ≤ 1 + |t| * M := by linarith [le_abs_self (t * h x)]
      exact mul_le_mul (H.q_le x) h2 (H.one_add_nonneg ht x) H.C_pos.le
  · exact ae_of_all _ (H.tiltDensity_nonneg ht)

end DGPS.TiltData

namespace DGPS

variable {d : ℕ}

/-! ### Bounded measurable functions and weighted integrals -/

/-- `f` is measurable and bounded. -/
def IsBdd {α : Type*} [MeasurableSpace α] (f : α → ℝ) : Prop :=
  Measurable f ∧ ∃ B, ∀ x, |f x| ≤ B

end DGPS

namespace DGPS.IsBdd

variable {d : ℕ}

variable {α : Type*} [MeasurableSpace α] {f g : α → ℝ}

theorem mul (hf : IsBdd f) (hg : IsBdd g) : IsBdd (fun x => f x * g x) := by
  obtain ⟨hfm, A, hA⟩ := hf
  obtain ⟨hgm, B, hB⟩ := hg
  refine ⟨hfm.mul hgm, A * B, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hA x) (hB x) (abs_nonneg _) ((abs_nonneg _).trans (hA x))

theorem add (hf : IsBdd f) (hg : IsBdd g) : IsBdd (fun x => f x + g x) := by
  obtain ⟨hfm, A, hA⟩ := hf
  obtain ⟨hgm, B, hB⟩ := hg
  exact ⟨hfm.add hgm, A + B, fun x => (abs_add_le _ _).trans (add_le_add (hA x) (hB x))⟩

theorem const (c : ℝ) : IsBdd (fun _ : α => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩

theorem integrable {P : Measure α} [IsFiniteMeasure P] (hf : IsBdd f) : Integrable f P :=
  integrable_of_abs_le hf.1 hf.2.choose hf.2.choose_spec

theorem comp_fst {β : Type*} [MeasurableSpace β] {f : α → ℝ} (hf : IsBdd f) :
    IsBdd (fun p : α × β => f p.1) :=
  ⟨hf.1.comp measurable_fst, hf.2.choose, fun p => hf.2.choose_spec p.1⟩

theorem comp_snd {β : Type*} [MeasurableSpace β] {f : β → ℝ} (hf : IsBdd f) :
    IsBdd (fun p : α × β => f p.2) :=
  ⟨hf.1.comp measurable_snd, hf.2.choose, fun p => hf.2.choose_spec p.2⟩

end DGPS.IsBdd

namespace DGPS

variable {d : ℕ}

theorem integral_withDensity_ofReal {α : Type*} [MeasurableSpace α] {P : Measure α}
    {ρ : α → ℝ} (hρ : Measurable ρ) (hnn : ∀ x, 0 ≤ ρ x) (g : α → ℝ) :
    ∫ x, g x ∂(P.withDensity fun x => ENNReal.ofReal (ρ x)) = ∫ x, ρ x * g x ∂P := by
  have hm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hρ
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [ENNReal.toReal_ofReal (hnn x)]

theorem integral_prod_withDensity_ofReal {α : Type*} [MeasurableSpace α] {P : Measure α}
    [SFinite P] {ρ : α → ℝ} (hρ : Measurable ρ) (hnn : ∀ x, 0 ≤ ρ x) (g : α × α → ℝ) :
    ∫ z, g z ∂((P.withDensity fun x => ENNReal.ofReal (ρ x)).prod
      (P.withDensity fun x => ENNReal.ofReal (ρ x))) = ∫ z, (ρ z.1 * ρ z.2) * g z ∂(P.prod P) := by
  have hm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hρ
  rw [prod_withDensity hm hm]
  have hm2 : Measurable fun z : α × α => ENNReal.ofReal (ρ z.1) * ENNReal.ofReal (ρ z.2) :=
    (hm.comp measurable_fst).mul (hm.comp measurable_snd)
  rw [integral_withDensity_eq_integral_toReal_smul hm2
    (ae_of_all _ fun x => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hnn z.1), ENNReal.toReal_ofReal (hnn z.2)]

/-! ### The tilted probability and the real free energy along the tilt -/

open Classical in
/-- The tilt as a `ProbabilityMeasure` (total: junk value `haar` where `tiltMeasure` is not a
probability). It equals `tiltMeasure q h t` whenever `|t| ‖h‖∞ < 1`. -/
noncomputable def tiltProb (q h : Torus d → ℝ) (t : ℝ) : ProbabilityMeasure (Torus d) :=
  if H : IsProbabilityMeasure (tiltMeasure q h t) then ⟨tiltMeasure q h t, H⟩
  else haarProbability d

/-- The real function `φ(t) = F((1 + t h) μ)`, via `toReal` of the extended free energy. -/
noncomputable def freeEnergyTilt (A : InteractionData d) (q h : Torus d → ℝ) (t : ℝ) : ℝ :=
  (freeEnergy A (tiltProb q h t)).toReal

/-- The entropy part `∫ ρ_t log ρ_t dm` of the tilted free energy. -/
noncomputable def tiltEntropy (q h : Torus d → ℝ) (t : ℝ) : ℝ :=
  ∫ x, tiltDensity q h t x * Real.log (tiltDensity q h t x) ∂(haar d)

/-- Constant coefficient of the potential part: `∫ V q dm + ½ ∬ W q⊗q dm²`. -/
noncomputable def tiltCoeff0 (A : InteractionData d) (q : Torus d → ℝ) : ℝ :=
  ∫ x, q x * A.V x ∂(haar d) +
    (1 / 2 : ℝ) * ∫ p : Torus d × Torus d, (q p.1 * q p.2) * A.W p.1 p.2 ∂((haar d).prod (haar d))

/-- Linear coefficient of the potential part. -/
noncomputable def tiltCoeff1 (A : InteractionData d) (q h : Torus d → ℝ) : ℝ :=
  ∫ x, (q x * h x) * A.V x ∂(haar d) +
    (1 / 2 : ℝ) * ∫ p : Torus d × Torus d, (q p.1 * q p.2) * (h p.1 + h p.2) * A.W p.1 p.2
      ∂((haar d).prod (haar d))

/-- Quadratic coefficient of the potential part: `½ ∬ W (q h)⊗(q h) dm²`. -/
noncomputable def tiltCoeff2 (A : InteractionData d) (q h : Torus d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ p : Torus d × Torus d, (q p.1 * q p.2) * (h p.1 * h p.2) * A.W p.1 p.2
    ∂((haar d).prod (haar d))

theorem InteractionData.isBdd_V (A : InteractionData d) : IsBdd A.V :=
  ⟨A.V_continuous.measurable, A.V_bounded⟩

theorem InteractionData.isBdd_W (A : InteractionData d) :
    IsBdd (fun p : Torus d × Torus d => A.W p.1 p.2) :=
  ⟨A.W_continuous.measurable, by
    obtain ⟨B, hB⟩ := A.W_bounded
    exact ⟨B, fun p => hB p.1 p.2⟩⟩

end DGPS

namespace DGPS.TiltData

variable {d : ℕ}

variable {q h : Torus d → ℝ} {c C M : ℝ} (H : TiltData q h c C M)
include H

theorem isBdd_q : IsBdd q :=
  ⟨H.q_meas, C, fun x => by rw [abs_of_pos (H.q_pos x)]; exact H.q_le x⟩

theorem isBdd_h : IsBdd h := ⟨H.h_meas, M, H.h_le⟩

theorem isBdd_tiltDensity (t : ℝ) : IsBdd (tiltDensity q h t) :=
  H.isBdd_q.mul ((IsBdd.const 1).add ((IsBdd.const t).mul H.isBdd_h))

theorem abs_log_tiltDensity_le {t : ℝ} (ht : |t| < tiltRadius M) (x : Torus d) :
    |Real.log (tiltDensity q h t x)| ≤ |Real.log (c / 2)| + |Real.log (3 * C / 2)| := by
  obtain ⟨h1, h2⟩ := H.tiltDensity_bounds ht x
  have hpos : 0 < c / 2 := half_pos H.c_pos
  have l1 := Real.log_le_log hpos h1
  have l2 := Real.log_le_log (H.tiltDensity_pos ht x) h2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (c / 2)), abs_nonneg (Real.log (3 * C / 2))]
  · linarith [le_abs_self (Real.log (3 * C / 2)), abs_nonneg (Real.log (c / 2))]

theorem isBdd_log_tiltDensity {t : ℝ} (ht : |t| < tiltRadius M) :
    IsBdd (fun x => Real.log (tiltDensity q h t x)) :=
  ⟨Real.measurable_log.comp (H.measurable_tiltDensity t), _, H.abs_log_tiltDensity_le ht⟩

theorem isProbabilityMeasure_tiltMeasure' {t : ℝ} (ht : |t| < tiltRadius M) :
    |t| * M < 1 := by
  have hM := H.M_nonneg
  have h1 : |t| * M ≤ tiltRadius M * M := mul_le_mul_of_nonneg_right ht.le hM
  have h2 : tiltRadius M * M ≤ 1 / 2 := by
    unfold tiltRadius
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

theorem coe_tiltProb {t : ℝ} (ht : |t| * M < 1) :
    ((tiltProb q h t : ProbabilityMeasure (Torus d)) : Measure (Torus d)) = tiltMeasure q h t := by
  have := H.isProbabilityMeasure_tiltMeasure ht
  simp [tiltProb, this]

theorem relativeEntropy_tilt {t : ℝ} (ht : |t| < tiltRadius M) :
    relativeEntropy (tiltMeasure q h t) (haar d) = ENNReal.ofReal (tiltEntropy q h t) ∧
      0 ≤ tiltEntropy q h t := by
  have hmeas := H.measurable_tiltDensity t
  have hnn : ∀ x, 0 ≤ tiltDensity q h t x := fun x => (H.tiltDensity_pos ht x).le
  have hlog := H.isBdd_log_tiltDensity ht
  have hρl : Integrable (fun x => tiltDensity q h t x * Real.log (tiltDensity q h t x))
      (haar d) := ((H.isBdd_tiltDensity t).mul hlog).integrable
  have hρ : Integrable (tiltDensity q h t) (haar d) := (H.isBdd_tiltDensity t).integrable
  have hint : Integrable (fun x => tiltDensity q h t x * Real.log (tiltDensity q h t x) -
      tiltDensity q h t x + 1) (haar d) := (hρl.sub hρ).add (integrable_const _)
  have hfnn : ∀ x, 0 ≤ tiltDensity q h t x * Real.log (tiltDensity q h t x) -
      tiltDensity q h t x + 1 := fun x => self_mul_log_sub_add_one_nonneg (hnn x)
  have hE : ∫ x, (tiltDensity q h t x * Real.log (tiltDensity q h t x) - tiltDensity q h t x + 1)
      ∂(haar d) = tiltEntropy q h t := by
    have h1 : Integrable (fun x => tiltDensity q h t x * Real.log (tiltDensity q h t x) -
        tiltDensity q h t x) (haar d) := hρl.sub hρ
    rw [integral_add h1 (integrable_const _), integral_sub hρl hρ, H.integral_tiltDensity]
    simp [tiltEntropy]
  refine ⟨?_, hE ▸ integral_nonneg hfnn⟩
  unfold tiltMeasure
  rw [relativeEntropy_withDensity (ae_of_all _ hnn) hmeas.aemeasurable,
    entropy_mass_one (H.integral_tiltDensity t),
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hfnn), hE]

theorem potential_tilt (A : InteractionData d) {t : ℝ} (ht : |t| * M < 1) :
    potentialEnergy A (tiltProb q h t : ProbabilityMeasure (Torus d)) +
        (1 / 2 : ℝ) * interactionEnergy A (tiltProb q h t : ProbabilityMeasure (Torus d)) =
      tiltCoeff0 A q + tiltCoeff1 A q h * t + tiltCoeff2 A q h * t ^ 2 := by
  have hq1 : IsBdd fun p : Torus d × Torus d => q p.1 := H.isBdd_q.comp_fst
  have hq2 : IsBdd fun p : Torus d × Torus d => q p.2 := H.isBdd_q.comp_snd
  have hh1 : IsBdd fun p : Torus d × Torus d => h p.1 := H.isBdd_h.comp_fst
  have hh2 : IsBdd fun p : Torus d × Torus d => h p.2 := H.isBdd_h.comp_snd
  have hW := A.isBdd_W
  have i0 : Integrable (fun p : Torus d × Torus d => (q p.1 * q p.2) * A.W p.1 p.2)
      ((haar d).prod (haar d)) := ((hq1.mul hq2).mul hW).integrable
  have i1 : Integrable (fun p : Torus d × Torus d =>
      (q p.1 * q p.2) * (h p.1 + h p.2) * A.W p.1 p.2) ((haar d).prod (haar d)) :=
    ((hq1.mul hq2).mul (hh1.add hh2) |>.mul hW).integrable
  have i2 : Integrable (fun p : Torus d × Torus d =>
      (q p.1 * q p.2) * (h p.1 * h p.2) * A.W p.1 p.2) ((haar d).prod (haar d)) :=
    ((hq1.mul hq2).mul (hh1.mul hh2) |>.mul hW).integrable
  have j0 : Integrable (fun x => q x * A.V x) (haar d) := (H.isBdd_q.mul A.isBdd_V).integrable
  have j1 : Integrable (fun x => (q x * h x) * A.V x) (haar d) :=
    ((H.isBdd_q.mul H.isBdd_h).mul A.isBdd_V).integrable
  unfold potentialEnergy interactionEnergy tiltCoeff0 tiltCoeff1 tiltCoeff2
  rw [H.coe_tiltProb ht]
  unfold tiltMeasure
  rw [integral_withDensity_ofReal (H.measurable_tiltDensity t) (H.tiltDensity_nonneg ht),
    integral_prod_withDensity_ofReal (H.measurable_tiltDensity t) (H.tiltDensity_nonneg ht)]
  have e1 : ∀ x, tiltDensity q h t x * A.V x = q x * A.V x + t * ((q x * h x) * A.V x) :=
    fun x => by unfold tiltDensity; ring
  have e2 : ∀ p : Torus d × Torus d, (tiltDensity q h t p.1 * tiltDensity q h t p.2) *
      A.W p.1 p.2 = (q p.1 * q p.2) * A.W p.1 p.2 +
        (t * ((q p.1 * q p.2) * (h p.1 + h p.2) * A.W p.1 p.2) +
          t ^ 2 * ((q p.1 * q p.2) * (h p.1 * h p.2) * A.W p.1 p.2)) :=
    fun p => by unfold tiltDensity; ring
  have k12 : Integrable (fun p : Torus d × Torus d =>
      t * ((q p.1 * q p.2) * (h p.1 + h p.2) * A.W p.1 p.2) +
        t ^ 2 * ((q p.1 * q p.2) * (h p.1 * h p.2) * A.W p.1 p.2)) ((haar d).prod (haar d)) :=
    (i1.const_mul t).add (i2.const_mul (t ^ 2))
  simp_rw [e1, e2]
  rw [integral_add j0 (j1.const_mul t), integral_const_mul, integral_add i0 k12,
    integral_add (i1.const_mul t) (i2.const_mul (t ^ 2)), integral_const_mul, integral_const_mul]
  ring

theorem freeEnergyTilt_eq (A : InteractionData d) {t : ℝ} (ht : |t| < tiltRadius M) :
    freeEnergyTilt A q h t = tiltEntropy q h t +
      (tiltCoeff0 A q + tiltCoeff1 A q h * t + tiltCoeff2 A q h * t ^ 2) := by
  have ht1 := H.isProbabilityMeasure_tiltMeasure' ht
  obtain ⟨hre, hnn⟩ := H.relativeEntropy_tilt ht
  rw [← H.potential_tilt A ht1]
  unfold freeEnergyTilt freeEnergy
  rw [H.coe_tiltProb ht1, hre, EReal.coe_ennreal_ofReal, max_eq_left hnn]
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.toReal_coe, add_assoc]

/-- The derivative `∫ q h (log ρ_t + 1) dm` of the entropy part. -/
noncomputable def tiltEntropyDeriv (q h : Torus d → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (q x * h x) * (Real.log (tiltDensity q h t x) + 1) ∂(haar d)

omit H in
theorem hasDerivAt_tiltDensity (x : Torus d) (t : ℝ) :
    HasDerivAt (fun s => tiltDensity q h s x) (q x * h x) t := by
  have := (((hasDerivAt_id t).mul_const (h x)).const_add 1).const_mul (q x)
  convert this using 1 <;> simp [tiltDensity]

theorem hasDerivAt_tiltEntropy {t : ℝ} (ht : |t| < tiltRadius M) :
    HasDerivAt (tiltEntropy q h) (tiltEntropyDeriv q h t) t := by
  have hs : Metric.ball (0 : ℝ) (tiltRadius M) ∈ 𝓝 t := Metric.isOpen_ball.mem_nhds (by simpa using ht)
  have hmem : ∀ s ∈ Metric.ball (0 : ℝ) (tiltRadius M), |s| < tiltRadius M := fun s hs => by
    simpa using hs
  have hFd : ∀ s ∈ Metric.ball (0 : ℝ) (tiltRadius M), IsBdd fun x =>
      (q x * h x) * (Real.log (tiltDensity q h s x) + 1) := fun s hs =>
    (H.isBdd_q.mul H.isBdd_h).mul ((H.isBdd_log_tiltDensity (hmem s hs)).add (IsBdd.const 1))
  obtain ⟨B, hB⟩ := (hFd t (by simpa using ht)).2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := haar d)
    (F := fun s x => tiltDensity q h s x * Real.log (tiltDensity q h s x))
    (F' := fun s x => (q x * h x) * (Real.log (tiltDensity q h s x) + 1))
    (bound := fun _ => |C * M| * (|Real.log (c / 2)| + |Real.log (3 * C / 2)| + 1))
    hs ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · refine Filter.eventually_of_mem hs fun s hs' => ?_
    exact ((H.isBdd_tiltDensity s).mul (H.isBdd_log_tiltDensity (hmem s hs'))).1.aestronglyMeasurable
  · exact ((H.isBdd_tiltDensity t).mul (H.isBdd_log_tiltDensity ht)).integrable
  · exact (hFd t (by simpa using ht)).1.aestronglyMeasurable
  · refine ae_of_all _ fun x s hs' => ?_
    have hL := H.abs_log_tiltDensity_le (hmem s hs') x
    have hqh : |q x * h x| ≤ |C * M| := by
      rw [abs_mul, abs_of_pos (H.q_pos x), abs_mul, abs_of_pos H.C_pos]
      exact (mul_le_mul (H.q_le x) (H.h_le x) (abs_nonneg _) H.C_pos.le).trans (le_abs_self _)
      |>.trans (by rw [abs_mul, abs_of_pos H.C_pos, abs_of_nonneg H.M_nonneg])
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hqh ((abs_add_le _ _).trans (by simpa using add_le_add_right hL 1))
      (abs_nonneg _) (abs_nonneg _)
  · exact integrable_const _
  · refine ae_of_all _ fun x s hs' => ?_
    have hpos := H.tiltDensity_pos (hmem s hs') x
    have h1 := (hasDerivAt_tiltDensity (q := q) (h := h) x s).log hpos.ne'
    have h2 := (hasDerivAt_tiltDensity (q := q) (h := h) x s).mul h1
    convert h2 using 1
    field_simp

theorem hasDerivAt_tiltEntropyDeriv_zero :
    HasDerivAt (tiltEntropyDeriv q h) (∫ x, q x * h x ^ 2 ∂(haar d)) 0 := by
  have hs : Metric.ball (0 : ℝ) (tiltRadius M) ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds _ H.tiltRadius_pos
  have hmem : ∀ s ∈ Metric.ball (0 : ℝ) (tiltRadius M), |s| < tiltRadius M := fun s hs => by
    simpa using hs
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := haar d)
    (F := fun s x => (q x * h x) * (Real.log (tiltDensity q h s x) + 1))
    (F' := fun s x => (q x * h x) * ((q x * h x) / tiltDensity q h s x))
    (bound := fun _ => |C * M| * (|C * M| / (c / 2)))
    hs ?_ ?_ ?_ ?_ ?_ ?_
  · have e : ∫ x, (q x * h x) * ((q x * h x) / tiltDensity q h 0 x) ∂(haar d) =
        ∫ x, q x * h x ^ 2 ∂(haar d) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      have := (H.q_pos x).ne'
      simp only [tiltDensity, zero_mul, add_zero, mul_one]
      field_simp
    rw [e] at key
    exact key.2
  · refine Filter.eventually_of_mem hs fun s hs' => ?_
    exact ((H.isBdd_q.mul H.isBdd_h).mul
      ((H.isBdd_log_tiltDensity (hmem s hs')).add (IsBdd.const 1))).1.aestronglyMeasurable
  · exact ((H.isBdd_q.mul H.isBdd_h).mul
      ((H.isBdd_log_tiltDensity (by simpa using H.tiltRadius_pos)).add (IsBdd.const 1))).integrable
  · exact ((H.q_meas.mul H.h_meas).mul
      ((H.q_meas.mul H.h_meas).div (H.measurable_tiltDensity 0))).aestronglyMeasurable
  · refine ae_of_all _ fun x s hs' => ?_
    have hb := (H.tiltDensity_bounds (hmem s hs') x).1
    have hqh : |q x * h x| ≤ |C * M| := by
      rw [abs_mul, abs_of_pos (H.q_pos x)]
      calc q x * |h x| ≤ C * M :=
            mul_le_mul (H.q_le x) (H.h_le x) (abs_nonneg _) H.C_pos.le
        _ ≤ |C * M| := le_abs_self _
    have hpos := H.tiltDensity_pos (hmem s hs') x
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hpos]
    refine mul_le_mul hqh ?_ (by positivity) (abs_nonneg _)
    exact div_le_div₀ (abs_nonneg _) hqh (half_pos H.c_pos) hb
  · exact integrable_const _
  · refine ae_of_all _ fun x s hs' => ?_
    have hpos := H.tiltDensity_pos (hmem s hs') x
    have h1 := (hasDerivAt_tiltDensity (q := q) (h := h) x s).log hpos.ne'
    exact (h1.add_const 1).const_mul (q x * h x)

/-- The derivative `φ'(t)` of the real free energy along the tilt. -/
noncomputable def freeEnergyTiltDeriv (A : InteractionData d) (q h : Torus d → ℝ) (t : ℝ) : ℝ :=
  tiltEntropyDeriv q h t + tiltCoeff1 A q h + 2 * tiltCoeff2 A q h * t

theorem hasDerivAt_freeEnergyTilt (A : InteractionData d) {t : ℝ} (ht : |t| < tiltRadius M) :
    HasDerivAt (freeEnergyTilt A q h) (freeEnergyTiltDeriv A q h t) t := by
  have hs : Metric.ball (0 : ℝ) (tiltRadius M) ∈ 𝓝 t :=
    Metric.isOpen_ball.mem_nhds (by simpa using ht)
  have hpoly : HasDerivAt (fun s : ℝ => tiltCoeff0 A q + tiltCoeff1 A q h * s +
      tiltCoeff2 A q h * s ^ 2) (tiltCoeff1 A q h + 2 * tiltCoeff2 A q h * t) t := by
    have := (((hasDerivAt_id t).const_mul (tiltCoeff1 A q h)).const_add (tiltCoeff0 A q)).add
      ((hasDerivAt_pow 2 t).const_mul (tiltCoeff2 A q h))
    convert this using 1
    · funext s; simp only [Pi.add_apply, id]
    · simp; ring
  have h2 := (H.hasDerivAt_tiltEntropy ht).add hpoly
  refine (h2.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hs] with s hs'
    exact H.freeEnergyTilt_eq A (by simpa using hs')
  · unfold freeEnergyTiltDeriv; ring

theorem hasDerivAt_freeEnergyTiltDeriv_zero (A : InteractionData d) :
    HasDerivAt (freeEnergyTiltDeriv A q h) (∫ x, q x * h x ^ 2 ∂(haar d) + 2 * tiltCoeff2 A q h)
      0 := by
  have h1 := ((H.hasDerivAt_tiltEntropyDeriv_zero).add_const (tiltCoeff1 A q h)).add
    (((hasDerivAt_id (0 : ℝ)).const_mul (2 * tiltCoeff2 A q h)))
  convert h1 using 1
  · funext s; simp only [freeEnergyTiltDeriv, Pi.add_apply, id]
  · simp

theorem finiteFreeEnergy_tilt (A : InteractionData d) {t : ℝ} (ht : |t| * M < 1) :
    FiniteFreeEnergy A (tiltProb q h t) := by
  rw [finiteFreeEnergy_iff, H.coe_tiltProb ht]
  have hnn := H.tiltDensity_nonneg ht
  unfold tiltMeasure
  rw [relativeEntropy_withDensity (ae_of_all _ hnn) (H.measurable_tiltDensity t).aemeasurable,
    entropy_mass_one (H.integral_tiltDensity t)]
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal ((C * (1 + |t| * M)) ^ 2 + 1) * haar d Set.univ)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) ?_
  rw [← lintegral_const]
  refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
  have hρ := hnn x
  have hB : tiltDensity q h t x ≤ C * (1 + |t| * M) := by
    unfold tiltDensity
    have h1 : t * h x ≤ |t| * M := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (H.h_le x) (abs_nonneg _)
    exact mul_le_mul (H.q_le x) (by linarith) (H.one_add_nonneg ht x) H.C_pos.le
  have hlog : tiltDensity q h t x * Real.log (tiltDensity q h t x) ≤
      tiltDensity q h t x * (tiltDensity q h t x - 1) := by
    rcases hρ.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h0) hρ
  have : tiltDensity q h t x ^ 2 ≤ (C * (1 + |t| * M)) ^ 2 := by
    exact pow_le_pow_left₀ hρ hB 2
  nlinarith

end DGPS.TiltData

namespace DGPS

variable {d : ℕ}

/-! ### The theorem -/

/-- Build the tilt data from a probability `μ = q · haar`. -/
theorem tiltData_of_measure (μ : ProbabilityMeasure (Torus d)) {q h : Torus d → ℝ} {c C M : ℝ}
    (hq : Measurable q) (hc : 0 < c) (hcq : ∀ x, c ≤ q x) (hqC : ∀ x, q x ≤ C)
    (hμ : (μ : Measure (Torus d)) = (haar d).withDensity fun x => ENNReal.ofReal (q x))
    (hh : Measurable h) (hM : ∀ x, |h x| ≤ M)
    (h0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) : TiltData q h c C M := by
  have hnn : ∀ x, 0 ≤ q x := fun x => hc.le.trans (hcq x)
  refine ⟨hq, hh, hc, hcq, hqC, hM, ?_, ?_⟩
  · have h1 : ∫ x, (1 : ℝ) ∂(μ : Measure (Torus d)) = 1 := by simp
    rw [hμ, integral_withDensity_ofReal hq hnn] at h1
    simpa using h1
  · rw [hμ, integral_withDensity_ofReal hq hnn] at h0
    exact h0

/-- **Second variation of the free energy.** Let `μ = q · haar` with `0 < c ≤ q ≤ C`, and `h`
bounded measurable with `∫ h dμ = 0`. For `|t| ‖h‖∞ < 1` the tilt `(1 + t h) μ` is a probability
measure of finite free energy, and `φ(t) = F((1 + t h) μ)` (a real function, via `toReal`) is
differentiable near `0` with a derivative `φ₁` that is itself differentiable at `0`, with
`φ''(0) = ∫ h² dμ + ∬ W h⊗h dμ²`. -/
theorem freeEnergy_secondVariation (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    {q h : Torus d → ℝ} {c C M : ℝ}
    (hq : Measurable q) (hc : 0 < c) (hcq : ∀ x, c ≤ q x) (hqC : ∀ x, q x ≤ C)
    (hμ : (μ : Measure (Torus d)) = (haar d).withDensity fun x => ENNReal.ofReal (q x))
    (hh : Measurable h) (hM : ∀ x, |h x| ≤ M)
    (h0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) :
    (∀ t : ℝ, |t| * M < 1 →
      ((tiltProb q h t : ProbabilityMeasure (Torus d)) : Measure (Torus d)) =
          (μ : Measure (Torus d)).withDensity (fun x => ENNReal.ofReal (1 + t * h x)) ∧
        ∃ hfin : FiniteFreeEnergy A (tiltProb q h t),
          freeEnergyValue A (tiltProb q h t) hfin = freeEnergyTilt A q h t) ∧
    ∃ φ₁ : ℝ → ℝ, (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (freeEnergyTilt A q h) (φ₁ t) t) ∧
      HasDerivAt φ₁ (∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) +
        ∫ p, A.W p.1 p.2 * (h p.1 * h p.2) ∂((μ : Measure (Torus d)).prod μ)) 0 := by
  have H := tiltData_of_measure μ hq hc hcq hqC hμ hh hM h0
  have hnn : ∀ x, 0 ≤ q x := fun x => H.q_pos x |>.le
  refine ⟨fun t ht => ⟨?_, H.finiteFreeEnergy_tilt A ht, rfl⟩, TiltData.freeEnergyTiltDeriv A q h, ?_, ?_⟩
  · rw [H.coe_tiltProb ht, hμ, tiltMeasure]
    have m1 : Measurable fun x => ENNReal.ofReal (q x) := ENNReal.measurable_ofReal.comp hq
    have m2 : Measurable fun x => ENNReal.ofReal (1 + t * h x) :=
      ENNReal.measurable_ofReal.comp (measurable_const.add (measurable_const.mul hh))
    rw [← withDensity_mul _ m1 m2]
    congr 1
    funext x
    simp only [Pi.mul_apply, tiltDensity]
    rw [ENNReal.ofReal_mul (hnn x)]
  · have hs : Metric.ball (0 : ℝ) (tiltRadius M) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds _ H.tiltRadius_pos
    filter_upwards [hs] with t ht
    exact H.hasDerivAt_freeEnergyTilt A (by simpa using ht)
  · have key := H.hasDerivAt_freeEnergyTiltDeriv_zero A
    convert key using 1
    have e1 : ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) = ∫ x, q x * h x ^ 2 ∂(haar d) := by
      rw [hμ, integral_withDensity_ofReal hq hnn]
    have e2 : ∫ p, A.W p.1 p.2 * (h p.1 * h p.2) ∂((μ : Measure (Torus d)).prod μ) =
        2 * tiltCoeff2 A q h := by
      rw [hμ, integral_prod_withDensity_ofReal hq hnn]
      unfold tiltCoeff2
      rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      ring
    rw [e1, e2]

/-- A bounded measurable mean-zero `h` defines an element `f` of `L²_0(μ)` (the `μ`-a.e. class of
`h`). -/
theorem exists_centeredL2_of_bounded (μ : ProbabilityMeasure (Torus d)) {h : Torus d → ℝ} {M : ℝ}
    (hh : Measurable h) (hM : ∀ x, |h x| ≤ M)
    (h0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) :
    ∃ f : centeredL2 μ, ((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) =ᵐ[(μ : Measure (Torus d))] h := by
  have hmem : MemLp h 2 (μ : Measure (Torus d)) :=
    MemLp.of_bound hh.aestronglyMeasurable M (ae_of_all _ fun x => by simpa using hM x)
  have hae := hmem.coeFn_toLp
  refine ⟨⟨hmem.toLp h, ?_⟩, hae⟩
  show ∫ x, (hmem.toLp h) x ∂(μ : Measure (Torus d)) = 0
  rw [integral_congr_ae hae, h0]

/-- **Second variation as the density Hessian form.** In the setting of
`freeEnergy_secondVariation`, the class `f ∈ L²_0(μ)` of `h` satisfies
`∫ h² dμ + ∬ W h⊗h dμ² = ⟨f, H_μ f⟩`. -/
theorem freeEnergy_secondVariation_hessian (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) {h : Torus d → ℝ} {M : ℝ}
    (hh : Measurable h) (hM : ∀ x, |h x| ≤ M)
    (h0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) :
    ∃ f : centeredL2 μ,
      ((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) =ᵐ[(μ : Measure (Torus d))] h ∧
      ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) +
          ∫ p, A.W p.1 p.2 * (h p.1 * h p.2) ∂((μ : Measure (Torus d)).prod μ) =
        inner ℝ f (densityHessian A μ f) := by
  obtain ⟨f, hf⟩ := exists_centeredL2_of_bounded μ hh hM h0
  refine ⟨f, hf, ?_⟩
  rw [inner_densityHessian]
  congr 1
  · have h1 : ‖f‖ ^ 2 = ∫ x, ((f : Lp ℝ 2 (μ : Measure (Torus d))) x) ^ 2 ∂(μ : Measure (Torus d)) := by
      have : ‖(f : Lp ℝ 2 (μ : Measure (Torus d)))‖ ^ 2 =
          inner ℝ (f : Lp ℝ 2 (μ : Measure (Torus d))) (f : Lp ℝ 2 (μ : Measure (Torus d))) :=
        (real_inner_self_eq_norm_sq _).symm
      rw [← Submodule.norm_coe, this, L2.inner_def]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp [sq]
    rw [h1]
    exact integral_congr_ae (hf.mono fun x hx => by simp only [hx])
  · have h1 : ∀ᵐ p ∂((μ : Measure (Torus d)).prod (μ : Measure (Torus d))),
        ((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) p.1 = h p.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := (μ : Measure (Torus d))) (ν := (μ : Measure (Torus d)))).ae hf
    have h2 : ∀ᵐ p ∂((μ : Measure (Torus d)).prod (μ : Measure (Torus d))),
        ((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) p.2 = h p.2 :=
      (Measure.quasiMeasurePreserving_snd (μ := (μ : Measure (Torus d))) (ν := (μ : Measure (Torus d)))).ae hf
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with p a b
    rw [a, b]

/-! ### The first variation -/

end DGPS

namespace DGPS.TiltData

variable {d : ℕ}

variable {q h : Torus d → ℝ} {c C M : ℝ} (H : TiltData q h c C M)
include H

theorem integrable_qh_log :
    Integrable (fun x => (q x * h x) * Real.log (q x)) (haar d) := by
  have hl : IsBdd fun x => Real.log (q x) :=
    ⟨Real.measurable_log.comp H.q_meas, |Real.log c| + |Real.log C|, fun x => by
      have l1 := Real.log_le_log H.c_pos (H.c_le x)
      have l2 := Real.log_le_log (H.q_pos x) (H.q_le x)
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log C)]
      · linarith [le_abs_self (Real.log C), abs_nonneg (Real.log c)]⟩
  exact ((H.isBdd_q.mul H.isBdd_h).mul hl).integrable

theorem tiltEntropyDeriv_zero :
    tiltEntropyDeriv q h 0 = ∫ x, (q x * h x) * Real.log (q x) ∂(haar d) := by
  have i1 := H.integrable_qh_log
  unfold tiltEntropyDeriv
  have e : ∀ x, (q x * h x) * (Real.log (tiltDensity q h 0 x) + 1) =
      (q x * h x) * Real.log (q x) + q x * h x := fun x => by
    simp [tiltDensity]; ring
  simp_rw [e]
  rw [integral_add i1 H.integrable_qh, H.int_qh, add_zero]

/-- The first derivative at `0`, as `haar`-integrals. -/
theorem freeEnergyTiltDeriv_zero (A : InteractionData d) :
    freeEnergyTiltDeriv A q h 0 =
      ∫ x, (q x * h x) * (Real.log (q x) + (A.V x + ∫ z, q z * A.W x z ∂(haar d))) ∂(haar d) := by
  have hq1 : IsBdd fun p : Torus d × Torus d => q p.1 := H.isBdd_q.comp_fst
  have hq2 : IsBdd fun p : Torus d × Torus d => q p.2 := H.isBdd_q.comp_snd
  have hh1 : IsBdd fun p : Torus d × Torus d => h p.1 := H.isBdd_h.comp_fst
  have hh2 : IsBdd fun p : Torus d × Torus d => h p.2 := H.isBdd_h.comp_snd
  have hW := A.isBdd_W
  have iA : Integrable (fun p : Torus d × Torus d => (q p.1 * q p.2) * h p.1 * A.W p.1 p.2)
      ((haar d).prod (haar d)) := (((hq1.mul hq2).mul hh1).mul hW).integrable
  have iB : Integrable (fun p : Torus d × Torus d => (q p.1 * q p.2) * h p.2 * A.W p.1 p.2)
      ((haar d).prod (haar d)) := (((hq1.mul hq2).mul hh2).mul hW).integrable
  have iV : Integrable (fun x => (q x * h x) * A.V x) (haar d) :=
    ((H.isBdd_q.mul H.isBdd_h).mul A.isBdd_V).integrable
  have sw : ∫ p : Torus d × Torus d, (q p.1 * q p.2) * h p.2 * A.W p.1 p.2 ∂((haar d).prod (haar d))
      = ∫ p : Torus d × Torus d, (q p.1 * q p.2) * h p.1 * A.W p.1 p.2 ∂((haar d).prod (haar d)) := by
    rw [← integral_prod_swap (μ := haar d) (ν := haar d)
      (fun p : Torus d × Torus d => (q p.1 * q p.2) * h p.1 * A.W p.1 p.2)]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [A.W_symm p.2 p.1]; ring
  have hg : ∀ x, ∫ z, ((q x * q z) * h x * A.W x z) ∂(haar d) =
      (q x * h x) * ∫ z, q z * A.W x z ∂(haar d) := fun x => by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ring
  have hA : ∫ p : Torus d × Torus d, (q p.1 * q p.2) * h p.1 * A.W p.1 p.2
      ∂((haar d).prod (haar d)) =
      ∫ x, (q x * h x) * ∫ z, q z * A.W x z ∂(haar d) ∂(haar d) := by
    rw [integral_prod _ iA]
    exact integral_congr_ae (ae_of_all _ hg)
  have iC : Integrable (fun x => (q x * h x) * ∫ z, q z * A.W x z ∂(haar d)) (haar d) := by
    have := iA.integral_prod_left
    refine this.congr (ae_of_all _ fun x => ?_)
    exact hg x
  have i1 : Integrable (fun x => (q x * h x) * (A.V x + ∫ z, q z * A.W x z ∂(haar d))) (haar d) := by
    have := iV.add iC
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]; ring
  have e1 : ∫ x, (q x * h x) * (A.V x + ∫ z, q z * A.W x z ∂(haar d)) ∂(haar d) =
      ∫ x, (q x * h x) * A.V x ∂(haar d) +
        ∫ x, (q x * h x) * ∫ z, q z * A.W x z ∂(haar d) ∂(haar d) := by
    rw [← integral_add iV iC]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [mul_add])
  have e0 : ∫ x, (q x * h x) * (Real.log (q x) + (A.V x + ∫ z, q z * A.W x z ∂(haar d)))
      ∂(haar d) = ∫ x, (q x * h x) * Real.log (q x) ∂(haar d) +
      ∫ x, (q x * h x) * (A.V x + ∫ z, q z * A.W x z ∂(haar d)) ∂(haar d) := by
    rw [← integral_add H.integrable_qh_log i1]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [mul_add])
  rw [e0]
  unfold freeEnergyTiltDeriv tiltCoeff1 tiltCoeff2
  rw [H.tiltEntropyDeriv_zero, e1, ← hA]
  have e2 : ∫ p : Torus d × Torus d, (q p.1 * q p.2) * (h p.1 + h p.2) * A.W p.1 p.2
      ∂((haar d).prod (haar d)) =
      ∫ p : Torus d × Torus d, (q p.1 * q p.2) * h p.1 * A.W p.1 p.2 ∂((haar d).prod (haar d)) +
      ∫ p : Torus d × Torus d, (q p.1 * q p.2) * h p.2 * A.W p.1 p.2 ∂((haar d).prod (haar d)) := by
    rw [← integral_add iA iB]
    exact integral_congr_ae (ae_of_all _ fun p => by ring)
  rw [e2, sw]
  ring

end DGPS.TiltData

namespace DGPS

variable {d : ℕ}

/-- **First variation** (bonus): `φ'(0) = ∫ h (log q + V + W * μ) dμ`. -/
theorem freeEnergy_firstVariation (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    {q h : Torus d → ℝ} {c C M : ℝ}
    (hq : Measurable q) (hc : 0 < c) (hcq : ∀ x, c ≤ q x) (hqC : ∀ x, q x ≤ C)
    (hμ : (μ : Measure (Torus d)) = (haar d).withDensity fun x => ENNReal.ofReal (q x))
    (hh : Measurable h) (hM : ∀ x, |h x| ≤ M)
    (h0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) :
    TiltData.freeEnergyTiltDeriv A q h 0 =
      ∫ x, h x * (Real.log (q x) + (A.V x + interactionConvolution A μ x))
        ∂(μ : Measure (Torus d)) := by
  have H := tiltData_of_measure μ hq hc hcq hqC hμ hh hM h0
  have hnn : ∀ x, 0 ≤ q x := fun x => (H.q_pos x).le
  rw [H.freeEnergyTiltDeriv_zero A, hμ, integral_withDensity_ofReal hq hnn]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have : interactionConvolution A μ x = ∫ z, q z * A.W x z ∂(haar d) := by
    unfold interactionConvolution
    rw [hμ, integral_withDensity_ofReal hq hnn]
  simp only []
  rw [this]
  ring

end DGPS
