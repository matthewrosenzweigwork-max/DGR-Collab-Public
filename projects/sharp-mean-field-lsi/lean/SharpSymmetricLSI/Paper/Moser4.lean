import SharpSymmetricLSI.Paper.Moser3

/-!
# One step of the Moser iteration (Phase 3, lane D)

From `∫|e|^{2m} < ∞` the Nash inequality, the energy inequality and Hölder interpolation give
`∫|e|^{4m+2} ≤ K^{(m+1)/m} (∫|e|^{2m})^{(2m+1)/m}` with an explicit `K`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI

/-- Hölder interpolation: `∫|w| ≤ (∫|e|^{2m})^{(2m+1)/(2(m+1))} (∫ w²)^{1/(2(m+1))}` when
`|w| ≤ |e|^{2m+1}`. -/
theorem holder_moser {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {w e : Ω → ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hw : AEStronglyMeasurable w μ) (he : AEStronglyMeasurable e μ)
    (hpt : ∀ x, |w x| ≤ |e x| ^ (2 * m + 1))
    (hZ : Integrable (fun x => |e x| ^ (2 * m)) μ) (hY : Integrable (fun x => w x ^ 2) μ) :
    ∫ x, |w x| ∂μ ≤ (∫ x, |e x| ^ (2 * m) ∂μ) ^ ((2 * m + 1 : ℝ) / (2 * (m + 1))) *
      (∫ x, w x ^ 2 ∂μ) ^ ((1 : ℝ) / (2 * (m + 1))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set p : ℝ := 2 * (m + 1) / (2 * m + 1)
  set q : ℝ := 2 * (m + 1)
  have hp : 0 < p := by positivity
  have hq : 0 < q := by positivity
  have hpq : p.HolderConjugate q := ⟨by simp only [p, q]; field_simp; ring, hp, hq⟩
  set α : ℝ := (2 * m + 1) * m / (m + 1)
  set f : Ω → ℝ := fun x => |e x| ^ α
  set g : Ω → ℝ := fun x => |w x| ^ ((1 : ℝ) / (m + 1))
  have hfp : ∀ x, f x ^ p = |e x| ^ (2 * m) := fun x => by
    simp only [f]
    rw [← Real.rpow_mul (abs_nonneg _)]
    have : α * p = ((2 * m : ℕ) : ℝ) := by simp only [α, p]; push_cast; field_simp
    rw [this, Real.rpow_natCast]
  have hgq : ∀ x, g x ^ q = w x ^ 2 := fun x => by
    simp only [g]
    rw [← Real.rpow_mul (abs_nonneg _)]
    have : (1 : ℝ) / (m + 1) * q = ((2 : ℕ) : ℝ) := by
      simp only [q]; push_cast; field_simp
    rw [this, Real.rpow_natCast, sq_abs]
  have hpt' : ∀ x, |w x| ≤ f x * g x := fun x => by
    have h1 : |w x| = |w x| ^ ((m : ℝ) / (m + 1)) * g x := by
      simp only [g]
      rw [← Real.rpow_add' (abs_nonneg _) (by positivity)]
      rw [show (m : ℝ) / (m + 1) + 1 / (m + 1) = 1 by field_simp, Real.rpow_one]
    rw [h1]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc |w x| ^ ((m : ℝ) / (m + 1)) ≤ (|e x| ^ (2 * m + 1)) ^ ((m : ℝ) / (m + 1)) :=
          Real.rpow_le_rpow (abs_nonneg _) (hpt x) (by positivity)
      _ = f x := by
          simp only [f, α]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
          congr 1; push_cast; ring
  have hfm : AEStronglyMeasurable f μ :=
    (he.norm.aemeasurable.pow_const α).aestronglyMeasurable.congr
      (Eventually.of_forall fun x => by simp only [f, Real.norm_eq_abs])
  have hgm : AEStronglyMeasurable g μ :=
    (hw.norm.aemeasurable.pow_const ((1 : ℝ) / (m + 1))).aestronglyMeasurable.congr
      (Eventually.of_forall fun x => by simp only [g, Real.norm_eq_abs])
  have hfL : MemLp f (ENNReal.ofReal p) μ := by
    rw [← integrable_norm_rpow_iff hfm (by simp [hp]) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le]
    refine hZ.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.norm_of_nonneg (by positivity), hfp]
  have hgL : MemLp g (ENNReal.ofReal q) μ := by
    rw [← integrable_norm_rpow_iff hgm (by simp [hq]) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq.le]
    refine hY.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.norm_of_nonneg (by positivity), hgq]
  have hfg : Integrable (fun x => f x * g x) μ := by
    refine ((hZ.div_const p).add (hY.div_const q)).mono' (hfm.mul hgm)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity), Pi.add_apply, ← hfp, ← hgq]
    exact Real.young_inequality_of_nonneg (by positivity) (by positivity) hpq
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (Eventually.of_forall fun x => by positivity)
    (Eventually.of_forall fun x => by positivity) hfL hgL
  simp_rw [hfp, hgq] at hH
  have e1 : (1 : ℝ) / p = (2 * m + 1 : ℝ) / (2 * (m + 1)) := by simp only [p]; field_simp
  have e2 : (1 : ℝ) / q = (1 : ℝ) / (2 * (m + 1)) := rfl
  rw [e1, e2] at hH
  exact (integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hfg
    (Eventually.of_forall hpt')).trans hH

/-- Absorption: `Y ≤ K (Z^α Y^β)²` gives `Y ≤ K^{(m+1)/m} Z^{(2m+1)/m}`. -/
theorem moser_absorb {Y K Z : ℝ} (hY : 0 ≤ Y) (hK : 0 ≤ K) (hZ : 0 ≤ Z) {m : ℕ} (hm : 1 ≤ m)
    (h : Y ≤ K * (Z ^ ((2 * m + 1 : ℝ) / (2 * (m + 1))) * Y ^ ((1 : ℝ) / (2 * (m + 1)))) ^ 2) :
    Y ≤ K ^ (((m : ℝ) + 1) / m) * Z ^ ((2 * m + 1 : ℝ) / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rcases hY.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  have e1 : (Z ^ ((2 * m + 1 : ℝ) / (2 * (m + 1))) * Y ^ ((1 : ℝ) / (2 * (m + 1)))) ^ 2 =
      Z ^ ((2 * m + 1 : ℝ) / (m + 1)) * Y ^ ((1 : ℝ) / (m + 1)) := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hZ,
      ← Real.rpow_mul hY]
    congr 2 <;> push_cast <;> field_simp
  rw [e1] at h
  have hsplit : Y = Y ^ ((m : ℝ) / (m + 1)) * Y ^ ((1 : ℝ) / (m + 1)) := by
    rw [← Real.rpow_add hpos, show (m : ℝ) / (m + 1) + 1 / (m + 1) = 1 by field_simp,
      Real.rpow_one]
  have hYb : 0 < Y ^ ((1 : ℝ) / (m + 1)) := Real.rpow_pos_of_pos hpos _
  have h2 : Y ^ ((m : ℝ) / (m + 1)) ≤ K * Z ^ ((2 * m + 1 : ℝ) / (m + 1)) := by
    rw [← mul_assoc] at h
    nth_rewrite 1 [hsplit] at h
    exact le_of_mul_le_mul_right h hYb
  have h3 := Real.rpow_le_rpow (by positivity) h2 (show (0 : ℝ) ≤ ((m : ℝ) + 1) / m by positivity)
  rw [← Real.rpow_mul hY, show (m : ℝ) / (m + 1) * ((m + 1) / m) = 1 by field_simp,
    Real.rpow_one, Real.mul_rpow hK (by positivity), ← Real.rpow_mul hZ] at h3
  convert h3 using 3
  field_simp

section step
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Measure (UnitAddTorus ι)}
  [IsProbabilityMeasure P] {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
  (ha : (volume : Measure (UnitAddTorus ι)) ≤ ENNReal.ofReal a • P)
  (hb : P ≤ ENNReal.ofReal b • volume) {e : UnitAddTorus ι → ℝ} (he : MemH1 P e) {lam : ℝ}
  (hlam : 0 ≤ lam)
  (heig : ∀ φ, MemH1 P φ → ∫ x, ∑ k, weakGrad e x k * weakGrad φ x k ∂P =
    lam * ∫ x, e x * φ x ∂P)

/-- The Nash scale. -/
def moserR (a b lam : ℝ) (m : ℕ) : ℕ := ⌈a * b * (1 + 2 * m) * lam⌉₊ + 1

/-- The constant of one Moser step. -/
def moserK (ι : Type*) [Fintype ι] (a b lam : ℝ) (m : ℕ) : ℝ :=
  2 * ((2 * moserR a b lam m + 1 : ℕ) : ℝ) ^ Fintype.card ι

theorem integral_le_smul_of_le {μ ν : Measure (UnitAddTorus ι)} {c : ℝ} (hc : 0 ≤ c)
    (hle : μ ≤ ENNReal.ofReal c • ν) {f : UnitAddTorus ι → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : Integrable f ν) : ∫ x, f x ∂μ ≤ c * ∫ x, f x ∂ν := by
  have h1 : Integrable f (ENNReal.ofReal c • ν) := hf.smul_measure ENNReal.ofReal_ne_top
  calc ∫ x, f x ∂μ ≤ ∫ x, f x ∂(ENNReal.ofReal c • ν) :=
        integral_mono_measure hle (Eventually.of_forall hf0) h1
    _ = c * ∫ x, f x ∂ν := by rw [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]

include ha0 hb0 ha hb he hlam heig in
/-- **The truncated Moser step.** -/
theorem moser_step_δ {m : ℕ} (hm : 1 ≤ m) (hZ : Integrable (fun x => |e x| ^ (2 * m)) volume)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, Fδ δ m (e x) ^ 2 ≤ moserK ι a b lam m ^ (((m : ℝ) + 1) / m) *
      (∫ x, |e x| ^ (2 * m)) ^ ((2 * m + 1 : ℝ) / m) := by
  obtain ⟨hw, hwH, hwae⟩ := memH1_comp ha hb he (contDiff_Fδ hδ m) (abs_deriv_Fδ_le hδ m)
    (by simp [Fδ])
  set w : UnitAddTorus ι → ℝ := fun y => Fδ δ m (e y)
  set g : UnitAddTorus ι → ι → ℝ := fun y k => deriv (Fδ δ m) (e y) * weakGrad e y k
  set L := (1 / δ) ^ m * (1 + 2 * m)
  have hwL : MemLp w 2 volume := memLp_vol ha hwH
  have hgP : ∀ k, MemLp (fun y => g y k) 2 P := fun k => by
    refine ((memLp_grad_P hb he k).const_mul L).of_le
      ((((contDiff_Fδ hδ m).continuous_deriv le_rfl).comp_aestronglyMeasurable
        he.2.1.aestronglyMeasurable).mul (memLp_grad_P hb he k).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (show 0 ≤ L by positivity)]
    exact mul_le_mul_of_nonneg_right (abs_deriv_Fδ_le hδ m _) (abs_nonneg _)
  have hgV : ∀ k, MemLp (fun y => g y k) 2 volume := fun k =>
    (hgP k).of_measure_le_smul ENNReal.ofReal_ne_top ha
  set R := moserR a b lam m
  have hR : 1 ≤ R := Nat.le_add_left 1 _
  have hnash := nash_torus hw hwL hgV hR
  -- the gradient term
  set Y := ∫ x, w x ^ 2
  have hsq : ∀ y, ∑ j, g y j ^ 2 = sqNorm (g y) := fun y => rfl
  have hgsum : ∑ j, ∫ y, g y j ^ 2 = ∫ y, sqNorm (g y) := by
    unfold sqNorm; exact (integral_finsetSum _ fun j _ => (hgV j).integrable_sq).symm
  have hsqP : Integrable (fun y => sqNorm (g y)) P :=
    integrable_finsetSum _ fun j _ => (hgP j).integrable_sq
  have hwP : Integrable (fun y => w y ^ 2) P := hwH.2.1.integrable_sq
  have hen := moser_energy ha hb he heig hδ m
  have hgrad : ∫ y, sqNorm (g y) ≤ a * b * (1 + 2 * m) * lam * Y := by
    calc ∫ y, sqNorm (g y) ≤ a * ∫ y, sqNorm (g y) ∂P :=
          integral_le_smul_of_le ha0.le ha (fun y => sqNorm_nonneg _) hsqP
      _ ≤ a * ((1 + 2 * m) * lam * ∫ y, w y ^ 2 ∂P) :=
          mul_le_mul_of_nonneg_left hen ha0.le
      _ ≤ a * ((1 + 2 * m) * lam * (b * Y)) := by
          gcongr
          exact integral_le_smul_of_le hb0.le hb (fun y => sq_nonneg _) hwL.integrable_sq
      _ = a * b * (1 + 2 * m) * lam * Y := by ring
  have hY0 : 0 ≤ Y := integral_nonneg fun y => sq_nonneg _
  have hRA : a * b * (1 + 2 * m) * lam ≤ 2 * π ^ 2 * R ^ 2 := by
    have h1 : a * b * (1 + 2 * m) * lam ≤ R := by
      have := Nat.le_ceil (a * b * (1 + 2 * m) * lam)
      simp only [R, moserR]; push_cast; linarith
    have h2 : (R : ℝ) ≤ R ^ 2 := by
      have : (1 : ℝ) ≤ R := by exact_mod_cast hR
      nlinarith
    have h3 : (1 : ℝ) ≤ 2 * π ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith
  have hRpos : (0 : ℝ) < 4 * π ^ 2 * R ^ 2 := by
    have : (0 : ℝ) < R := by exact_mod_cast hR
    positivity
  have hhalf : (∑ j, ∫ y, g y j ^ 2) / (4 * π ^ 2 * R ^ 2) ≤ Y / 2 := by
    rw [hgsum, div_le_iff₀ hRpos]
    nlinarith
  have hYX : Y ≤ moserK ι a b lam m * (∫ y, |w y|) ^ 2 := by
    simp only [moserK]; linarith
  -- Hölder
  have hpt : ∀ x, |w x| ≤ |e x| ^ (2 * m + 1) := fun x => by
    have := Fδ_sq_le hδ m (e x)
    have h2 : |w x| ^ 2 ≤ (|e x| ^ (2 * m + 1)) ^ 2 := by
      rw [sq_abs, ← pow_mul, mul_comm, pow_mul, sq_abs]; exact this
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp h2
  have hX := holder_moser hm hwL.aestronglyMeasurable (memLp_vol ha he).aestronglyMeasurable hpt hZ
    hwL.integrable_sq
  have hZ0 : 0 ≤ ∫ x, |e x| ^ (2 * m) := integral_nonneg fun _ => by positivity
  have hK0 : 0 ≤ moserK ι a b lam m := by unfold moserK; positivity
  refine moser_absorb hY0 hK0 hZ0 hm (hYX.trans ?_)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (integral_nonneg fun _ => abs_nonneg _) hX 2) hK0

include ha0 hb0 ha hb he hlam heig in
/-- **One Moser step**: `∫|e|^{4m+2} ≤ K^{(m+1)/m} (∫|e|^{2m})^{(2m+1)/m}`. -/
theorem moser_step {m : ℕ} (hm : 1 ≤ m) (hZ : Integrable (fun x => |e x| ^ (2 * m)) volume) :
    Integrable (fun x => |e x| ^ (4 * m + 2)) volume ∧
      ∫ x, |e x| ^ (4 * m + 2) ≤ moserK ι a b lam m ^ (((m : ℝ) + 1) / m) *
        (∫ x, |e x| ^ (2 * m)) ^ ((2 * m + 1 : ℝ) / m) := by
  set B := moserK ι a b lam m ^ (((m : ℝ) + 1) / m) *
    (∫ x, |e x| ^ (2 * m)) ^ ((2 * m + 1 : ℝ) / m)
  have hem : AEStronglyMeasurable e volume := (memLp_vol ha he).aestronglyMeasurable
  have hpow : ∀ x, (e x ^ 2) ^ (2 * m + 1) = |e x| ^ (4 * m + 2) := fun x => by
    rw [← sq_abs, ← pow_mul]; ring_nf
  set f : ℕ → UnitAddTorus ι → ℝ≥0∞ := fun n x => ENNReal.ofReal (Fδ (1 / (n + 1)) m (e x) ^ 2)
  set F : UnitAddTorus ι → ℝ≥0∞ := fun x => ENNReal.ofReal (|e x| ^ (4 * m + 2))
  have hint_n : ∀ n : ℕ, Integrable (fun x => Fδ (1 / (n + 1)) m (e x) ^ 2) volume := fun n => by
    obtain ⟨-, hwH, -⟩ := memH1_comp ha hb he (contDiff_Fδ (δ := 1 / (n + 1)) (by positivity) m)
      (abs_deriv_Fδ_le (by positivity) m) (by simp [Fδ])
    exact (memLp_vol ha hwH).integrable_sq
  have hfn : ∀ n, ∫⁻ x, f n x ≤ ENNReal.ofReal B := fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint_n n)
      (Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (moser_step_δ ha0 hb0 ha hb he hlam heig hm hZ (by positivity))
  have hlim : Tendsto (fun n => ∫⁻ x, f n x) atTop (𝓝 (∫⁻ x, F x)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_)
      (Eventually.of_forall fun x a c hac => ENNReal.ofReal_le_ofReal
        (monotone_Fδ_sq m (e x) hac))
      (Eventually.of_forall fun x => ?_)
    · exact (hint_n n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    · have := (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_Fδ_sq m (e x))
      simp only [F, ← hpow]
      exact this
  have hF : ∫⁻ x, F x ≤ ENNReal.ofReal B := le_of_tendsto' hlim hfn
  have hFm : AEStronglyMeasurable (fun x => |e x| ^ (4 * m + 2)) volume :=
    (hem.norm.pow (4 * m + 2)).congr (Eventually.of_forall fun x => by simp)
  have hInt : Integrable (fun x => |e x| ^ (4 * m + 2)) volume := by
    refine ⟨hFm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => by positivity)]
    exact hF.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity)
    hFm]
  have hB0 : 0 ≤ B := by
    have : 0 ≤ moserK ι a b lam m := by unfold moserK; positivity
    positivity
  exact ENNReal.toReal_le_of_le_ofReal hB0 hF

end step

end SharpLSI
