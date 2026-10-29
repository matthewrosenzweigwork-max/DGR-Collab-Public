import Mathlib
import DGPS.Foundations.Entropy

/-!
# Anchored half-line resistance Poincare inequality (FIN006)

Let `μ(dx) = p(x) dx` be a probability measure on an open interval `I`, with `p > 0` continuous,
and let `a ∈ I` be an anchor (not necessarily a median). With the resistance `W(x) = ∫_a^x 1/p`
and the constants
`B_+ = sup_{x>a} μ([x,b)) ∫_a^x 1/p`, `B_- = sup_{x<a} μ((l,x]) ∫_x^a 1/p`,
we prove, for every absolutely continuous `f` of finite energy,
`∫ (f - f a)² dμ ≤ 4 max(B_+, B_-) ∫ |f'|² dμ` and the same bound for `Var_μ f`
(`anchored_half_line_resistance_poincare`).

The proof is a weighted Hardy (Muckenhoupt) argument with the Cauchy-Schwarz weight `√W`
(constant `1/(α(1-α)) = 4` at `α = 1/2`) on each side of `a`; the left side is obtained from the
right side by the reflection `x ↦ -x` (`hardy_core_left`).

Design notes: `I` is a general open order-connected subset of `ℝ`, `μ = densityMeasure I p`;
`μ([x,b))` is `μ (Ici x)` and `μ((l,x])` is `μ (Iic x)` (as `μ Iᶜ = 0`); `f` is absolutely
continuous in the sense `f y - f x = ∫_x^y f'` on `I` with `f'` locally integrable on `I`.

## Median logarithmic Hardy LSI criterion (FIN007)

At the end of the file, `median_logarithmic_hardy_lsi_criterion` bounds the homogeneous entropy
`Ent_μ(f²) ≤ 200 max(C_+, C_-) ∫ |f'|² dμ` for a median `m` of `μ`, where
`C_± = sup Ψ(μ(tail)) ∫ 1/p` with `Ψ(t) = t log (1 + 1/t)`. Proof: the weak Rothaus bound
`entropyIntegrand_sq_add_le`, the Gibbs variational step `homogeneousEntropy_le_ofReal_integral`,
the weight `w = log (1 + g²/G)` (Jensen bound `setIntegral_weight_le`) and the weighted Hardy
inequality `hardy_of_bounds_w`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace DGPS.FiniteN

lemma lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {F G : α → ℝ≥0∞}
    (hF : AEMeasurable F μ) (hG : AEMeasurable G μ) :
    (∫⁻ x, F x * G x ∂μ) ^ 2 ≤ (∫⁻ x, F x ^ 2 ∂μ) * ∫⁻ x, G x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hF hG
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ x, F x * G x ∂μ) ^ 2
      ≤ ((∫⁻ x, F x ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫⁻ x, G x ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2 :=
        pow_le_pow_left' h 2
    _ = (∫⁻ x, F x ^ 2 ∂μ) * ∫⁻ x, G x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast ((∫⁻ x, G x ^ 2 ∂μ) ^ (1 / (2:ℝ))),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

lemma setLIntegral_Ioi_inter_le {I : Set ℝ} (hIo : IsOpen I) (hIc : I.OrdConnected) {t : ℝ}
    (ht : t ∈ I) (F : ℝ → ℝ≥0∞) {C : ℝ≥0∞}
    (h : ∀ s ∈ I, t < s → ∫⁻ x in Ioc t s, F x ≤ C) : ∫⁻ x in I ∩ Ioi t, F x ≤ C := by
  let ι := {q : ℚ // (q : ℝ) ∈ I ∧ t < q}
  have hU : I ∩ Ioi t = ⋃ q : ι, Ioc t (q.1 : ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_iUnion, mem_Ioc]
    constructor
    · rintro ⟨hxI, hxt⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hIo x hxI
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < x + ε by linarith)
      refine ⟨⟨q, hball ?_, by linarith⟩, hxt, hq1.le⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    · rintro ⟨q, hxt, hxq⟩
      exact ⟨hIc.out ht q.2.1 ⟨hxt.le, hxq⟩, hxt⟩
  rw [hU]
  have hd : Directed (· ⊆ ·) (fun q : ι => Ioc t (q.1 : ℝ)) := by
    intro q r
    rcases le_total (q.1 : ℝ) r.1 with h1 | h1
    · exact ⟨r, Ioc_subset_Ioc_right h1, subset_rfl⟩
    · exact ⟨q, subset_rfl, Ioc_subset_Ioc_right h1⟩
  rw [setLIntegral_iUnion_of_directed _ hd]
  exact iSup_le fun q => h _ q.2.1 q.2.2


/-- The resistance integral `∫_a^x 1/p`. -/
noncomputable def resistance (p : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ t in a..x, (p t)⁻¹

section Resistance

variable {I : Set ℝ} {p : ℝ → ℝ} {a : ℝ}

lemma continuousOn_inv_density (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) :
    ContinuousOn (fun t => (p t)⁻¹) I :=
  hp.inv₀ fun t ht => (hp0 t ht).ne'

lemma hasDerivAt_resistance (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {x : ℝ} (hx : x ∈ I) :
    HasDerivAt (resistance p a) (p x)⁻¹ x := by
  have hc := continuousOn_inv_density hp hp0
  exact intervalIntegral.integral_hasDerivAt_right
    ((hc.mono (hIc.uIcc_subset ha hx)).intervalIntegrable)
    (hc.stronglyMeasurableAtFilter hIo x hx) (hc.continuousAt (hIo.mem_nhds hx))

lemma continuousOn_resistance (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) :
    ContinuousOn (resistance p a) I := fun _ hx =>
  (hasDerivAt_resistance hIo hIc ha hp hp0 hx).continuousAt.continuousWithinAt

lemma resistance_pos (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {x : ℝ} (hx : x ∈ I) (hax : a < x) :
    0 < resistance p a x := by
  have hc := continuousOn_inv_density hp hp0
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((hc.mono (hIc.uIcc_subset ha hx)).intervalIntegrable) (fun y hy => ?_) hax
  have hyI : y ∈ I := hIc.out ha hx ⟨hy.1.le, hy.2.le⟩
  exact inv_pos.2 (hp0 y hyI)

lemma integral_inv_mul_sqrt_resistance (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {x : ℝ} (hx : x ∈ I) (hax : a < x) :
    ∫ t in a..x, (p t * √(resistance p a t))⁻¹ = 2 * √(resistance p a x) := by
  have hW : ∀ y ∈ I, HasDerivAt (resistance p a) (p y)⁻¹ y :=
    fun y hy => hasDerivAt_resistance hIo hIc ha hp hp0 hy
  have hsub : Icc a x ⊆ I := hIc.out ha hx
  have hcont : ContinuousOn (fun y => 2 * √(resistance p a y)) (Icc a x) := by
    have : ContinuousOn (resistance p a) (Icc a x) :=
      (continuousOn_resistance hIo hIc ha hp hp0).mono hsub
    fun_prop
  have hder : ∀ y ∈ Ioo a x, HasDerivAt (fun y => 2 * √(resistance p a y))
      (p y * √(resistance p a y))⁻¹ y := by
    intro y hy
    have hyI : y ∈ I := hsub ⟨hy.1.le, hy.2.le⟩
    have hWy : 0 < resistance p a y := resistance_pos hIc ha hp hp0 hyI hy.1
    have := ((hW y hyI).sqrt hWy.ne').const_mul 2
    convert this using 1
    have := hp0 y hyI
    have h2 := Real.sqrt_pos.2 hWy
    field_simp
  have hint : IntervalIntegrable (fun y => (p y * √(resistance p a y))⁻¹) volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hax.le]
    refine intervalIntegral.integrableOn_deriv_of_nonneg hcont hder (fun y hy => ?_)
    have hyI : y ∈ I := hsub ⟨hy.1.le, hy.2.le⟩
    have := hp0 y hyI
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hax.le hcont hder hint]
  simp [resistance]

lemma tail_integral_le (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {T : ℝ → ℝ} {B : ℝ}
    (hT : ∀ x ∈ I, a < x → HasDerivAt T (-p x) x) (hT0 : ∀ x ∈ I, a < x → 0 ≤ T x)
    (hB : ∀ x ∈ I, a < x → T x * resistance p a x ≤ B)
    {t s : ℝ} (ht : t ∈ I) (hat : a < t) (hs : s ∈ I) (hts : t ≤ s) :
    ∫ x in t..s, p x * √(resistance p a x) ≤ 2 * B / √(resistance p a t) := by
  have hW : ∀ y ∈ I, HasDerivAt (resistance p a) (p y)⁻¹ y :=
    fun y hy => hasDerivAt_resistance hIo hIc ha hp hp0 hy
  have hsub : Icc t s ⊆ I := hIc.out ht hs
  have hWpos : ∀ x ∈ Icc t s, 0 < resistance p a x := fun x hx =>
    resistance_pos hIc ha hp hp0 (hsub hx) (lt_of_lt_of_le hat hx.1)
  set F : ℝ → ℝ := fun x => ∫ y in t..x, p y * √(resistance p a y) with hFdef
  have hcontg : ∀ x ∈ I, ContinuousAt (fun y => p y * √(resistance p a y)) x := by
    intro x hx
    exact (hp.continuousAt (hIo.mem_nhds hx)).mul
      ((hW x hx).continuousAt.sqrt)
  have hFd : ∀ x ∈ Icc t s, HasDerivAt F (p x * √(resistance p a x)) x := by
    intro x hx
    have hxI := hsub hx
    have hcg : ContinuousOn (fun y => p y * √(resistance p a y)) I := fun y hy =>
      (hcontg y hy).continuousWithinAt
    exact intervalIntegral.integral_hasDerivAt_right
      ((hcg.mono (hIc.uIcc_subset ht hxI)).intervalIntegrable)
      (hcg.stronglyMeasurableAtFilter hIo x hxI) (hcontg x hxI)
  set G : ℝ → ℝ := fun x => F s - F x - T x * √(resistance p a x)
    - B * (√(resistance p a x))⁻¹ with hGdef
  have hGd : ∀ x ∈ Icc t s, HasDerivAt G
      ((B - T x * resistance p a x) / (2 * p x * resistance p a x * √(resistance p a x))) x := by
    intro x hx
    have hxI := hsub hx
    have hxa : a < x := lt_of_lt_of_le hat hx.1
    have hWx := hWpos x hx
    have hS : 0 < √(resistance p a x) := Real.sqrt_pos.2 hWx
    have h1 := ((((hFd x hx).const_sub (F s)).sub
      ((hT x hxI hxa).mul ((hW x hxI).sqrt hWx.ne'))).sub
      ((((hW x hxI).sqrt hWx.ne').inv hS.ne').const_mul B))
    convert h1 using 1
    have hpx := hp0 x hxI
    have hsq : √(resistance p a x) ^ 2 = resistance p a x := Real.sq_sqrt hWx.le
    field_simp
    rw [hsq]
    ring
  have hmono : MonotoneOn G (Icc t s) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => (B - T x * resistance p a x) /
      (2 * p x * resistance p a x * √(resistance p a x))) (convex_Icc t s) ?_ ?_ ?_
    · exact fun x hx => (hGd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hGd x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Icc t s := ⟨hx.1.le, hx.2.le⟩
      have hxI := hsub hx'
      have hxa : a < x := lt_of_lt_of_le hat hx'.1
      have hWx := hWpos x hx'
      have hS : 0 < √(resistance p a x) := Real.sqrt_pos.2 hWx
      have := hp0 x hxI
      have := hB x hxI hxa
      apply div_nonneg (by linarith) (by positivity)
  have hGts : G t ≤ G s := hmono ⟨le_rfl, hts⟩ ⟨hts, le_rfl⟩ hts
  have hWt := hWpos t ⟨le_rfl, hts⟩
  have hWs := hWpos s ⟨hts, le_rfl⟩
  have hSt : 0 < √(resistance p a t) := Real.sqrt_pos.2 hWt
  have hSs : 0 < √(resistance p a s) := Real.sqrt_pos.2 hWs
  have hTt := hT0 t ht hat
  have hTs := hT0 s hs (lt_of_lt_of_le hat hts)
  have hBt := hB t ht hat
  have hB0 : 0 ≤ B := le_trans (mul_nonneg hTt hWt.le) hBt
  have hGs : G s ≤ 0 := by
    simp only [hGdef, sub_self, zero_sub]
    have : 0 ≤ T s * √(resistance p a s) := by positivity
    have : 0 ≤ B * (√(resistance p a s))⁻¹ := by positivity
    linarith
  have hFt : F t = 0 := by simp [hFdef]
  have h1 : F s ≤ T t * √(resistance p a t) + B * (√(resistance p a t))⁻¹ := by
    have := hGts.trans hGs
    simp only [hGdef, hFt] at this
    linarith
  have h2 : T t * √(resistance p a t) ≤ B * (√(resistance p a t))⁻¹ := by
    have hsq : √(resistance p a t) ^ 2 = resistance p a t := Real.sq_sqrt hWt.le
    rw [← div_eq_mul_inv, le_div_iff₀ hSt, mul_assoc, ← sq, hsq]
    exact hBt
  calc ∫ x in t..s, p x * √(resistance p a x) = F s := rfl
    _ ≤ 2 * B / √(resistance p a t) := by
      have : 2 * B / √(resistance p a t) = B * (√(resistance p a t))⁻¹ +
        B * (√(resistance p a t))⁻¹ := by ring
      rw [this]; linarith

end Resistance

section Core

variable {I : Set ℝ} {p : ℝ → ℝ} {a : ℝ}

lemma lintegral_inv_mul_sqrt_resistance (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {x : ℝ} (hx : x ∈ I) (hax : a < x) :
    ∫⁻ t in Ioo a x, ENNReal.ofReal ((p t * √(resistance p a t))⁻¹)
      = ENNReal.ofReal (2 * √(resistance p a x)) := by
  have hint : IntervalIntegrable (fun y => (p y * √(resistance p a y))⁻¹) volume a x := by
    have hW : ∀ y ∈ I, HasDerivAt (resistance p a) (p y)⁻¹ y :=
      fun y hy => hasDerivAt_resistance hIo hIc ha hp hp0 hy
    have hsub : Icc a x ⊆ I := hIc.out ha hx
    have hcont : ContinuousOn (fun y => 2 * √(resistance p a y)) (Icc a x) := by
      have : ContinuousOn (resistance p a) (Icc a x) :=
        (continuousOn_resistance hIo hIc ha hp hp0).mono hsub
      fun_prop
    have hder : ∀ y ∈ Ioo a x, HasDerivAt (fun y => 2 * √(resistance p a y))
        (p y * √(resistance p a y))⁻¹ y := by
      intro y hy
      have hyI : y ∈ I := hsub ⟨hy.1.le, hy.2.le⟩
      have hWy : 0 < resistance p a y := resistance_pos hIc ha hp hp0 hyI hy.1
      have := ((hW y hyI).sqrt hWy.ne').const_mul 2
      convert this using 1
      have := hp0 y hyI
      have h2 := Real.sqrt_pos.2 hWy
      field_simp
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hax.le]
    refine intervalIntegral.integrableOn_deriv_of_nonneg hcont hder (fun y hy => ?_)
    have hyI : y ∈ I := hsub ⟨hy.1.le, hy.2.le⟩
    have := hp0 y hyI
    positivity
  have hI : IntegrableOn (fun y => (p y * √(resistance p a y))⁻¹) (Ioo a x) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hax.le).1 hint).mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hI]
  · congr 1
    rw [← integral_inv_mul_sqrt_resistance hIo hIc ha hp hp0 hx hax,
      intervalIntegral.integral_of_le hax.le, integral_Ioc_eq_integral_Ioo]
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hyI : y ∈ I := hIc.out ha hx ⟨hy.1.le, hy.2.le⟩
    have := hp0 y hyI
    have := Real.sqrt_nonneg (resistance p a y)
    positivity

lemma continuousOn_density_sqrt (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) :
    ContinuousOn (fun t => p t * √(resistance p a t)) I := by
  have := continuousOn_resistance hIo hIc ha hp hp0
  fun_prop

lemma pointwise_cs (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {g u : ℝ → ℝ}
    (hg : AEMeasurable g (volume.restrict (I ∩ Ioi a)))
    (hug : ∀ x ∈ I, a < x → ‖u x‖ₑ ≤ ∫⁻ t in Ioo a x, ‖g t‖ₑ) {x : ℝ} (hx : x ∈ I) (hax : a < x) :
    ENNReal.ofReal (u x ^ 2 * p x) ≤ ENNReal.ofReal (p x * (2 * √(resistance p a x))) *
      ∫⁻ t in Ioo a x, ENNReal.ofReal (g t ^ 2 * p t * √(resistance p a t)) := by
  have hsub : Ioo a x ⊆ I ∩ Ioi a := fun t ht =>
    ⟨hIc.out ha hx ⟨ht.1.le, ht.2.le⟩, ht.1⟩
  have hIsub : Ioo a x ⊆ I := fun t ht => (hsub ht).1
  have hg' : AEMeasurable g (volume.restrict (Ioo a x)) :=
    hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  set q : ℝ → ℝ := fun t => p t * √(resistance p a t) with hq
  have hqc : ContinuousOn q (Ioo a x) :=
    (continuousOn_density_sqrt hIo hIc ha hp hp0).mono hIsub
  have hqpos : ∀ t ∈ Ioo a x, 0 < q t := fun t ht =>
    mul_pos (hp0 t (hIsub ht)) (Real.sqrt_pos.2 (resistance_pos hIc ha hp hp0 (hIsub ht) ht.1))
  have hsq : ContinuousOn (fun t => √(q t)) (Ioo a x) := hqc.sqrt
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (|g t| * √(q t)) with hF
  set G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (√(q t))⁻¹ with hG
  have hFm : AEMeasurable F (volume.restrict (Ioo a x)) :=
    (hg'.abs.mul (hsq.aemeasurable measurableSet_Ioo)).ennreal_ofReal
  have hGm : AEMeasurable G (volume.restrict (Ioo a x)) := by
    have : ContinuousOn (fun t => (√(q t))⁻¹) (Ioo a x) :=
      hsq.inv₀ fun t ht => (Real.sqrt_pos.2 (hqpos t ht)).ne'
    exact (this.aemeasurable measurableSet_Ioo).ennreal_ofReal
  have hFG : ∀ t ∈ Ioo a x, ‖g t‖ₑ = F t * G t := by
    intro t ht
    have h1 := Real.sqrt_pos.2 (hqpos t ht)
    simp only [hF, hG, ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) h1.le),
      Real.enorm_eq_ofReal_abs]
    congr 1
    field_simp
  have hF2 : ∀ t ∈ Ioo a x, F t ^ 2 =
      ENNReal.ofReal (g t ^ 2 * p t * √(resistance p a t)) := by
    intro t ht
    simp only [hF, ← ENNReal.ofReal_pow (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))]
    congr 1
    rw [mul_pow, sq_abs, Real.sq_sqrt (hqpos t ht).le]
    simp only [hq]
    ring
  have hG2 : ∀ t ∈ Ioo a x, G t ^ 2 = ENNReal.ofReal ((p t * √(resistance p a t))⁻¹) := by
    intro t ht
    have h1 := Real.sqrt_pos.2 (hqpos t ht)
    simp only [hG, ← ENNReal.ofReal_pow (inv_nonneg.2 h1.le)]
    congr 1
    rw [inv_pow, Real.sq_sqrt (hqpos t ht).le]
  have hcs := lintegral_mul_sq_le (volume.restrict (Ioo a x)) hFm hGm
  have e1 : ∫⁻ t in Ioo a x, ‖g t‖ₑ = ∫⁻ t in Ioo a x, F t * G t :=
    setLIntegral_congr_fun measurableSet_Ioo hFG
  have e2 : ∫⁻ t in Ioo a x, F t ^ 2 =
      ∫⁻ t in Ioo a x, ENNReal.ofReal (g t ^ 2 * p t * √(resistance p a t)) :=
    setLIntegral_congr_fun measurableSet_Ioo hF2
  have e3 : ∫⁻ t in Ioo a x, G t ^ 2 = ENNReal.ofReal (2 * √(resistance p a x)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioo hG2]
    exact lintegral_inv_mul_sqrt_resistance hIo hIc ha hp hp0 hx hax
  have hu := hug x hx hax
  rw [e1] at hu
  have hu2 : ‖u x‖ₑ ^ 2 ≤ (∫⁻ t in Ioo a x, F t * G t) ^ 2 := pow_le_pow_left' hu 2
  rw [e2, e3] at hcs
  have hpx : 0 ≤ p x := (hp0 x hx).le
  calc ENNReal.ofReal (u x ^ 2 * p x) = ‖u x‖ₑ ^ 2 * ENNReal.ofReal (p x) := by
        rw [ENNReal.ofReal_mul (sq_nonneg _), Real.enorm_eq_ofReal_abs,
          ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    _ ≤ (∫⁻ t in Ioo a x, F t * G t) ^ 2 * ENNReal.ofReal (p x) := by gcongr
    _ ≤ ((∫⁻ t in Ioo a x, ENNReal.ofReal (g t ^ 2 * p t * √(resistance p a t))) *
          ENNReal.ofReal (2 * √(resistance p a x))) * ENNReal.ofReal (p x) := by gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul hpx]
        ring

lemma lintegral_tail_le (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {T : ℝ → ℝ} {B : ℝ}
    (hT : ∀ x ∈ I, a < x → HasDerivAt T (-p x) x) (hT0 : ∀ x ∈ I, a < x → 0 ≤ T x)
    (hB : ∀ x ∈ I, a < x → T x * resistance p a x ≤ B) {t : ℝ} (ht : t ∈ I) (hat : a < t) :
    ∫⁻ x in I ∩ Ioi t, ENNReal.ofReal (p x * (2 * √(resistance p a x)))
      ≤ ENNReal.ofReal (4 * B / √(resistance p a t)) := by
  refine setLIntegral_Ioi_inter_le hIo hIc ht _ fun s hs hts => ?_
  have hsub : Icc t s ⊆ I := hIc.out ht hs
  have hc : ContinuousOn (fun x => p x * (2 * √(resistance p a x))) (Icc t s) := by
    have := (continuousOn_resistance hIo hIc ha hp hp0).mono hsub
    have := hp.mono hsub
    fun_prop
  have hint : IntegrableOn (fun x => p x * (2 * √(resistance p a x))) (Ioc t s) volume :=
    (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [← intervalIntegral.integral_of_le hts.le]
    have h1 := tail_integral_le hIo hIc ha hp hp0 hT hT0 hB ht hat hs hts.le
    have : ∫ x in t..s, p x * (2 * √(resistance p a x)) =
        2 * ∫ x in t..s, p x * √(resistance p a x) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext x; ring
    rw [this]
    calc 2 * ∫ x in t..s, p x * √(resistance p a x) ≤ 2 * (2 * B / √(resistance p a t)) := by
          gcongr
      _ = 4 * B / √(resistance p a t) := by ring
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hyI : y ∈ I := hsub ⟨hy.1.le, hy.2⟩
    have := hp0 y hyI
    positivity

/-- The right half-line Hardy inequality with the constant `4 B`. -/
theorem hardy_core (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {T : ℝ → ℝ} {B : ℝ}
    (hT : ∀ x ∈ I, a < x → HasDerivAt T (-p x) x) (hT0 : ∀ x ∈ I, a < x → 0 ≤ T x)
    (hB : ∀ x ∈ I, a < x → T x * resistance p a x ≤ B) {g u : ℝ → ℝ}
    (hg : AEMeasurable g (volume.restrict (I ∩ Ioi a)))
    (hug : ∀ x ∈ I, a < x → ‖u x‖ₑ ≤ ∫⁻ t in Ioo a x, ‖g t‖ₑ) :
    ∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (u x ^ 2 * p x) ≤
      ENNReal.ofReal (4 * B) * ∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (g x ^ 2 * p x) := by
  set R : Set ℝ := I ∩ Ioi a with hR
  have hRm : MeasurableSet R := hIo.measurableSet.inter measurableSet_Ioi
  set Φ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (g t ^ 2 * p t * √(resistance p a t)) with hΦ
  set h : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (p x * (2 * √(resistance p a x))) with hh
  have hRI : ∀ x ∈ R, x ∈ I ∧ a < x := fun x hx => hx
  -- Step 1: pointwise bound
  have step1 : ∫⁻ x in R, ENNReal.ofReal (u x ^ 2 * p x) ≤
      ∫⁻ x in R, h x * ∫⁻ t in Ioo a x, Φ t :=
    setLIntegral_mono' hRm fun x hx =>
      pointwise_cs hIo hIc ha hp hp0 hg hug hx.1 hx.2
  -- measurability
  have hpm : AEMeasurable (fun x => p x) (volume.restrict R) :=
    (hp.mono inter_subset_left).aemeasurable hRm
  have hWc : ContinuousOn (resistance p a) R :=
    (continuousOn_resistance hIo hIc ha hp hp0).mono inter_subset_left
  have hhm : AEMeasurable h (volume.restrict R) := by
    have : ContinuousOn (fun x => p x * (2 * √(resistance p a x))) R := by
      have := hp.mono (inter_subset_left : R ⊆ I)
      fun_prop
    exact (this.aemeasurable hRm).ennreal_ofReal
  have hΦm : AEMeasurable Φ (volume.restrict R) := by
    have : ContinuousOn (fun x => p x * √(resistance p a x)) R :=
      (continuousOn_density_sqrt hIo hIc ha hp hp0).mono inter_subset_left
    have h2 := (hg.pow_const 2).mul ((this.aemeasurable hRm))
    refine h2.ennreal_ofReal.congr ?_
    exact Filter.Eventually.of_forall fun t => by
      simp only [hΦ, Pi.mul_apply]; congr 1; ring
  -- Step 2: Tonelli
  let K : ℝ × ℝ → ℝ≥0∞ := {z : ℝ × ℝ | z.2 < z.1}.indicator fun z => h z.1 * Φ z.2
  have hKm : AEMeasurable K ((volume.restrict R).prod (volume.restrict R)) := by
    have h1 : AEMeasurable (fun z : ℝ × ℝ => h z.1) ((volume.restrict R).prod (volume.restrict R)) :=
      hhm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : AEMeasurable (fun z : ℝ × ℝ => Φ z.2) ((volume.restrict R).prod (volume.restrict R)) :=
      hΦm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have : AEMeasurable (fun z : ℝ × ℝ => h z.1 * Φ z.2)
        ((volume.restrict R).prod (volume.restrict R)) := h1.mul h2
    exact this.indicator (measurableSet_lt measurable_snd measurable_fst)
  have step2 : ∫⁻ x in R, h x * ∫⁻ t in Ioo a x, Φ t = ∫⁻ x in R, ∫⁻ t in R, K (x, t) := by
    refine setLIntegral_congr_fun hRm fun x hx => ?_
    have hset : (Ioo a x) = Iio x ∩ R := by
      ext t
      simp only [hR, mem_Ioo, mem_inter_iff, mem_Ioi, mem_Iio]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, ⟨hIc.out ha hx.1 ⟨h1.le, h2.le⟩, h1⟩⟩
      · rintro ⟨h2, ⟨_, h1⟩⟩; exact ⟨h1, h2⟩
    have hK : ∀ t, K (x, t) = (Iio x).indicator (fun t => h x * Φ t) t := by
      intro t
      simp only [K, Set.indicator, mem_ofPred_eq, mem_Iio]
    simp_rw [hK]
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      ← hset, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have step3 : ∀ t ∈ R, ∫⁻ x in R, K (x, t) ≤ ENNReal.ofReal (4 * B) *
      ENNReal.ofReal (g t ^ 2 * p t) := by
    intro t ht
    obtain ⟨htI, hat⟩ := ht
    have hKt : ∀ x, K (x, t) = (Ioi t).indicator (fun x => h x * Φ t) x := by
      intro x
      simp only [K, Set.indicator, mem_ofPred_eq, mem_Ioi]
    simp_rw [hKt]
    have hset : Ioi t ∩ R = I ∩ Ioi t := by
      ext x
      simp only [hR, mem_inter_iff, mem_Ioi]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, lt_trans hat h1⟩
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hset,
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    have hWt : 0 < resistance p a t := resistance_pos hIc ha hp hp0 htI hat
    have hS : 0 < √(resistance p a t) := Real.sqrt_pos.2 hWt
    have hB0 : 0 ≤ B := le_trans (mul_nonneg (hT0 t htI hat) hWt.le) (hB t htI hat)
    have hpt := hp0 t htI
    calc (∫⁻ x in I ∩ Ioi t, h x) * Φ t
        ≤ ENNReal.ofReal (4 * B / √(resistance p a t)) * Φ t := by
          gcongr
          exact lintegral_tail_le hIo hIc ha hp hp0 hT hT0 hB htI hat
      _ = _ := by
          simp only [hΦ]
          rw [mul_comm, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  calc ∫⁻ x in R, ENNReal.ofReal (u x ^ 2 * p x)
      ≤ ∫⁻ x in R, h x * ∫⁻ t in Ioo a x, Φ t := step1
    _ = ∫⁻ x in R, ∫⁻ t in R, K (x, t) := step2
    _ = ∫⁻ t in R, ∫⁻ x in R, K (x, t) := lintegral_lintegral_swap hKm
    _ ≤ ∫⁻ t in R, ENNReal.ofReal (4 * B) * ENNReal.ofReal (g t ^ 2 * p t) :=
        setLIntegral_mono' hRm step3
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Core

section Measure

variable {I : Set ℝ} {p : ℝ → ℝ} {a : ℝ}

/-- The measure `μ(dx) = p(x) dx` carried by the interval `I`. -/
noncomputable def densityMeasure (I : Set ℝ) (p : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict I).withDensity fun x => ENNReal.ofReal (p x)

lemma densityMeasure_apply {s : Set ℝ} (hs : MeasurableSet s)
    (hsI : s ⊆ I) :
    densityMeasure I p s = ∫⁻ x in s, ENNReal.ofReal (p x) := by
  rw [densityMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs,
    inter_eq_left.2 hsI]

lemma densityMeasure_Ioc (hIc : I.OrdConnected)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I)
    (hxy : x ≤ y) :
    densityMeasure I p (Ioc x y) = ENNReal.ofReal (∫ t in x..y, p t) := by
  have hsub : Icc x y ⊆ I := hIc.out hx hy
  rw [densityMeasure_apply measurableSet_Ioc (Ioc_subset_Icc_self.trans hsub)]
  have hint : IntegrableOn p (Ioc x y) volume :=
    ((hp.mono hsub).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint, intervalIntegral.integral_of_le hxy]
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
  exact (hp0 t (hsub ⟨ht.1.le, ht.2⟩)).le

lemma densityMeasure_Ico (hIc : I.OrdConnected)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I)
    (hxy : x ≤ y) :
    densityMeasure I p (Ico x y) = ENNReal.ofReal (∫ t in x..y, p t) := by
  have hsub : Icc x y ⊆ I := hIc.out hx hy
  rw [densityMeasure_apply measurableSet_Ico (Ico_subset_Icc_self.trans hsub)]
  have hint : IntegrableOn p (Ico x y) volume :=
    ((hp.mono hsub).integrableOn_Icc).mono_set Ico_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint, intervalIntegral.integral_of_le hxy,
    integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine (ae_restrict_iff' measurableSet_Ico).2 (Filter.Eventually.of_forall fun t ht => ?_)
  exact (hp0 t (hsub ⟨ht.1, ht.2.le⟩)).le

lemma densityMeasure_Ici_toReal (hIc : I.OrdConnected)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x)
    [IsFiniteMeasure (densityMeasure I p)] (ha : a ∈ I) {x : ℝ} (hx : x ∈ I) (hax : a ≤ x) :
    (densityMeasure I p (Ici x)).toReal =
      (densityMeasure I p (Ici a)).toReal - ∫ t in a..x, p t := by
  have hsub : Icc a x ⊆ I := hIc.out ha hx
  have hU : densityMeasure I p (Ici a) =
      densityMeasure I p (Ico a x) + densityMeasure I p (Ici x) := by
    rw [← measure_union _ measurableSet_Ici, Ico_union_Ici_eq_Ici hax]
    exact Set.disjoint_left.2 fun t h1 h2 => absurd h1.2 (not_lt.2 h2)
  rw [hU, densityMeasure_Ico hIc hp hp0 ha hx hax, ENNReal.toReal_add ENNReal.ofReal_ne_top
    (measure_ne_top _ _), ENNReal.toReal_ofReal]
  · ring
  · exact intervalIntegral.integral_nonneg hax fun t ht => (hp0 t (hsub ht)).le

lemma densityMeasure_Iic_toReal (hIc : I.OrdConnected)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x)
    [IsFiniteMeasure (densityMeasure I p)] (ha : a ∈ I) {x : ℝ} (hx : x ∈ I) (hxa : x ≤ a) :
    (densityMeasure I p (Iic x)).toReal =
      (densityMeasure I p (Iic a)).toReal - ∫ t in x..a, p t := by
  have hsub : Icc x a ⊆ I := hIc.out hx ha
  have hU : densityMeasure I p (Iic a) =
      densityMeasure I p (Iic x) + densityMeasure I p (Ioc x a) := by
    rw [← measure_union _ measurableSet_Ioc, Iic_union_Ioc_eq_Iic hxa]
    exact Set.disjoint_left.2 fun t h1 h2 => absurd h1 (not_le.2 h2.1)
  rw [hU, densityMeasure_Ioc hIc hp hp0 hx ha hxa, ENNReal.toReal_add (measure_ne_top _ _)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal]
  · ring
  · exact intervalIntegral.integral_nonneg hxa fun t ht => (hp0 t (hsub ht)).le

lemma hasDerivAt_tail_right (hIo : IsOpen I) (hIc : I.OrdConnected)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x)
    [IsFiniteMeasure (densityMeasure I p)] (ha : a ∈ I) {x : ℝ} (hx : x ∈ I) (hax : a < x) :
    HasDerivAt (fun z => (densityMeasure I p (Ici z)).toReal) (-p x) x := by
  have hc : ContinuousOn p I := hp
  have hH : HasDerivAt (fun z => ∫ t in a..z, p t) (p x) x :=
    intervalIntegral.integral_hasDerivAt_right
      ((hc.mono (hIc.uIcc_subset ha hx)).intervalIntegrable)
      (hc.stronglyMeasurableAtFilter hIo x hx) (hc.continuousAt (hIo.mem_nhds hx))
  have h1 := hH.const_sub (densityMeasure I p (Ici a)).toReal
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hIo.mem_nhds hx, Ioi_mem_nhds hax] with z hz hz2
  exact densityMeasure_Ici_toReal hIc hp hp0 ha hz (le_of_lt hz2)

lemma hasDerivAt_tail_left (hIo : IsOpen I) (hIc : I.OrdConnected)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x)
    [IsFiniteMeasure (densityMeasure I p)] (ha : a ∈ I) {y : ℝ} (hy : -y ∈ I) (hya : -y < a) :
    HasDerivAt (fun z => (densityMeasure I p (Iic (-z))).toReal) (-p (-y)) y := by
  have hH : HasDerivAt (fun w => ∫ t in a..w, p t) (p (-y)) (-y) :=
    intervalIntegral.integral_hasDerivAt_right
      ((hp.mono (hIc.uIcc_subset ha hy)).intervalIntegrable)
      (hp.stronglyMeasurableAtFilter hIo (-y) hy) (hp.continuousAt (hIo.mem_nhds hy))
  have h2 : HasDerivAt (fun z : ℝ => -z) (-1) y := hasDerivAt_neg y
  have h3 := (hH.comp y h2).const_add (densityMeasure I p (Iic a)).toReal
  have h4 : HasDerivAt (fun z => (densityMeasure I p (Iic a)).toReal +
      (fun w => ∫ t in a..w, p t) (-z)) (-p (-y)) y := by
    have h5 := h3
    rw [mul_neg_one] at h5
    exact h5
  refine h4.congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun z : ℝ => -z) y := continuous_neg.continuousAt
  filter_upwards [hc.preimage_mem_nhds (hIo.mem_nhds hy),
    hc.preimage_mem_nhds (Iio_mem_nhds hya)] with z hz hz2
  have := densityMeasure_Iic_toReal hIc hp hp0 ha (x := -z) hz (le_of_lt hz2)
  simp only [this]
  rw [intervalIntegral.integral_symm]; ring

end Measure

section Reflection

variable {I : Set ℝ} {p : ℝ → ℝ} {a : ℝ}

lemma neg_measurePreserving_restrict (s : Set ℝ) :
    MeasurePreserving (fun x : ℝ => -x) (volume.restrict (Neg.neg ⁻¹' s)) (volume.restrict s) :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding s

lemma setLIntegral_comp_neg (f : ℝ → ℝ≥0∞) (s : Set ℝ) :
    ∫⁻ x in Neg.neg ⁻¹' s, f (-x) = ∫⁻ x in s, f x :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding f s

/-- The left half-line Hardy inequality with the constant `4 B`, by reflection. The auxiliary
function `T` is given through its reflection `z ↦ T (-z)`. -/
theorem hardy_core_left (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {T : ℝ → ℝ} {B : ℝ}
    (hT : ∀ y : ℝ, -y ∈ I → -y < a → HasDerivAt (fun z => T (-z)) (-p (-y)) y)
    (hT0 : ∀ x ∈ I, x < a → 0 ≤ T x)
    (hB : ∀ x ∈ I, x < a → T x * ∫ t in x..a, (p t)⁻¹ ≤ B) {g u : ℝ → ℝ}
    (hg : AEMeasurable g (volume.restrict (I ∩ Iio a)))
    (hug : ∀ x ∈ I, x < a → ‖u x‖ₑ ≤ ∫⁻ t in Ioo x a, ‖g t‖ₑ) :
    ∫⁻ x in I ∩ Iio a, ENNReal.ofReal (u x ^ 2 * p x) ≤
      ENNReal.ofReal (4 * B) * ∫⁻ x in I ∩ Iio a, ENNReal.ofReal (g x ^ 2 * p x) := by
  set I' : Set ℝ := Neg.neg ⁻¹' I with hI'
  have hI'o : IsOpen I' := hIo.preimage continuous_neg
  have hI'c : I'.OrdConnected := hIc.preimage_anti (fun _ _ h => neg_le_neg h)
  have ha' : -a ∈ I' := by simpa [hI'] using ha
  have hp' : ContinuousOn (fun x => p (-x)) I' :=
    hp.comp continuous_neg.continuousOn (fun x hx => hx)
  have hp0' : ∀ x ∈ I', 0 < p (-x) := fun x hx => hp0 _ hx
  have hres : ∀ y, resistance (fun x => p (-x)) (-a) y = ∫ t in -y..a, (p t)⁻¹ := by
    intro y
    unfold resistance
    rw [intervalIntegral.integral_comp_neg (fun t => (p t)⁻¹), neg_neg]
  have hset : I' ∩ Ioi (-a) = Neg.neg ⁻¹' (I ∩ Iio a) := by
    ext x; simp only [mem_inter_iff, mem_Ioi, mem_preimage, mem_Iio, hI']
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  have key := hardy_core (I := I') (p := fun x => p (-x)) (a := -a) (T := fun z => T (-z)) (B := B)
    (g := fun t => g (-t)) (u := fun x => u (-x)) hI'o hI'c ha' hp' hp0'
    (fun x hx hax => hT x hx (by linarith))
    (fun x hx hax => hT0 _ hx (by linarith))
    (fun x hx hax => by
      rw [hres]; exact hB _ hx (by linarith))
    (by
      rw [hset]
      exact hg.comp_quasiMeasurePreserving
        (neg_measurePreserving_restrict _).quasiMeasurePreserving)
    (fun x hx hax => by
      refine (hug (-x) hx (by linarith)).trans (le_of_eq ?_)
      have : Ioo (-a) x = Neg.neg ⁻¹' Ioo (-x) a := by
        ext z; simp only [mem_Ioo, mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      rw [this]
      exact (setLIntegral_comp_neg (fun t => ‖g t‖ₑ) (Ioo (-x) a)).symm)
  rw [hset] at key
  have e1 := setLIntegral_comp_neg (fun x => ENNReal.ofReal (u x ^ 2 * p x)) (I ∩ Iio a)
  have e2 := setLIntegral_comp_neg (fun x => ENNReal.ofReal (g x ^ 2 * p x)) (I ∩ Iio a)
  rw [e1, e2] at key
  exact key

end Reflection

section Function

variable {I : Set ℝ} {p : ℝ → ℝ} {a : ℝ} {f f' : ℝ → ℝ}

lemma continuousOn_of_ftc (hIo : IsOpen I)
    (hf : ∀ x ∈ I, ∀ y ∈ I, f y - f x = ∫ t in x..y, f' t)
    (hf' : LocallyIntegrableOn f' I volume) : ContinuousOn f I := by
  intro y hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hIo y hy
  have hsub : Icc (y - ε / 2) (y + ε / 2) ⊆ I := fun z hz =>
    hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2])
  have hc : y - ε / 2 ≤ y + ε / 2 := by linarith
  have hint : IntervalIntegrable f' volume (y - ε / 2) (y + ε / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc]
    exact hf'.integrableOn_compact_subset hsub isCompact_Icc
  have hcont := intervalIntegral.continuousOn_primitive_interval' hint
    (a := y - ε / 2) (by rw [uIcc_of_le hc]; exact left_mem_Icc.2 hc)
  have hcI : y - ε / 2 ∈ I := hsub (left_mem_Icc.2 hc)
  have hEq : ContinuousOn f (Icc (y - ε / 2) (y + ε / 2)) := by
    have : ContinuousOn (fun b => f (y - ε / 2) + ∫ t in (y - ε / 2)..b, f' t)
        (Icc (y - ε / 2) (y + ε / 2)) := by
      rw [uIcc_of_le hc] at hcont
      exact continuousOn_const.add hcont
    refine this.congr fun b hb => ?_
    have := hf _ hcI b (hsub hb)
    linarith
  exact (hEq.continuousAt (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt

lemma enorm_sub_le_lintegral
    (hf : ∀ x ∈ I, ∀ y ∈ I, f y - f x = ∫ t in x..y, f' t) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I)
    (hxy : x ≤ y) : ‖f y - f x‖ₑ ≤ ∫⁻ t in Ioo x y, ‖f' t‖ₑ := by
  rw [hf x hx y hy, intervalIntegral.integral_of_le hxy]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  exact (setLIntegral_congr Ioo_ae_eq_Ioc).symm

lemma lintegral_densityMeasure_sq (hIo : IsOpen I) (hp : ContinuousOn p I) {G : ℝ → ℝ}
    (hG : AEMeasurable G (volume.restrict I)) :
    ∫⁻ x, ENNReal.ofReal (G x ^ 2) ∂(densityMeasure I p) =
      ∫⁻ x in I, ENNReal.ofReal (G x ^ 2 * p x) := by
  have hρ : AEMeasurable (fun x => ENNReal.ofReal (p x)) (volume.restrict I) :=
    (hp.aemeasurable hIo.measurableSet).ennreal_ofReal
  have hg : AEMeasurable (fun x => ENNReal.ofReal (G x ^ 2)) (volume.restrict I) :=
    ((hG.pow_const 2)).ennreal_ofReal
  rw [densityMeasure, lintegral_withDensity_eq_lintegral_mul₀ hρ hg]
  refine setLIntegral_congr_fun hIo.measurableSet fun x _ => ?_
  rw [Pi.mul_apply, mul_comm, ← ENNReal.ofReal_mul (sq_nonneg _)]

/-- Explicit-constant form of the anchored Hardy inequality (lintegral form). -/
theorem hardy_of_bounds (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x)
    [IsFiniteMeasure (densityMeasure I p)] {B₁ B₂ : ℝ}
    (hB₁ : ∀ x ∈ I, a < x →
      (densityMeasure I p (Ici x)).toReal * ∫ t in a..x, (p t)⁻¹ ≤ B₁)
    (hB₂ : ∀ x ∈ I, x < a →
      (densityMeasure I p (Iic x)).toReal * ∫ t in x..a, (p t)⁻¹ ≤ B₂)
    (hf : ∀ x ∈ I, ∀ y ∈ I, f y - f x = ∫ t in x..y, f' t)
    (hf' : LocallyIntegrableOn f' I volume) :
    ∫⁻ x, ENNReal.ofReal ((f x - f a) ^ 2) ∂(densityMeasure I p) ≤
      ENNReal.ofReal (4 * max B₁ B₂) *
        ∫⁻ x, ENNReal.ofReal (f' x ^ 2) ∂(densityMeasure I p) := by
  have hfc := continuousOn_of_ftc hIo hf hf'
  have hu : AEMeasurable (fun x => f x - f a) (volume.restrict I) :=
    ((hfc.sub continuousOn_const).aemeasurable hIo.measurableSet)
  have hg : AEMeasurable f' (volume.restrict I) := hf'.aestronglyMeasurable.aemeasurable
  rw [lintegral_densityMeasure_sq hIo hp hu, lintegral_densityMeasure_sq hIo hp hg]
  have hR := hardy_core hIo hIc ha hp hp0 (T := fun z => (densityMeasure I p (Ici z)).toReal)
    (B := B₁) (g := f') (u := fun x => f x - f a)
    (fun x hx hax => hasDerivAt_tail_right hIo hIc hp hp0 ha hx hax)
    (fun x _ _ => ENNReal.toReal_nonneg) hB₁ (hg.mono_set inter_subset_left)
    (fun x hx hax => enorm_sub_le_lintegral hf ha hx hax.le)
  have hL := hardy_core_left hIo hIc ha hp hp0 (T := fun z => (densityMeasure I p (Iic z)).toReal)
    (B := B₂) (g := f') (u := fun x => f x - f a)
    (fun y hy hya => hasDerivAt_tail_left hIo hIc hp hp0 ha hy hya)
    (fun x _ _ => ENNReal.toReal_nonneg) hB₂ (hg.mono_set inter_subset_left)
    (fun x hx hxa => by
      rw [← enorm_neg, neg_sub]
      exact enorm_sub_le_lintegral hf hx ha hxa.le)
  have hdisj : Disjoint (I ∩ Iio a) (I ∩ Ioi a) :=
    Set.disjoint_left.2 fun x h1 h2 => lt_asymm (show x < a from h1.2) (show a < x from h2.2)
  have hmeasR : MeasurableSet (I ∩ Ioi a) := hIo.measurableSet.inter measurableSet_Ioi
  have hcov : I ⊆ ((I ∩ Iio a) ∪ (I ∩ Ioi a)) ∪ {a} := by
    intro x hx
    rcases lt_trichotomy x a with h | h | h
    · exact Or.inl (Or.inl ⟨hx, h⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨hx, h⟩)
  have hS : ∫⁻ x in I, ENNReal.ofReal ((f x - f a) ^ 2 * p x) ≤
      (∫⁻ x in I ∩ Iio a, ENNReal.ofReal ((f x - f a) ^ 2 * p x)) +
        (∫⁻ x in I ∩ Ioi a, ENNReal.ofReal ((f x - f a) ^ 2 * p x)) := by
    calc _ ≤ ∫⁻ x in ((I ∩ Iio a) ∪ (I ∩ Ioi a)) ∪ {a},
            ENNReal.ofReal ((f x - f a) ^ 2 * p x) := lintegral_mono_set hcov
      _ ≤ (∫⁻ x in (I ∩ Iio a) ∪ (I ∩ Ioi a), ENNReal.ofReal ((f x - f a) ^ 2 * p x)) +
            ∫⁻ x in ({a} : Set ℝ), ENNReal.ofReal ((f x - f a) ^ 2 * p x) :=
          lintegral_union_le _ _ _
      _ ≤ _ := by
          rw [setLIntegral_measure_zero ({a} : Set ℝ) _ (measure_singleton a), add_zero]
          exact lintegral_union_le _ _ _
  have hT : (∫⁻ x in I ∩ Iio a, ENNReal.ofReal (f' x ^ 2 * p x)) +
        (∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (f' x ^ 2 * p x)) ≤
      ∫⁻ x in I, ENNReal.ofReal (f' x ^ 2 * p x) := by
    rw [← lintegral_union hmeasR hdisj]
    exact lintegral_mono_set (union_subset inter_subset_left inter_subset_left)
  have hM₁ : ENNReal.ofReal (4 * B₁) ≤ ENNReal.ofReal (4 * max B₁ B₂) :=
    ENNReal.ofReal_le_ofReal (by have := le_max_left B₁ B₂; linarith)
  have hM₂ : ENNReal.ofReal (4 * B₂) ≤ ENNReal.ofReal (4 * max B₁ B₂) :=
    ENNReal.ofReal_le_ofReal (by have := le_max_right B₁ B₂; linarith)
  calc _ ≤ _ := hS
    _ ≤ ENNReal.ofReal (4 * B₂) * (∫⁻ x in I ∩ Iio a, ENNReal.ofReal (f' x ^ 2 * p x)) +
        ENNReal.ofReal (4 * B₁) * (∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (f' x ^ 2 * p x)) :=
          add_le_add hL hR
    _ ≤ ENNReal.ofReal (4 * max B₁ B₂) * (∫⁻ x in I ∩ Iio a, ENNReal.ofReal (f' x ^ 2 * p x)) +
        ENNReal.ofReal (4 * max B₁ B₂) * (∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (f' x ^ 2 * p x)) := by
          gcongr
    _ = ENNReal.ofReal (4 * max B₁ B₂) * ((∫⁻ x in I ∩ Iio a, ENNReal.ofReal (f' x ^ 2 * p x)) +
        (∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (f' x ^ 2 * p x))) := (mul_add _ _ _).symm
    _ ≤ _ := by gcongr

end Function

section Main

variable {I : Set ℝ} {p : ℝ → ℝ} {a : ℝ} {f f' : ℝ → ℝ}

/-- The right resistance constant `B_+ = sup_{x > a} μ([x, b)) ∫_a^x 1/p` (as a real supremum;
the sup is taken over `x ∈ I`, `a < x`). -/
noncomputable def rightResistanceConstant (I : Set ℝ) (p : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun x => (densityMeasure I p (Ici x)).toReal * ∫ t in a..x, (p t)⁻¹) '' (I ∩ Ioi a))

/-- The left resistance constant `B_- = sup_{x < a} μ((l, x]) ∫_x^a 1/p` (as a real supremum;
the sup is taken over `x ∈ I`, `x < a`). -/
noncomputable def leftResistanceConstant (I : Set ℝ) (p : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun x => (densityMeasure I p (Iic x)).toReal * ∫ t in x..a, (p t)⁻¹) '' (I ∩ Iio a))

lemma rightResistanceConstant_nonneg (hp0 : ∀ x ∈ I, 0 < p x) (hIc : I.OrdConnected)
    (ha : a ∈ I) : 0 ≤ rightResistanceConstant I p a := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, ⟨hx, hax⟩, rfl⟩
  have hsub : Icc a x ⊆ I := hIc.out ha hx
  refine mul_nonneg ENNReal.toReal_nonneg (intervalIntegral.integral_nonneg (le_of_lt hax)
    fun t ht => (inv_pos.2 (hp0 t (hsub ht))).le)

lemma leftResistanceConstant_nonneg (hp0 : ∀ x ∈ I, 0 < p x) (hIc : I.OrdConnected)
    (ha : a ∈ I) : 0 ≤ leftResistanceConstant I p a := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, ⟨hx, hxa⟩, rfl⟩
  have hsub : Icc x a ⊆ I := hIc.out hx ha
  refine mul_nonneg ENNReal.toReal_nonneg (intervalIntegral.integral_nonneg (le_of_lt hxa)
    fun t ht => (inv_pos.2 (hp0 t (hsub ht))).le)

/-- Lintegral form of the anchored half-line resistance Poincare inequality: no integrability or
finite-energy hypothesis on `f` is needed. -/
theorem anchored_half_line_resistance_poincare_lintegral (hIo : IsOpen I)
    (hIc : I.OrdConnected) (ha : a ∈ I) (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x)
    [IsFiniteMeasure (densityMeasure I p)]
    (hBp : BddAbove ((fun x => (densityMeasure I p (Ici x)).toReal * ∫ t in a..x, (p t)⁻¹) ''
      (I ∩ Ioi a)))
    (hBm : BddAbove ((fun x => (densityMeasure I p (Iic x)).toReal * ∫ t in x..a, (p t)⁻¹) ''
      (I ∩ Iio a)))
    (hf : ∀ x ∈ I, ∀ y ∈ I, f y - f x = ∫ t in x..y, f' t)
    (hf' : LocallyIntegrableOn f' I volume) :
    ∫⁻ x, ENNReal.ofReal ((f x - f a) ^ 2) ∂(densityMeasure I p) ≤
      ENNReal.ofReal (4 * max (rightResistanceConstant I p a) (leftResistanceConstant I p a)) *
        ∫⁻ x, ENNReal.ofReal (f' x ^ 2) ∂(densityMeasure I p) :=
  hardy_of_bounds hIo hIc ha hp hp0
    (fun x hx hax => le_csSup hBp ⟨x, ⟨hx, hax⟩, rfl⟩)
    (fun x hx hxa => le_csSup hBm ⟨x, ⟨hx, hxa⟩, rfl⟩) hf hf'

/-- **Anchored half-line resistance Poincare inequality.** Let `μ(dx) = p(x) dx` be a probability
measure on the open interval `I`, with `p > 0` continuous, and `a ∈ I` an anchor (not necessarily
a median). If the resistance constants `B_±` are finite, then every absolutely continuous `f`
with `∫ |f'|² dμ < ∞` satisfies `∫ (f - f a)² dμ ≤ 4 max(B_+, B_-) ∫ |f'|² dμ`, and the same
bound holds for `Var_μ f`. -/
theorem anchored_half_line_resistance_poincare (hIo : IsOpen I)
    (hIc : I.OrdConnected) (ha : a ∈ I) (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x)
    [IsProbabilityMeasure (densityMeasure I p)]
    (hBp : BddAbove ((fun x => (densityMeasure I p (Ici x)).toReal * ∫ t in a..x, (p t)⁻¹) ''
      (I ∩ Ioi a)))
    (hBm : BddAbove ((fun x => (densityMeasure I p (Iic x)).toReal * ∫ t in x..a, (p t)⁻¹) ''
      (I ∩ Iio a)))
    (hf : ∀ x ∈ I, ∀ y ∈ I, f y - f x = ∫ t in x..y, f' t)
    (hf' : LocallyIntegrableOn f' I volume)
    (hE : Integrable (fun x => f' x ^ 2) (densityMeasure I p)) :
    Integrable (fun x => (f x - f a) ^ 2) (densityMeasure I p) ∧
    MemLp f 2 (densityMeasure I p) ∧
    ∫ x, (f x - f a) ^ 2 ∂(densityMeasure I p) ≤
      4 * max (rightResistanceConstant I p a) (leftResistanceConstant I p a) *
        ∫ x, f' x ^ 2 ∂(densityMeasure I p) ∧
    ProbabilityTheory.variance f (densityMeasure I p) ≤
      4 * max (rightResistanceConstant I p a) (leftResistanceConstant I p a) *
        ∫ x, f' x ^ 2 ∂(densityMeasure I p) := by
  set μ := densityMeasure I p with hμ
  set M := max (rightResistanceConstant I p a) (leftResistanceConstant I p a) with hM
  have hM0 : 0 ≤ M := (rightResistanceConstant_nonneg hp0 hIc ha).trans (le_max_left _ _)
  have hmain := anchored_half_line_resistance_poincare_lintegral hIo hIc ha hp hp0 hBp hBm hf hf'
  have hfc := continuousOn_of_ftc hIo hf hf'
  have hfa : AEStronglyMeasurable f μ :=
    (hfc.aestronglyMeasurable hIo.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hua : AEStronglyMeasurable (fun x => f x - f a) μ := hfa.sub aestronglyMeasurable_const
  have hE' : ∫⁻ x, ENNReal.ofReal (f' x ^ 2) ∂μ = ENNReal.ofReal (∫ x, f' x ^ 2 ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hE (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
  have hlt : ∫⁻ x, ENNReal.ofReal ((f x - f a) ^ 2) ∂μ < ⊤ := by
    refine lt_of_le_of_lt hmain ?_
    rw [hE']
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hint : Integrable (fun x => (f x - f a) ^ 2) μ :=
    ⟨hua.pow 2,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)).2 hlt⟩
  have hreal : ∫ x, (f x - f a) ^ 2 ∂μ ≤ 4 * M * ∫ x, f' x ^ 2 ∂μ := by
    have hE0 : 0 ≤ ∫ x, f' x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have h1 : ENNReal.ofReal (∫ x, (f x - f a) ^ 2 ∂μ) =
        ∫⁻ x, ENNReal.ofReal ((f x - f a) ^ 2) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)
    have h2 : ENNReal.ofReal (∫ x, (f x - f a) ^ 2 ∂μ) ≤
        ENNReal.ofReal (4 * M * ∫ x, f' x ^ 2 ∂μ) := by
      rw [h1, ENNReal.ofReal_mul (by linarith)]
      rw [hE'] at hmain
      exact hmain
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith) hE0)).1 h2
  have hmem : MemLp f 2 μ := by
    have h0 : MemLp (fun x => f x - f a) 2 μ :=
      (memLp_two_iff_integrable_sq hua).2 hint
    have h3 := h0.add (memLp_const (f a))
    have e : ((fun x => f x - f a) + fun _ => f a) = f := by ext x; simp
    rw [e] at h3
    exact h3
  refine ⟨hint, hmem, hreal, ?_⟩
  have hv := ProbabilityTheory.variance_sub_const hfa (f a)
  have hv2 := ProbabilityTheory.variance_le_expectation_sq hua
  rw [← hv]
  refine hv2.trans ?_
  simpa [Pi.pow_apply] using hreal

end Main

section WeightedCore

variable {I : Set ℝ} {p : ℝ → ℝ} {a : ℝ}

lemma tail_integral_le_w (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {q : ℝ → ℝ} (hq : ContinuousOn q I)
    {T : ℝ → ℝ} {B : ℝ}
    (hT : ∀ x ∈ I, a < x → HasDerivAt T (-q x) x) (hT0 : ∀ x ∈ I, a < x → 0 ≤ T x)
    (hB : ∀ x ∈ I, a < x → T x * resistance p a x ≤ B)
    {t s : ℝ} (ht : t ∈ I) (hat : a < t) (hs : s ∈ I) (hts : t ≤ s) :
    ∫ x in t..s, q x * √(resistance p a x) ≤ 2 * B / √(resistance p a t) := by
  have hW : ∀ y ∈ I, HasDerivAt (resistance p a) (p y)⁻¹ y :=
    fun y hy => hasDerivAt_resistance hIo hIc ha hp hp0 hy
  have hsub : Icc t s ⊆ I := hIc.out ht hs
  have hWpos : ∀ x ∈ Icc t s, 0 < resistance p a x := fun x hx =>
    resistance_pos hIc ha hp hp0 (hsub hx) (lt_of_lt_of_le hat hx.1)
  set F : ℝ → ℝ := fun x => ∫ y in t..x, q y * √(resistance p a y) with hFdef
  have hcontg : ∀ x ∈ I, ContinuousAt (fun y => q y * √(resistance p a y)) x := by
    intro x hx
    exact (hq.continuousAt (hIo.mem_nhds hx)).mul
      ((hW x hx).continuousAt.sqrt)
  have hFd : ∀ x ∈ Icc t s, HasDerivAt F (q x * √(resistance p a x)) x := by
    intro x hx
    have hxI := hsub hx
    have hcg : ContinuousOn (fun y => q y * √(resistance p a y)) I := fun y hy =>
      (hcontg y hy).continuousWithinAt
    exact intervalIntegral.integral_hasDerivAt_right
      ((hcg.mono (hIc.uIcc_subset ht hxI)).intervalIntegrable)
      (hcg.stronglyMeasurableAtFilter hIo x hxI) (hcontg x hxI)
  set G : ℝ → ℝ := fun x => F s - F x - T x * √(resistance p a x)
    - B * (√(resistance p a x))⁻¹ with hGdef
  have hGd : ∀ x ∈ Icc t s, HasDerivAt G
      ((B - T x * resistance p a x) / (2 * p x * resistance p a x * √(resistance p a x))) x := by
    intro x hx
    have hxI := hsub hx
    have hxa : a < x := lt_of_lt_of_le hat hx.1
    have hWx := hWpos x hx
    have hS : 0 < √(resistance p a x) := Real.sqrt_pos.2 hWx
    have h1 := ((((hFd x hx).const_sub (F s)).sub
      ((hT x hxI hxa).mul ((hW x hxI).sqrt hWx.ne'))).sub
      ((((hW x hxI).sqrt hWx.ne').inv hS.ne').const_mul B))
    convert h1 using 1
    have hpx := hp0 x hxI
    have hsq : √(resistance p a x) ^ 2 = resistance p a x := Real.sq_sqrt hWx.le
    field_simp
    rw [hsq]
    ring
  have hmono : MonotoneOn G (Icc t s) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => (B - T x * resistance p a x) /
      (2 * p x * resistance p a x * √(resistance p a x))) (convex_Icc t s) ?_ ?_ ?_
    · exact fun x hx => (hGd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hGd x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Icc t s := ⟨hx.1.le, hx.2.le⟩
      have hxI := hsub hx'
      have hxa : a < x := lt_of_lt_of_le hat hx'.1
      have hWx := hWpos x hx'
      have hS : 0 < √(resistance p a x) := Real.sqrt_pos.2 hWx
      have := hp0 x hxI
      have := hB x hxI hxa
      apply div_nonneg (by linarith) (by positivity)
  have hGts : G t ≤ G s := hmono ⟨le_rfl, hts⟩ ⟨hts, le_rfl⟩ hts
  have hWt := hWpos t ⟨le_rfl, hts⟩
  have hWs := hWpos s ⟨hts, le_rfl⟩
  have hSt : 0 < √(resistance p a t) := Real.sqrt_pos.2 hWt
  have hSs : 0 < √(resistance p a s) := Real.sqrt_pos.2 hWs
  have hTt := hT0 t ht hat
  have hTs := hT0 s hs (lt_of_lt_of_le hat hts)
  have hBt := hB t ht hat
  have hB0 : 0 ≤ B := le_trans (mul_nonneg hTt hWt.le) hBt
  have hGs : G s ≤ 0 := by
    simp only [hGdef, sub_self, zero_sub]
    have : 0 ≤ T s * √(resistance p a s) := by positivity
    have : 0 ≤ B * (√(resistance p a s))⁻¹ := by positivity
    linarith
  have hFt : F t = 0 := by simp [hFdef]
  have h1 : F s ≤ T t * √(resistance p a t) + B * (√(resistance p a t))⁻¹ := by
    have := hGts.trans hGs
    simp only [hGdef, hFt] at this
    linarith
  have h2 : T t * √(resistance p a t) ≤ B * (√(resistance p a t))⁻¹ := by
    have hsq : √(resistance p a t) ^ 2 = resistance p a t := Real.sq_sqrt hWt.le
    rw [← div_eq_mul_inv, le_div_iff₀ hSt, mul_assoc, ← sq, hsq]
    exact hBt
  calc ∫ x in t..s, q x * √(resistance p a x) = F s := rfl
    _ ≤ 2 * B / √(resistance p a t) := by
      have : 2 * B / √(resistance p a t) = B * (√(resistance p a t))⁻¹ +
        B * (√(resistance p a t))⁻¹ := by ring
      rw [this]; linarith


lemma pointwise_cs_w (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {q : ℝ → ℝ} (hq0 : ∀ x ∈ I, 0 ≤ q x)
    {g u : ℝ → ℝ}
    (hg : AEMeasurable g (volume.restrict (I ∩ Ioi a)))
    (hug : ∀ x ∈ I, a < x → ‖u x‖ₑ ≤ ∫⁻ t in Ioo a x, ‖g t‖ₑ) {x : ℝ} (hx : x ∈ I) (hax : a < x) :
    ENNReal.ofReal (u x ^ 2 * q x) ≤ ENNReal.ofReal (q x * (2 * √(resistance p a x))) *
      ∫⁻ t in Ioo a x, ENNReal.ofReal (g t ^ 2 * p t * √(resistance p a t)) := by
  have hsub : Ioo a x ⊆ I ∩ Ioi a := fun t ht =>
    ⟨hIc.out ha hx ⟨ht.1.le, ht.2.le⟩, ht.1⟩
  have hIsub : Ioo a x ⊆ I := fun t ht => (hsub ht).1
  have hg' : AEMeasurable g (volume.restrict (Ioo a x)) :=
    hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  set r : ℝ → ℝ := fun t => p t * √(resistance p a t) with hr
  have hrc : ContinuousOn r (Ioo a x) :=
    (continuousOn_density_sqrt hIo hIc ha hp hp0).mono hIsub
  have hrpos : ∀ t ∈ Ioo a x, 0 < r t := fun t ht =>
    mul_pos (hp0 t (hIsub ht)) (Real.sqrt_pos.2 (resistance_pos hIc ha hp hp0 (hIsub ht) ht.1))
  have hsq : ContinuousOn (fun t => √(r t)) (Ioo a x) := hrc.sqrt
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (|g t| * √(r t)) with hF
  set G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (√(r t))⁻¹ with hG
  have hFm : AEMeasurable F (volume.restrict (Ioo a x)) :=
    (hg'.abs.mul (hsq.aemeasurable measurableSet_Ioo)).ennreal_ofReal
  have hGm : AEMeasurable G (volume.restrict (Ioo a x)) := by
    have : ContinuousOn (fun t => (√(r t))⁻¹) (Ioo a x) :=
      hsq.inv₀ fun t ht => (Real.sqrt_pos.2 (hrpos t ht)).ne'
    exact (this.aemeasurable measurableSet_Ioo).ennreal_ofReal
  have hFG : ∀ t ∈ Ioo a x, ‖g t‖ₑ = F t * G t := by
    intro t ht
    have h1 := Real.sqrt_pos.2 (hrpos t ht)
    simp only [hF, hG, ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) h1.le),
      Real.enorm_eq_ofReal_abs]
    congr 1
    field_simp
  have hF2 : ∀ t ∈ Ioo a x, F t ^ 2 =
      ENNReal.ofReal (g t ^ 2 * p t * √(resistance p a t)) := by
    intro t ht
    simp only [hF, ← ENNReal.ofReal_pow (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))]
    congr 1
    rw [mul_pow, sq_abs, Real.sq_sqrt (hrpos t ht).le]
    simp only [hr]
    ring
  have hG2 : ∀ t ∈ Ioo a x, G t ^ 2 = ENNReal.ofReal ((p t * √(resistance p a t))⁻¹) := by
    intro t ht
    have h1 := Real.sqrt_pos.2 (hrpos t ht)
    simp only [hG, ← ENNReal.ofReal_pow (inv_nonneg.2 h1.le)]
    congr 1
    rw [inv_pow, Real.sq_sqrt (hrpos t ht).le]
  have hcs := lintegral_mul_sq_le (volume.restrict (Ioo a x)) hFm hGm
  have e1 : ∫⁻ t in Ioo a x, ‖g t‖ₑ = ∫⁻ t in Ioo a x, F t * G t :=
    setLIntegral_congr_fun measurableSet_Ioo hFG
  have e2 : ∫⁻ t in Ioo a x, F t ^ 2 =
      ∫⁻ t in Ioo a x, ENNReal.ofReal (g t ^ 2 * p t * √(resistance p a t)) :=
    setLIntegral_congr_fun measurableSet_Ioo hF2
  have e3 : ∫⁻ t in Ioo a x, G t ^ 2 = ENNReal.ofReal (2 * √(resistance p a x)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioo hG2]
    exact lintegral_inv_mul_sqrt_resistance hIo hIc ha hp hp0 hx hax
  have hu := hug x hx hax
  rw [e1] at hu
  have hu2 : ‖u x‖ₑ ^ 2 ≤ (∫⁻ t in Ioo a x, F t * G t) ^ 2 := pow_le_pow_left' hu 2
  rw [e2, e3] at hcs
  have hpx : 0 ≤ q x := hq0 x hx
  calc ENNReal.ofReal (u x ^ 2 * q x) = ‖u x‖ₑ ^ 2 * ENNReal.ofReal (q x) := by
        rw [ENNReal.ofReal_mul (sq_nonneg _), Real.enorm_eq_ofReal_abs,
          ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    _ ≤ (∫⁻ t in Ioo a x, F t * G t) ^ 2 * ENNReal.ofReal (q x) := by gcongr
    _ ≤ ((∫⁻ t in Ioo a x, ENNReal.ofReal (g t ^ 2 * p t * √(resistance p a t))) *
          ENNReal.ofReal (2 * √(resistance p a x))) * ENNReal.ofReal (q x) := by gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul hpx]
        ring


lemma lintegral_tail_le_w (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {q : ℝ → ℝ} (hq : ContinuousOn q I)
    (hq0 : ∀ x ∈ I, 0 ≤ q x) {T : ℝ → ℝ} {B : ℝ}
    (hT : ∀ x ∈ I, a < x → HasDerivAt T (-q x) x) (hT0 : ∀ x ∈ I, a < x → 0 ≤ T x)
    (hB : ∀ x ∈ I, a < x → T x * resistance p a x ≤ B) {t : ℝ} (ht : t ∈ I) (hat : a < t) :
    ∫⁻ x in I ∩ Ioi t, ENNReal.ofReal (q x * (2 * √(resistance p a x)))
      ≤ ENNReal.ofReal (4 * B / √(resistance p a t)) := by
  refine setLIntegral_Ioi_inter_le hIo hIc ht _ fun s hs hts => ?_
  have hsub : Icc t s ⊆ I := hIc.out ht hs
  have hc : ContinuousOn (fun x => q x * (2 * √(resistance p a x))) (Icc t s) := by
    have := (continuousOn_resistance hIo hIc ha hp hp0).mono hsub
    have := hq.mono hsub
    fun_prop
  have hint : IntegrableOn (fun x => q x * (2 * √(resistance p a x))) (Ioc t s) volume :=
    (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [← intervalIntegral.integral_of_le hts.le]
    have h1 := tail_integral_le_w hIo hIc ha hp hp0 hq hT hT0 hB ht hat hs hts.le
    have : ∫ x in t..s, q x * (2 * √(resistance p a x)) =
        2 * ∫ x in t..s, q x * √(resistance p a x) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext x; ring
    rw [this]
    calc 2 * ∫ x in t..s, q x * √(resistance p a x) ≤ 2 * (2 * B / √(resistance p a t)) := by
          gcongr
      _ = 4 * B / √(resistance p a t) := by ring
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hyI : y ∈ I := hsub ⟨hy.1.le, hy.2⟩
    have := hq0 y hyI
    have := Real.sqrt_nonneg (resistance p a y)
    positivity


theorem hardy_core_w (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {q : ℝ → ℝ} (hq : ContinuousOn q I)
    (hq0 : ∀ x ∈ I, 0 ≤ q x) {T : ℝ → ℝ} {B : ℝ}
    (hT : ∀ x ∈ I, a < x → HasDerivAt T (-q x) x) (hT0 : ∀ x ∈ I, a < x → 0 ≤ T x)
    (hB : ∀ x ∈ I, a < x → T x * resistance p a x ≤ B) {g u : ℝ → ℝ}
    (hg : AEMeasurable g (volume.restrict (I ∩ Ioi a)))
    (hug : ∀ x ∈ I, a < x → ‖u x‖ₑ ≤ ∫⁻ t in Ioo a x, ‖g t‖ₑ) :
    ∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (u x ^ 2 * q x) ≤
      ENNReal.ofReal (4 * B) * ∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (g x ^ 2 * p x) := by
  set R : Set ℝ := I ∩ Ioi a with hR
  have hRm : MeasurableSet R := hIo.measurableSet.inter measurableSet_Ioi
  set Φ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (g t ^ 2 * p t * √(resistance p a t)) with hΦ
  set h : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (q x * (2 * √(resistance p a x))) with hh
  have hRI : ∀ x ∈ R, x ∈ I ∧ a < x := fun x hx => hx
  -- Step 1: pointwise bound
  have step1 : ∫⁻ x in R, ENNReal.ofReal (u x ^ 2 * q x) ≤
      ∫⁻ x in R, h x * ∫⁻ t in Ioo a x, Φ t :=
    setLIntegral_mono' hRm fun x hx =>
      pointwise_cs_w hIo hIc ha hp hp0 hq0 hg hug hx.1 hx.2
  -- measurability
  have hpm : AEMeasurable (fun x => p x) (volume.restrict R) :=
    (hp.mono inter_subset_left).aemeasurable hRm
  have hWc : ContinuousOn (resistance p a) R :=
    (continuousOn_resistance hIo hIc ha hp hp0).mono inter_subset_left
  have hhm : AEMeasurable h (volume.restrict R) := by
    have : ContinuousOn (fun x => q x * (2 * √(resistance p a x))) R := by
      have := hq.mono (inter_subset_left : R ⊆ I)
      fun_prop
    exact (this.aemeasurable hRm).ennreal_ofReal
  have hΦm : AEMeasurable Φ (volume.restrict R) := by
    have : ContinuousOn (fun x => p x * √(resistance p a x)) R :=
      (continuousOn_density_sqrt hIo hIc ha hp hp0).mono inter_subset_left
    have h2 := (hg.pow_const 2).mul ((this.aemeasurable hRm))
    refine h2.ennreal_ofReal.congr ?_
    exact Filter.Eventually.of_forall fun t => by
      simp only [hΦ, Pi.mul_apply]; congr 1; ring
  -- Step 2: Tonelli
  let K : ℝ × ℝ → ℝ≥0∞ := {z : ℝ × ℝ | z.2 < z.1}.indicator fun z => h z.1 * Φ z.2
  have hKm : AEMeasurable K ((volume.restrict R).prod (volume.restrict R)) := by
    have h1 : AEMeasurable (fun z : ℝ × ℝ => h z.1) ((volume.restrict R).prod (volume.restrict R)) :=
      hhm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : AEMeasurable (fun z : ℝ × ℝ => Φ z.2) ((volume.restrict R).prod (volume.restrict R)) :=
      hΦm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have : AEMeasurable (fun z : ℝ × ℝ => h z.1 * Φ z.2)
        ((volume.restrict R).prod (volume.restrict R)) := h1.mul h2
    exact this.indicator (measurableSet_lt measurable_snd measurable_fst)
  have step2 : ∫⁻ x in R, h x * ∫⁻ t in Ioo a x, Φ t = ∫⁻ x in R, ∫⁻ t in R, K (x, t) := by
    refine setLIntegral_congr_fun hRm fun x hx => ?_
    have hset : (Ioo a x) = Iio x ∩ R := by
      ext t
      simp only [hR, mem_Ioo, mem_inter_iff, mem_Ioi, mem_Iio]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, ⟨hIc.out ha hx.1 ⟨h1.le, h2.le⟩, h1⟩⟩
      · rintro ⟨h2, ⟨_, h1⟩⟩; exact ⟨h1, h2⟩
    have hK : ∀ t, K (x, t) = (Iio x).indicator (fun t => h x * Φ t) t := by
      intro t
      simp only [K, Set.indicator, mem_ofPred_eq, mem_Iio]
    simp_rw [hK]
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      ← hset, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have step3 : ∀ t ∈ R, ∫⁻ x in R, K (x, t) ≤ ENNReal.ofReal (4 * B) *
      ENNReal.ofReal (g t ^ 2 * p t) := by
    intro t ht
    obtain ⟨htI, hat⟩ := ht
    have hKt : ∀ x, K (x, t) = (Ioi t).indicator (fun x => h x * Φ t) x := by
      intro x
      simp only [K, Set.indicator, mem_ofPred_eq, mem_Ioi]
    simp_rw [hKt]
    have hset : Ioi t ∩ R = I ∩ Ioi t := by
      ext x
      simp only [hR, mem_inter_iff, mem_Ioi]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, lt_trans hat h1⟩
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hset,
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    have hWt : 0 < resistance p a t := resistance_pos hIc ha hp hp0 htI hat
    have hS : 0 < √(resistance p a t) := Real.sqrt_pos.2 hWt
    have hB0 : 0 ≤ B := le_trans (mul_nonneg (hT0 t htI hat) hWt.le) (hB t htI hat)
    have hpt := hp0 t htI
    calc (∫⁻ x in I ∩ Ioi t, h x) * Φ t
        ≤ ENNReal.ofReal (4 * B / √(resistance p a t)) * Φ t := by
          gcongr
          exact lintegral_tail_le_w hIo hIc ha hp hp0 hq hq0 hT hT0 hB htI hat
      _ = _ := by
          simp only [hΦ]
          rw [mul_comm, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  calc ∫⁻ x in R, ENNReal.ofReal (u x ^ 2 * q x)
      ≤ ∫⁻ x in R, h x * ∫⁻ t in Ioo a x, Φ t := step1
    _ = ∫⁻ x in R, ∫⁻ t in R, K (x, t) := step2
    _ = ∫⁻ t in R, ∫⁻ x in R, K (x, t) := lintegral_lintegral_swap hKm
    _ ≤ ∫⁻ t in R, ENNReal.ofReal (4 * B) * ENNReal.ofReal (g t ^ 2 * p t) :=
        setLIntegral_mono' hRm step3
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The left half-line weighted Hardy inequality with the constant `4 B`, by reflection. The auxiliary
function `T` is given through its reflection `z ↦ T (-z)`. -/
theorem hardy_core_left_w (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {q : ℝ → ℝ} (hq : ContinuousOn q I)
    (hq0 : ∀ x ∈ I, 0 ≤ q x) {T : ℝ → ℝ} {B : ℝ}
    (hT : ∀ y : ℝ, -y ∈ I → -y < a → HasDerivAt (fun z => T (-z)) (-q (-y)) y)
    (hT0 : ∀ x ∈ I, x < a → 0 ≤ T x)
    (hB : ∀ x ∈ I, x < a → T x * ∫ t in x..a, (p t)⁻¹ ≤ B) {g u : ℝ → ℝ}
    (hg : AEMeasurable g (volume.restrict (I ∩ Iio a)))
    (hug : ∀ x ∈ I, x < a → ‖u x‖ₑ ≤ ∫⁻ t in Ioo x a, ‖g t‖ₑ) :
    ∫⁻ x in I ∩ Iio a, ENNReal.ofReal (u x ^ 2 * q x) ≤
      ENNReal.ofReal (4 * B) * ∫⁻ x in I ∩ Iio a, ENNReal.ofReal (g x ^ 2 * p x) := by
  set I' : Set ℝ := Neg.neg ⁻¹' I with hI'
  have hI'o : IsOpen I' := hIo.preimage continuous_neg
  have hI'c : I'.OrdConnected := hIc.preimage_anti (fun _ _ h => neg_le_neg h)
  have ha' : -a ∈ I' := by simpa [hI'] using ha
  have hp' : ContinuousOn (fun x => p (-x)) I' :=
    hp.comp continuous_neg.continuousOn (fun x hx => hx)
  have hp0' : ∀ x ∈ I', 0 < p (-x) := fun x hx => hp0 _ hx
  have hq' : ContinuousOn (fun x => q (-x)) I' :=
    hq.comp continuous_neg.continuousOn (fun x hx => hx)
  have hq0' : ∀ x ∈ I', 0 ≤ q (-x) := fun x hx => hq0 _ hx
  have hres : ∀ y, resistance (fun x => p (-x)) (-a) y = ∫ t in -y..a, (p t)⁻¹ := by
    intro y
    unfold resistance
    rw [intervalIntegral.integral_comp_neg (fun t => (p t)⁻¹), neg_neg]
  have hset : I' ∩ Ioi (-a) = Neg.neg ⁻¹' (I ∩ Iio a) := by
    ext x; simp only [mem_inter_iff, mem_Ioi, mem_preimage, mem_Iio, hI']
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  have key := hardy_core_w (I := I') (p := fun x => p (-x)) (q := fun x => q (-x)) (a := -a) (T := fun z => T (-z)) (B := B)
    (g := fun t => g (-t)) (u := fun x => u (-x)) hI'o hI'c ha' hp' hp0' hq' hq0'
    (fun x hx hax => hT x hx (by linarith))
    (fun x hx hax => hT0 _ hx (by linarith))
    (fun x hx hax => by
      rw [hres]; exact hB _ hx (by linarith))
    (by
      rw [hset]
      exact hg.comp_quasiMeasurePreserving
        (neg_measurePreserving_restrict _).quasiMeasurePreserving)
    (fun x hx hax => by
      refine (hug (-x) hx (by linarith)).trans (le_of_eq ?_)
      have : Ioo (-a) x = Neg.neg ⁻¹' Ioo (-x) a := by
        ext z; simp only [mem_Ioo, mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      rw [this]
      exact (setLIntegral_comp_neg (fun t => ‖g t‖ₑ) (Ioo (-x) a)).symm)
  rw [hset] at key
  have e1 := setLIntegral_comp_neg (fun x => ENNReal.ofReal (u x ^ 2 * q x)) (I ∩ Iio a)
  have e2 := setLIntegral_comp_neg (fun x => ENNReal.ofReal (g x ^ 2 * p x)) (I ∩ Iio a)
  rw [e1, e2] at key
  exact key


variable {f f' : ℝ → ℝ}

/-- Weighted anchored Hardy inequality (lintegral form), from the two half-line cores. -/
theorem hardy_of_bounds_w (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {q : ℝ → ℝ} (hq : ContinuousOn q I)
    (hq0 : ∀ x ∈ I, 0 ≤ q x) {TR TL : ℝ → ℝ} {B₁ B₂ : ℝ}
    (hTR : ∀ x ∈ I, a < x → HasDerivAt TR (-q x) x) (hTR0 : ∀ x ∈ I, a < x → 0 ≤ TR x)
    (hB₁ : ∀ x ∈ I, a < x → TR x * ∫ t in a..x, (p t)⁻¹ ≤ B₁)
    (hTL : ∀ y : ℝ, -y ∈ I → -y < a → HasDerivAt (fun z => TL (-z)) (-q (-y)) y)
    (hTL0 : ∀ x ∈ I, x < a → 0 ≤ TL x)
    (hB₂ : ∀ x ∈ I, x < a → TL x * ∫ t in x..a, (p t)⁻¹ ≤ B₂)
    (hf : ∀ x ∈ I, ∀ y ∈ I, f y - f x = ∫ t in x..y, f' t)
    (hf' : LocallyIntegrableOn f' I volume) :
    ∫⁻ x in I, ENNReal.ofReal ((f x - f a) ^ 2 * q x) ≤
      ENNReal.ofReal (4 * max B₁ B₂) * ∫⁻ x in I, ENNReal.ofReal (f' x ^ 2 * p x) := by
  have hfc := continuousOn_of_ftc hIo hf hf'
  have hg : AEMeasurable f' (volume.restrict I) := hf'.aestronglyMeasurable.aemeasurable
  have hR := hardy_core_w hIo hIc ha hp hp0 hq hq0 (T := TR)
    (B := B₁) (g := f') (u := fun x => f x - f a) hTR hTR0 hB₁
    (hg.mono_set inter_subset_left)
    (fun x hx hax => enorm_sub_le_lintegral hf ha hx hax.le)
  have hL := hardy_core_left_w hIo hIc ha hp hp0 hq hq0 (T := TL)
    (B := B₂) (g := f') (u := fun x => f x - f a) hTL hTL0 hB₂ (hg.mono_set inter_subset_left)
    (fun x hx hxa => by
      rw [← enorm_neg, neg_sub]
      exact enorm_sub_le_lintegral hf hx ha hxa.le)
  have hdisj : Disjoint (I ∩ Iio a) (I ∩ Ioi a) :=
    Set.disjoint_left.2 fun x h1 h2 => lt_asymm (show x < a from h1.2) (show a < x from h2.2)
  have hmeasR : MeasurableSet (I ∩ Ioi a) := hIo.measurableSet.inter measurableSet_Ioi
  have hcov : I ⊆ ((I ∩ Iio a) ∪ (I ∩ Ioi a)) ∪ {a} := by
    intro x hx
    rcases lt_trichotomy x a with h | h | h
    · exact Or.inl (Or.inl ⟨hx, h⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨hx, h⟩)
  have hS : ∫⁻ x in I, ENNReal.ofReal ((f x - f a) ^ 2 * q x) ≤
      (∫⁻ x in I ∩ Iio a, ENNReal.ofReal ((f x - f a) ^ 2 * q x)) +
        (∫⁻ x in I ∩ Ioi a, ENNReal.ofReal ((f x - f a) ^ 2 * q x)) := by
    calc _ ≤ ∫⁻ x in ((I ∩ Iio a) ∪ (I ∩ Ioi a)) ∪ {a},
            ENNReal.ofReal ((f x - f a) ^ 2 * q x) := lintegral_mono_set hcov
      _ ≤ (∫⁻ x in (I ∩ Iio a) ∪ (I ∩ Ioi a), ENNReal.ofReal ((f x - f a) ^ 2 * q x)) +
            ∫⁻ x in ({a} : Set ℝ), ENNReal.ofReal ((f x - f a) ^ 2 * q x) :=
          lintegral_union_le _ _ _
      _ ≤ _ := by
          rw [setLIntegral_measure_zero ({a} : Set ℝ) _ (measure_singleton a), add_zero]
          exact lintegral_union_le _ _ _
  have hT : (∫⁻ x in I ∩ Iio a, ENNReal.ofReal (f' x ^ 2 * p x)) +
        (∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (f' x ^ 2 * p x)) ≤
      ∫⁻ x in I, ENNReal.ofReal (f' x ^ 2 * p x) := by
    rw [← lintegral_union hmeasR hdisj]
    exact lintegral_mono_set (union_subset inter_subset_left inter_subset_left)
  have hM₁ : ENNReal.ofReal (4 * B₁) ≤ ENNReal.ofReal (4 * max B₁ B₂) :=
    ENNReal.ofReal_le_ofReal (by have := le_max_left B₁ B₂; linarith)
  have hM₂ : ENNReal.ofReal (4 * B₂) ≤ ENNReal.ofReal (4 * max B₁ B₂) :=
    ENNReal.ofReal_le_ofReal (by have := le_max_right B₁ B₂; linarith)
  calc _ ≤ _ := hS
    _ ≤ ENNReal.ofReal (4 * B₂) * (∫⁻ x in I ∩ Iio a, ENNReal.ofReal (f' x ^ 2 * p x)) +
        ENNReal.ofReal (4 * B₁) * (∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (f' x ^ 2 * p x)) :=
          add_le_add hL hR
    _ ≤ ENNReal.ofReal (4 * max B₁ B₂) * (∫⁻ x in I ∩ Iio a, ENNReal.ofReal (f' x ^ 2 * p x)) +
        ENNReal.ofReal (4 * max B₁ B₂) * (∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (f' x ^ 2 * p x)) := by
          gcongr
    _ = ENNReal.ofReal (4 * max B₁ B₂) * ((∫⁻ x in I ∩ Iio a, ENNReal.ofReal (f' x ^ 2 * p x)) +
        (∫⁻ x in I ∩ Ioi a, ENNReal.ofReal (f' x ^ 2 * p x))) := (mul_add _ _ _).symm
    _ ≤ _ := by gcongr

end WeightedCore



/-- The tail weight `Ψ(t) = t log (1 + 1/t)` of the median logarithmic Hardy criterion. -/
noncomputable def tailLogWeight (t : ℝ) : ℝ := t * Real.log (1 + 1 / t)

lemma tailLogWeight_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ tailLogWeight t := by
  unfold tailLogWeight
  have : 0 ≤ 1 / t := by positivity
  exact mul_nonneg ht (Real.log_nonneg (by linarith))

lemma self_le_tailLogWeight {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) : t ≤ tailLogWeight t := by
  rcases ht0.eq_or_lt with h | h
  · subst h; simp [tailLogWeight]
  · unfold tailLogWeight
    have h2 : 2 ≤ 1 / t := by
      rw [le_div_iff₀ h]; linarith
    have h3 : 1 ≤ Real.log (1 + 1 / t) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9
      linarith
    nlinarith

lemma mul_log_two_div_le {t : ℝ} (ht : 0 < t) :
    t * Real.log (2 / t) ≤ 2 * tailLogWeight t := by
  unfold tailLogWeight
  have h1 : Real.log (2 / t) ≤ 2 * Real.log (1 + 1 / t) := by
    have hpos : 0 < 1 + 1 / t := by positivity
    rw [← show Real.log ((1 + 1 / t) ^ 2) = 2 * Real.log (1 + 1 / t) by
      rw [Real.log_pow]; norm_num]
    refine Real.log_le_log (by positivity) ?_
    have : (1 + 1 / t) ^ 2 = 1 + 2 / t + 1 / t ^ 2 := by field_simp; ring
    rw [this]
    have : 0 ≤ 1 / t ^ 2 := by positivity
    have : 2 / t ≤ 1 + 2 / t + 1 / t ^ 2 := by linarith
    exact this
  nlinarith

lemma log_le_log_add_div {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Real.log y ≤ Real.log c - 1 + y / c := by
  have := Real.log_le_sub_one_of_pos (div_pos hy hc)
  rw [Real.log_div hy.ne' hc.ne'] at this
  linarith

/-- Weak Rothaus-type pointwise bound. -/
lemma entropyIntegrand_sq_add_le {c x G : ℝ} (hG : 0 < G) :
    DGPS.entropyIntegrand (c ^ 2 + G) ((c + x) ^ 2) ≤
      39 * x ^ 2 + 3 * G + 4 * (x ^ 2 * Real.log (1 + x ^ 2 / G)) := by
  set s := c ^ 2 + G with hs
  have hs0 : 0 < s := by positivity
  have hlogx : 0 ≤ x ^ 2 * Real.log (1 + x ^ 2 / G) :=
    mul_nonneg (sq_nonneg _) (Real.log_nonneg (by have : 0 ≤ x ^ 2 / G := by positivity
                                                  linarith))
  unfold DGPS.entropyIntegrand
  by_cases hcase : (c + x) ^ 2 ≤ 4 * s
  · -- quadratic regime
    have hk : (c + x) ^ 2 * Real.log ((c + x) ^ 2 / s) - (c + x) ^ 2 + s ≤
        ((c + x) ^ 2 - s) ^ 2 / s := by
      rcases (sq_nonneg (c + x)).eq_or_lt with h0 | h0
      · rw [← h0]; simp
        rw [le_div_iff₀ hs0]; nlinarith
      · have := Real.log_le_sub_one_of_pos (div_pos h0 hs0)
        have h1 : (c + x) ^ 2 * Real.log ((c + x) ^ 2 / s) ≤
            (c + x) ^ 2 * ((c + x) ^ 2 / s - 1) := mul_le_mul_of_nonneg_left this h0.le
        have h2 : ((c + x) ^ 2 - s) ^ 2 / s =
            (c + x) ^ 2 * ((c + x) ^ 2 / s - 1) - (c + x) ^ 2 + s := by
          field_simp; ring
        rw [h2]; linarith
    have hx9 : x ^ 2 ≤ 9 * s := by
      have h1 : |c + x| ≤ 2 * √s := by
        rw [← Real.sqrt_sq_eq_abs]
        calc √((c + x) ^ 2) ≤ √(4 * s) := Real.sqrt_le_sqrt hcase
          _ = 2 * √s := by
            rw [Real.sqrt_mul (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
      have h2 : |c| ≤ √s := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by rw [hs]; linarith)
      have h3 : |x| ≤ 3 * √s := by
        have : |x| ≤ |c + x| + |c| := by
          have := abs_sub (c + x) c
          simpa using this
        linarith
      have h4 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      rw [h4]
      have h5 : (3 * √s) ^ 2 = 9 * s := by
        rw [mul_pow, Real.sq_sqrt hs0.le]; norm_num
      have h6 : |x| ^ 2 ≤ (3 * √s) ^ 2 := by gcongr
      linarith
    have hfin : ((c + x) ^ 2 - s) ^ 2 / s ≤ 39 * x ^ 2 + 3 * G := by
      rw [div_le_iff₀ hs0]
      have e : (c + x) ^ 2 - s = 2 * c * x + x ^ 2 - G := by rw [hs]; ring
      rw [e]
      have : (2 * c * x + x ^ 2 - G) ^ 2 ≤ 3 * (4 * c ^ 2 * x ^ 2 + x ^ 4 + G ^ 2) := by
        nlinarith [sq_nonneg (2 * c * x - x ^ 2), sq_nonneg (2 * c * x + G),
          sq_nonneg (x ^ 2 + G)]
      have h7 : x ^ 4 ≤ 9 * s * x ^ 2 := by nlinarith [sq_nonneg x]
      have h8 : 0 ≤ G * s := by positivity
      nlinarith [sq_nonneg x, sq_nonneg c, sq_nonneg G, mul_nonneg (sq_nonneg x) (sq_nonneg c),
        mul_nonneg (sq_nonneg x) hG.le]
    linarith
  · -- logarithmic regime
    rw [not_le] at hcase
    have hy : s ≤ (c + x) ^ 2 := by nlinarith
    have hcx : |c| ≤ |c + x| / 2 := by
      have h1 : c ^ 2 ≤ s := by rw [hs]; linarith
      have h2 : |c| ^ 2 ≤ |c + x| ^ 2 / 4 := by
        rw [sq_abs, sq_abs]; linarith
      nlinarith [abs_nonneg c, abs_nonneg (c + x)]
    have hxy : (c + x) ^ 2 ≤ 4 * x ^ 2 := by
      have h3 : |c + x| ≤ |c| + |x| := by
        have := abs_sub (c + x) (-c)
        have := abs_add_le c x
        exact this
      have h4 : |c + x| ≤ 2 * |x| := by linarith
      have h5 : |c + x| ^ 2 ≤ (2 * |x|) ^ 2 := by gcongr
      rw [sq_abs, mul_pow, sq_abs] at h5
      linarith
    have hxs : s ≤ x ^ 2 := by nlinarith
    have hxG : G ≤ x ^ 2 := by rw [hs] at hxs; nlinarith [sq_nonneg c]
    have hx0 : 0 < x ^ 2 := lt_of_lt_of_le hs0 hxs
    -- monotonicity of t log(t/s)
    have hmono : (c + x) ^ 2 * Real.log ((c + x) ^ 2 / s) ≤
        (4 * x ^ 2) * Real.log (4 * x ^ 2 / s) := by
      have l1 : 0 ≤ Real.log ((c + x) ^ 2 / s) :=
        Real.log_nonneg (by rw [le_div_iff₀ hs0]; linarith)
      have l2 : Real.log ((c + x) ^ 2 / s) ≤ Real.log (4 * x ^ 2 / s) :=
        Real.log_le_log (div_pos (lt_of_lt_of_le hs0 hy) hs0) (by gcongr)
      exact mul_le_mul hxy l2 l1 (by positivity)
    have hlog : Real.log (4 * x ^ 2 / s) ≤ Real.log 4 + Real.log (1 + x ^ 2 / G) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hs0]
      have : x ^ 2 / G * s ≥ x ^ 2 := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hG]
        nlinarith [sq_nonneg c]
      nlinarith
    have hl4 : Real.log 4 ≤ 3 / 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    have h4x : 0 ≤ 4 * x ^ 2 := by positivity
    calc (c + x) ^ 2 * Real.log ((c + x) ^ 2 / s) - (c + x) ^ 2 + s
        ≤ (4 * x ^ 2) * Real.log (4 * x ^ 2 / s) := by linarith
      _ ≤ (4 * x ^ 2) * (Real.log 4 + Real.log (1 + x ^ 2 / G)) := by gcongr
      _ ≤ 39 * x ^ 2 + 3 * G + 4 * (x ^ 2 * Real.log (1 + x ^ 2 / G)) := by
        have : 4 * x ^ 2 * Real.log 4 ≤ 4 * x ^ 2 * (3 / 2) := by gcongr
        nlinarith [hG]


lemma homogeneousEntropy_le_ofReal_integral {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {v : α → ℝ} {s : ℝ} (hs : 0 < s) (hv0 : ∀ x, 0 ≤ v x)
    (hvi : Integrable v P) (hEi : Integrable (fun x => DGPS.entropyIntegrand s (v x)) P) :
    DGPS.homogeneousEntropy P v ≤ ENNReal.ofReal (∫ x, DGPS.entropyIntegrand s (v x) ∂P) := by
  set a := ∫ x, v x ∂P with ha
  have ha0 : 0 ≤ a := integral_nonneg hv0
  rcases ha0.eq_or_lt with h0 | h0
  · rw [DGPS.homogeneousEntropy_of_integral_eq_zero h0.symm]; exact bot_le
  rw [DGPS.homogeneousEntropy_of_integral_ne_zero h0.ne', ← ha]
  have hpt : ∀ x, DGPS.entropyIntegrand a (v x) =
      DGPS.entropyIntegrand s (v x) - (Real.log (a / s) * v x + (s - a)) := by
    intro x
    unfold DGPS.entropyIntegrand
    rcases eq_or_ne (v x) 0 with h | h
    · rw [h]; simp
    · have : Real.log (v x / s) = Real.log (v x / a) + Real.log (a / s) := by
        rw [← Real.log_mul (div_ne_zero h h0.ne') (div_ne_zero h0.ne' hs.ne')]
        congr 1; field_simp
      rw [this]; ring
  have hint : Integrable (fun x => DGPS.entropyIntegrand a (v x)) P := by
    simp_rw [hpt]
    exact hEi.sub ((hvi.const_mul _).add (integrable_const _))
  have hnn : 0 ≤ᵐ[P] fun x => DGPS.entropyIntegrand a (v x) :=
    Filter.Eventually.of_forall fun x => DGPS.entropyIntegrand_nonneg h0 (hv0 x)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [hpt]
  have hI2 : Integrable (fun x => Real.log (a / s) * v x + (s - a)) P :=
    (hvi.const_mul _).add (integrable_const _)
  rw [integral_sub hEi hI2, integral_add (hvi.const_mul _) (integrable_const _),
    integral_const_mul, ← ha]
  simp only [integral_const, probReal_univ, one_smul]
  have := DGPS.entropyIntegrand_nonneg hs h0.le
  unfold DGPS.entropyIntegrand at this
  have e : a * Real.log (a / s) - a + s = Real.log (a / s) * a + (s - a) := by ring
  linarith



section LogHardy

variable {I : Set ℝ} {p : ℝ → ℝ} {a : ℝ}

lemma setIntegral_densityMeasure (hIo : IsOpen I) (hp : ContinuousOn p I)
    (hp0 : ∀ x ∈ I, 0 < p x) {s : Set ℝ} (hs : MeasurableSet s) (hsI : s ⊆ I) (h : ℝ → ℝ) :
    ∫ t in s, h t ∂(densityMeasure I p) = ∫ t in s, p t * h t := by
  have hρ : AEMeasurable (fun x => ENNReal.ofReal (p x)) ((volume.restrict I).restrict s) :=
    ((hp.aemeasurable hIo.measurableSet).ennreal_ofReal).restrict
  unfold densityMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hρ
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) h hs,
    Measure.restrict_restrict hs, inter_eq_left.2 hsI]
  refine setIntegral_congr_fun hs fun t ht => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (hp0 t (hsI ht)).le]

lemma tailIntegral_Ici (hIo : IsOpen I) (hIc : I.OrdConnected) (hp : ContinuousOn p I)
    (hp0 : ∀ x ∈ I, 0 < p x) {h : ℝ → ℝ}
    (hint : Integrable h (densityMeasure I p)) (ha : a ∈ I) {z : ℝ} (hz : z ∈ I) (haz : a ≤ z) :
    ∫ t in Ici z, h t ∂(densityMeasure I p) =
      ∫ t in Ici a, h t ∂(densityMeasure I p) - ∫ t in a..z, p t * h t := by
  have hsub : Icc a z ⊆ I := hIc.out ha hz
  have hU : ∫ t in Ici a, h t ∂(densityMeasure I p) =
      ∫ t in Ico a z, h t ∂(densityMeasure I p) + ∫ t in Ici z, h t ∂(densityMeasure I p) := by
    rw [← setIntegral_union _ measurableSet_Ici hint.integrableOn hint.integrableOn,
      Ico_union_Ici_eq_Ici haz]
    exact Set.disjoint_left.2 fun t h1 h2 => absurd h1.2 (not_lt.2 h2)
  have hE : ∫ t in Ico a z, h t ∂(densityMeasure I p) = ∫ t in a..z, p t * h t := by
    rw [setIntegral_densityMeasure hIo hp hp0 measurableSet_Ico (Ico_subset_Icc_self.trans hsub),
      intervalIntegral.integral_of_le haz, integral_Ico_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
  rw [hU, hE]; ring

lemma tailIntegral_Iic (hIo : IsOpen I) (hIc : I.OrdConnected) (hp : ContinuousOn p I)
    (hp0 : ∀ x ∈ I, 0 < p x) {h : ℝ → ℝ}
    (hint : Integrable h (densityMeasure I p)) (ha : a ∈ I) {z : ℝ} (hz : z ∈ I) (hza : z ≤ a) :
    ∫ t in Iic z, h t ∂(densityMeasure I p) =
      ∫ t in Iic a, h t ∂(densityMeasure I p) - ∫ t in z..a, p t * h t := by
  have hsub : Icc z a ⊆ I := hIc.out hz ha
  have hU : ∫ t in Iic a, h t ∂(densityMeasure I p) =
      ∫ t in Iic z, h t ∂(densityMeasure I p) + ∫ t in Ioc z a, h t ∂(densityMeasure I p) := by
    rw [← setIntegral_union _ measurableSet_Ioc hint.integrableOn hint.integrableOn,
      Iic_union_Ioc_eq_Iic hza]
    exact Set.disjoint_left.2 fun t h1 h2 => absurd h1 (not_le.2 h2.1)
  have hE : ∫ t in Ioc z a, h t ∂(densityMeasure I p) = ∫ t in z..a, p t * h t := by
    rw [setIntegral_densityMeasure hIo hp hp0 measurableSet_Ioc (Ioc_subset_Icc_self.trans hsub),
      intervalIntegral.integral_of_le hza]
  rw [hU, hE]; ring

lemma hasDerivAt_tailIntegral_right (hIo : IsOpen I) (hIc : I.OrdConnected)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {h : ℝ → ℝ} (hh : ContinuousOn h I)
    (hint : Integrable h (densityMeasure I p)) (ha : a ∈ I) {x : ℝ} (hx : x ∈ I) (hax : a < x) :
    HasDerivAt (fun z => ∫ t in Ici z, h t ∂(densityMeasure I p)) (-(h x * p x)) x := by
  have hc : ContinuousOn (fun t => p t * h t) I := hp.mul hh
  have hH : HasDerivAt (fun z => ∫ t in a..z, p t * h t) (p x * h x) x :=
    intervalIntegral.integral_hasDerivAt_right
      ((hc.mono (hIc.uIcc_subset ha hx)).intervalIntegrable)
      (hc.stronglyMeasurableAtFilter hIo x hx) (hc.continuousAt (hIo.mem_nhds hx))
  have h1 := hH.const_sub (∫ t in Ici a, h t ∂(densityMeasure I p))
  rw [mul_comm (h x)]
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hIo.mem_nhds hx, Ioi_mem_nhds hax] with z hz hz2
  exact tailIntegral_Ici hIo hIc hp hp0 hint ha hz (le_of_lt hz2)

lemma hasDerivAt_tailIntegral_left (hIo : IsOpen I) (hIc : I.OrdConnected)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x) {h : ℝ → ℝ} (hh : ContinuousOn h I)
    (hint : Integrable h (densityMeasure I p)) (ha : a ∈ I) {y : ℝ} (hy : -y ∈ I)
    (hya : -y < a) :
    HasDerivAt (fun z => ∫ t in Iic (-z), h t ∂(densityMeasure I p)) (-(h (-y) * p (-y))) y := by
  have hc : ContinuousOn (fun t => p t * h t) I := hp.mul hh
  have hH : HasDerivAt (fun w => ∫ t in a..w, p t * h t) (p (-y) * h (-y)) (-y) :=
    intervalIntegral.integral_hasDerivAt_right
      ((hc.mono (hIc.uIcc_subset ha hy)).intervalIntegrable)
      (hc.stronglyMeasurableAtFilter hIo (-y) hy) (hc.continuousAt (hIo.mem_nhds hy))
  have h2 : HasDerivAt (fun z : ℝ => -z) (-1) y := hasDerivAt_neg y
  have h3 := (hH.comp y h2).const_add (∫ t in Iic a, h t ∂(densityMeasure I p))
  have h4 : HasDerivAt (fun z => (∫ t in Iic a, h t ∂(densityMeasure I p)) +
      (fun w => ∫ t in a..w, p t * h t) (-z)) (-(h (-y) * p (-y))) y := by
    have h5 := h3
    rw [mul_neg_one] at h5
    rw [mul_comm (h (-y))]
    exact h5
  refine h4.congr_of_eventuallyEq ?_
  have hc' : ContinuousAt (fun z : ℝ => -z) y := continuous_neg.continuousAt
  filter_upwards [hc'.preimage_mem_nhds (hIo.mem_nhds hy),
    hc'.preimage_mem_nhds (Iio_mem_nhds hya)] with z hz hz2
  have := tailIntegral_Iic hIo hIc hp hp0 hint ha (z := -z) hz (le_of_lt hz2)
  simp only [this]
  rw [intervalIntegral.integral_symm]; ring


lemma lintegral_densityMeasure_ofReal (hIo : IsOpen I) (hp : ContinuousOn p I)
    (hp0 : ∀ x ∈ I, 0 < p x) {h : ℝ → ℝ} (hh : AEMeasurable h (volume.restrict I)) :
    ∫⁻ x, ENNReal.ofReal (h x) ∂(densityMeasure I p) =
      ∫⁻ x in I, ENNReal.ofReal (h x * p x) := by
  have hρ : AEMeasurable (fun x => ENNReal.ofReal (p x)) (volume.restrict I) :=
    (hp.aemeasurable hIo.measurableSet).ennreal_ofReal
  have hg : AEMeasurable (fun x => ENNReal.ofReal (h x)) (volume.restrict I) :=
    hh.ennreal_ofReal
  rw [densityMeasure, lintegral_withDensity_eq_lintegral_mul₀ hρ hg]
  refine setLIntegral_congr_fun hIo.measurableSet fun x hx => ?_
  rw [Pi.mul_apply, mul_comm, (ENNReal.ofReal_mul' (hp0 x hx).le).symm]

/-- Jensen-type bound for the logarithmic weight on a measurable set. -/
lemma setIntegral_weight_le {P : Measure ℝ} [IsProbabilityMeasure P] {w : ℝ → ℝ}
    (hwi : Integrable w P)
    (hei : Integrable (fun x => Real.exp (w x)) P)
    (hexp : ∫ x, Real.exp (w x) ∂P = 2) {A : Set ℝ} :
    ∫ x in A, w x ∂P ≤ 2 * tailLogWeight (P A).toReal := by
  set T := (P A).toReal with hT
  rcases (ENNReal.toReal_nonneg : 0 ≤ T).eq_or_lt with h0 | hpos
  · have hz : P A = 0 := by
      have := (ENNReal.toReal_eq_zero_iff _).1 h0.symm
      exact this.resolve_right (measure_ne_top _ _)
    have hT0 : T = 0 := h0.symm
    rw [Measure.restrict_eq_zero.2 hz, hT0]
    simp [tailLogWeight]
  · have hpt : ∀ x, w x ≤ Real.log (2 / T) - 1 + T / 2 * Real.exp (w x) := by
      intro x
      have := log_le_log_add_div (Real.exp_pos (w x)) (show 0 < 2 / T by positivity)
      rw [Real.log_exp] at this
      have e : Real.exp (w x) / (2 / T) = T / 2 * Real.exp (w x) := by
        field_simp
      linarith
    have hAi : Integrable (fun x => Real.log (2 / T) - 1 + T / 2 * Real.exp (w x)) P :=
      (integrable_const _).add (hei.const_mul _)
    have h1 : ∫ x in A, w x ∂P ≤
        ∫ x in A, (Real.log (2 / T) - 1 + T / 2 * Real.exp (w x)) ∂P :=
      setIntegral_mono hwi.integrableOn hAi.integrableOn hpt
    have h2 : ∫ x in A, Real.exp (w x) ∂P ≤ 2 := by
      rw [← hexp]
      exact setIntegral_le_integral hei (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    have h3 : ∫ x in A, (Real.log (2 / T) - 1 + T / 2 * Real.exp (w x)) ∂P =
        T * (Real.log (2 / T) - 1) + T / 2 * ∫ x in A, Real.exp (w x) ∂P := by
      rw [integral_add (integrable_const _).integrableOn (hei.const_mul _).integrableOn,
        integral_const, integral_const_mul]
      simp [Measure.real, hT]
    have h4 := mul_log_two_div_le hpos
    have h5 : T / 2 * ∫ x in A, Real.exp (w x) ∂P ≤ T / 2 * 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith

/-- Right logarithmic resistance constant
`C_+ = sup_{x > a} Ψ(μ([x,b))) ∫_a^x 1/p`, with `Ψ(t) = t log (1 + 1/t)`. -/
noncomputable def rightLogResistanceConstant (I : Set ℝ) (p : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun x => tailLogWeight (densityMeasure I p (Ici x)).toReal * ∫ t in a..x, (p t)⁻¹) ''
    (I ∩ Ioi a))

/-- Left logarithmic resistance constant
`C_- = sup_{x < a} Ψ(μ((l,x])) ∫_x^a 1/p`. -/
noncomputable def leftLogResistanceConstant (I : Set ℝ) (p : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun x => tailLogWeight (densityMeasure I p (Iic x)).toReal * ∫ t in x..a, (p t)⁻¹) ''
    (I ∩ Iio a))

lemma rightLogResistanceConstant_nonneg (hp0 : ∀ x ∈ I, 0 < p x) (hIc : I.OrdConnected)
    (ha : a ∈ I) : 0 ≤ rightLogResistanceConstant I p a := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, ⟨hx, hax⟩, rfl⟩
  have hsub : Icc a x ⊆ I := hIc.out ha hx
  exact mul_nonneg (tailLogWeight_nonneg ENNReal.toReal_nonneg)
    (intervalIntegral.integral_nonneg (le_of_lt hax) fun t ht => (inv_pos.2 (hp0 t (hsub ht))).le)

lemma leftLogResistanceConstant_nonneg (hp0 : ∀ x ∈ I, 0 < p x) (hIc : I.OrdConnected)
    (ha : a ∈ I) : 0 ≤ leftLogResistanceConstant I p a := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, ⟨hx, hxa⟩, rfl⟩
  have hsub : Icc x a ⊆ I := hIc.out hx ha
  exact mul_nonneg (tailLogWeight_nonneg ENNReal.toReal_nonneg)
    (intervalIntegral.integral_nonneg (le_of_lt hxa) fun t ht => (inv_pos.2 (hp0 t (hsub ht))).le)

section Weighted

variable {f f' : ℝ → ℝ}

/-- The weighted Hardy estimate for the logarithmic weight `w = log (1 + g²/G)`,
`g = f - f a`, `G = ∫ g² dμ`. -/
lemma weighted_log_hardy (hIo : IsOpen I) (hIc : I.OrdConnected) (ha : a ∈ I)
    (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x)
    [IsProbabilityMeasure (densityMeasure I p)]
    (hBp : BddAbove ((fun x => tailLogWeight (densityMeasure I p (Ici x)).toReal *
      ∫ t in a..x, (p t)⁻¹) '' (I ∩ Ioi a)))
    (hBm : BddAbove ((fun x => tailLogWeight (densityMeasure I p (Iic x)).toReal *
      ∫ t in x..a, (p t)⁻¹) '' (I ∩ Iio a)))
    (hf : ∀ x ∈ I, ∀ y ∈ I, f y - f x = ∫ t in x..y, f' t)
    (hf' : LocallyIntegrableOn f' I volume) {G : ℝ} (hG : 0 < G)
    (hGd : ∫ x, (f x - f a) ^ 2 ∂(densityMeasure I p) = G)
    (hgi : Integrable (fun x => (f x - f a) ^ 2) (densityMeasure I p))
    (hE : Integrable (fun x => f' x ^ 2) (densityMeasure I p)) :
    Integrable (fun x => (f x - f a) ^ 2 * Real.log (1 + (f x - f a) ^ 2 / G))
      (densityMeasure I p) ∧
    ∫ x, (f x - f a) ^ 2 * Real.log (1 + (f x - f a) ^ 2 / G) ∂(densityMeasure I p) ≤
      8 * max (rightLogResistanceConstant I p a) (leftLogResistanceConstant I p a) *
        ∫ x, f' x ^ 2 ∂(densityMeasure I p) := by
  set μ := densityMeasure I p with hμ
  set w : ℝ → ℝ := fun x => Real.log (1 + (f x - f a) ^ 2 / G) with hw
  have hfc := continuousOn_of_ftc hIo hf hf'
  have hgc : ContinuousOn (fun x => (f x - f a) ^ 2) I := (hfc.sub continuousOn_const).pow 2
  have hpos : ∀ x, 0 < 1 + (f x - f a) ^ 2 / G := fun x => by positivity
  have hwc : ContinuousOn w I :=
    ContinuousOn.log (continuousOn_const.add (hgc.div_const G)) fun x _ => (hpos x).ne'
  have hw0 : ∀ x, 0 ≤ w x := fun x =>
    Real.log_nonneg (by have : 0 ≤ (f x - f a) ^ 2 / G := by positivity
                        linarith)
  have hwle : ∀ x, w x ≤ (f x - f a) ^ 2 / G := fun x => by
    have := Real.log_le_sub_one_of_pos (hpos x)
    simp only [hw]; linarith
  have hμac : μ ≪ volume.restrict I := withDensity_absolutelyContinuous _ _
  have hwa : AEStronglyMeasurable w μ :=
    (hwc.aestronglyMeasurable hIo.measurableSet).mono_ac hμac
  have hga : AEStronglyMeasurable (fun x => (f x - f a) ^ 2) μ := hgi.aestronglyMeasurable
  have hwi : Integrable w μ :=
    Integrable.mono' (hgi.div_const G) hwa
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (hw0 x)]; exact hwle x)
  have hexpe : ∀ x, Real.exp (w x) = 1 + (f x - f a) ^ 2 / G := fun x =>
    Real.exp_log (hpos x)
  have hei : Integrable (fun x => Real.exp (w x)) μ := by
    simp_rw [hexpe]
    exact (integrable_const _).add (hgi.div_const G)
  have hexp : ∫ x, Real.exp (w x) ∂μ = 2 := by
    simp_rw [hexpe]
    rw [integral_add (integrable_const _) (hgi.div_const G), integral_const,
      integral_div, hGd]
    simp [div_self hG.ne']
    norm_num
  have hCR : 0 ≤ rightLogResistanceConstant I p a := rightLogResistanceConstant_nonneg hp0 hIc ha
  have hCL : 0 ≤ leftLogResistanceConstant I p a := leftLogResistanceConstant_nonneg hp0 hIc ha
  have hqc : ContinuousOn (fun x => w x * p x) I := hwc.mul hp
  have hq0 : ∀ x ∈ I, 0 ≤ w x * p x := fun x hx => mul_nonneg (hw0 x) (hp0 x hx).le
  have hjen : ∀ A : Set ℝ, ∫ x in A, w x ∂μ ≤ 2 * tailLogWeight (μ A).toReal := fun A =>
    setIntegral_weight_le hwi hei hexp
  have hB₁ : ∀ x ∈ I, a < x →
      (∫ t in Ici x, w t ∂μ) * ∫ t in a..x, (p t)⁻¹ ≤ 2 * rightLogResistanceConstant I p a := by
    intro x hx hax
    have hW : 0 ≤ ∫ t in a..x, (p t)⁻¹ :=
      intervalIntegral.integral_nonneg hax.le fun t ht => (inv_pos.2 (hp0 t (hIc.out ha hx ht))).le
    have h1 : tailLogWeight (μ (Ici x)).toReal * ∫ t in a..x, (p t)⁻¹ ≤
        rightLogResistanceConstant I p a := le_csSup hBp ⟨x, ⟨hx, hax⟩, rfl⟩
    have h2 := mul_le_mul_of_nonneg_right (hjen (Ici x)) hW
    linarith
  have hB₂ : ∀ x ∈ I, x < a →
      (∫ t in Iic x, w t ∂μ) * ∫ t in x..a, (p t)⁻¹ ≤ 2 * leftLogResistanceConstant I p a := by
    intro x hx hxa
    have hW : 0 ≤ ∫ t in x..a, (p t)⁻¹ :=
      intervalIntegral.integral_nonneg hxa.le fun t ht => (inv_pos.2 (hp0 t (hIc.out hx ha ht))).le
    have h1 : tailLogWeight (μ (Iic x)).toReal * ∫ t in x..a, (p t)⁻¹ ≤
        leftLogResistanceConstant I p a := le_csSup hBm ⟨x, ⟨hx, hxa⟩, rfl⟩
    have h2 := mul_le_mul_of_nonneg_right (hjen (Iic x)) hW
    linarith
  have hard := hardy_of_bounds_w hIo hIc ha hp hp0 hqc hq0
    (TR := fun x => ∫ t in Ici x, w t ∂μ) (TL := fun x => ∫ t in Iic x, w t ∂μ)
    (B₁ := 2 * rightLogResistanceConstant I p a) (B₂ := 2 * leftLogResistanceConstant I p a)
    (fun x hx hax => hasDerivAt_tailIntegral_right hIo hIc hp hp0 hwc hwi ha hx hax)
    (fun x _ _ => setIntegral_nonneg measurableSet_Ici fun t _ => hw0 t) hB₁
    (fun y hy hya => hasDerivAt_tailIntegral_left hIo hIc hp hp0 hwc hwi ha hy hya)
    (fun x _ _ => setIntegral_nonneg measurableSet_Iic fun t _ => hw0 t) hB₂ hf hf'
  have hHc : ContinuousOn (fun x => (f x - f a) ^ 2 * w x) I := hgc.mul hwc
  have hH0 : ∀ x, 0 ≤ (f x - f a) ^ 2 * w x := fun x => mul_nonneg (sq_nonneg _) (hw0 x)
  have hconv : ∫⁻ x, ENNReal.ofReal ((f x - f a) ^ 2 * w x) ∂μ =
      ∫⁻ x in I, ENNReal.ofReal ((f x - f a) ^ 2 * (w x * p x)) := by
    rw [lintegral_densityMeasure_ofReal hIo hp hp0 (hHc.aemeasurable hIo.measurableSet)]
    simp_rw [mul_assoc]
  have hg' : AEMeasurable f' (volume.restrict I) := hf'.aestronglyMeasurable.aemeasurable
  have hE' : ∫⁻ x in I, ENNReal.ofReal (f' x ^ 2 * p x) = ENNReal.ofReal (∫ x, f' x ^ 2 ∂μ) := by
    rw [← lintegral_densityMeasure_sq hIo hp hg']
    exact (ofReal_integral_eq_lintegral_ofReal hE
      (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
  rw [← hconv, hE'] at hard
  have hHa : AEStronglyMeasurable (fun x => (f x - f a) ^ 2 * w x) μ :=
    (hHc.aestronglyMeasurable hIo.measurableSet).mono_ac hμac
  have hlt : ∫⁻ x, ENNReal.ofReal ((f x - f a) ^ 2 * w x) ∂μ < ⊤ :=
    lt_of_le_of_lt hard (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hHi : Integrable (fun x => (f x - f a) ^ 2 * w x) μ :=
    ⟨hHa, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hH0)).2 hlt⟩
  refine ⟨hHi, ?_⟩
  have hE0 : 0 ≤ ∫ x, f' x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hmx : 4 * max (2 * rightLogResistanceConstant I p a) (2 * leftLogResistanceConstant I p a) =
      8 * max (rightLogResistanceConstant I p a) (leftLogResistanceConstant I p a) := by
    rw [← mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]; ring
  rw [hmx] at hard
  have hM0 : 0 ≤ 8 * max (rightLogResistanceConstant I p a) (leftLogResistanceConstant I p a) :=
    by have := le_max_left (rightLogResistanceConstant I p a) (leftLogResistanceConstant I p a)
       linarith
  have h1 : ENNReal.ofReal (∫ x, (f x - f a) ^ 2 * w x ∂μ) =
      ∫⁻ x, ENNReal.ofReal ((f x - f a) ^ 2 * w x) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hHi (Filter.Eventually.of_forall hH0)
  rw [← h1, ← ENNReal.ofReal_mul hM0] at hard
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM0 hE0)).1 hard

end Weighted

section Median

lemma toReal_Ici_le_half {P : Measure ℝ} [IsProbabilityMeasure P] {m x : ℝ} (hmx : m < x)
    (h : 1 / 2 ≤ (P (Iic m)).toReal) : (P (Ici x)).toReal ≤ 1 / 2 := by
  have hd : Disjoint (Iic m) (Ici x) :=
    Set.disjoint_left.2 fun t h1 h2 => absurd (h2.trans h1) (not_le.2 hmx)
  have h1 := measure_union hd (measurableSet_Ici (a := x)) (μ := P)
  have h2 : (P (Iic m ∪ Ici x)).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := P) (s := Iic m ∪ Ici x))
    simpa using this
  rw [h1, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
  linarith

lemma toReal_Iic_le_half {P : Measure ℝ} [IsProbabilityMeasure P] {m x : ℝ} (hxm : x < m)
    (h : 1 / 2 ≤ (P (Ici m)).toReal) : (P (Iic x)).toReal ≤ 1 / 2 := by
  have hd : Disjoint (Ici m) (Iic x) :=
    Set.disjoint_left.2 fun t h1 h2 => absurd (h1.trans h2) (not_le.2 hxm)
  have h1 := measure_union hd (measurableSet_Iic (a := x)) (μ := P)
  have h2 : (P (Ici m ∪ Iic x)).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := P) (s := Ici m ∪ Iic x))
    simpa using this
  rw [h1, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
  linarith

variable {m : ℝ} {f f' : ℝ → ℝ}

/-- **Median logarithmic Hardy LSI criterion.** Let `μ = p dx` be a probability measure on the open
interval `I` with `p > 0` continuous, and let `m ∈ I` be a median of `μ`. If the logarithmic
resistance constants `C_±` (anchored at `m`) are finite, then every absolutely continuous `f` of
finite energy satisfies `Ent_μ(f²) ≤ 200 max(C_+, C_-) ∫ |f'|² dμ`. -/
theorem median_logarithmic_hardy_lsi_criterion (hIo : IsOpen I) (hIc : I.OrdConnected)
    (hm : m ∈ I) (hp : ContinuousOn p I) (hp0 : ∀ x ∈ I, 0 < p x)
    [IsProbabilityMeasure (densityMeasure I p)]
    (hmed₁ : 1 / 2 ≤ (densityMeasure I p (Iic m)).toReal)
    (hmed₂ : 1 / 2 ≤ (densityMeasure I p (Ici m)).toReal)
    (hBp : BddAbove ((fun x => tailLogWeight (densityMeasure I p (Ici x)).toReal *
      ∫ t in m..x, (p t)⁻¹) '' (I ∩ Ioi m)))
    (hBm : BddAbove ((fun x => tailLogWeight (densityMeasure I p (Iic x)).toReal *
      ∫ t in x..m, (p t)⁻¹) '' (I ∩ Iio m)))
    (hf : ∀ x ∈ I, ∀ y ∈ I, f y - f x = ∫ t in x..y, f' t)
    (hf' : LocallyIntegrableOn f' I volume)
    (hE : Integrable (fun x => f' x ^ 2) (densityMeasure I p)) :
    DGPS.homogeneousEntropy (densityMeasure I p) (fun x => f x ^ 2) ≤
      ENNReal.ofReal (200 * max (rightLogResistanceConstant I p m) (leftLogResistanceConstant I p m)
        * ∫ x, f' x ^ 2 ∂(densityMeasure I p)) := by
  set μ := densityMeasure I p with hμ
  set C := max (rightLogResistanceConstant I p m) (leftLogResistanceConstant I p m) with hC
  have hCR : 0 ≤ rightLogResistanceConstant I p m := rightLogResistanceConstant_nonneg hp0 hIc hm
  have hCL : 0 ≤ leftLogResistanceConstant I p m := leftLogResistanceConstant_nonneg hp0 hIc hm
  have hC0 : 0 ≤ C := hCR.trans (le_max_left _ _)
  have hE0 : 0 ≤ ∫ x, f' x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hRle : ∀ x ∈ I, m < x → (μ (Ici x)).toReal * ∫ t in m..x, (p t)⁻¹ ≤
      rightLogResistanceConstant I p m := by
    intro x hx hmx
    have hW : 0 ≤ ∫ t in m..x, (p t)⁻¹ :=
      intervalIntegral.integral_nonneg hmx.le fun t ht => (inv_pos.2 (hp0 t (hIc.out hm hx ht))).le
    have h1 : tailLogWeight (μ (Ici x)).toReal * ∫ t in m..x, (p t)⁻¹ ≤
        rightLogResistanceConstant I p m := le_csSup hBp ⟨x, ⟨hx, hmx⟩, rfl⟩
    have h2 := self_le_tailLogWeight ENNReal.toReal_nonneg (toReal_Ici_le_half hmx hmed₁)
    exact (mul_le_mul_of_nonneg_right h2 hW).trans h1
  have hLle : ∀ x ∈ I, x < m → (μ (Iic x)).toReal * ∫ t in x..m, (p t)⁻¹ ≤
      leftLogResistanceConstant I p m := by
    intro x hx hxm
    have hW : 0 ≤ ∫ t in x..m, (p t)⁻¹ :=
      intervalIntegral.integral_nonneg hxm.le fun t ht => (inv_pos.2 (hp0 t (hIc.out hx hm ht))).le
    have h1 : tailLogWeight (μ (Iic x)).toReal * ∫ t in x..m, (p t)⁻¹ ≤
        leftLogResistanceConstant I p m := le_csSup hBm ⟨x, ⟨hx, hxm⟩, rfl⟩
    have h2 := self_le_tailLogWeight ENNReal.toReal_nonneg (toReal_Iic_le_half hxm hmed₂)
    exact (mul_le_mul_of_nonneg_right h2 hW).trans h1
  have hBp' : BddAbove ((fun x => (μ (Ici x)).toReal * ∫ t in m..x, (p t)⁻¹) '' (I ∩ Ioi m)) :=
    ⟨_, by rintro _ ⟨x, ⟨hx, hmx⟩, rfl⟩; exact hRle x hx hmx⟩
  have hBm' : BddAbove ((fun x => (μ (Iic x)).toReal * ∫ t in x..m, (p t)⁻¹) '' (I ∩ Iio m)) :=
    ⟨_, by rintro _ ⟨x, ⟨hx, hxm⟩, rfl⟩; exact hLle x hx hxm⟩
  have hRB : rightResistanceConstant I p m ≤ rightLogResistanceConstant I p m :=
    Real.sSup_le (by rintro _ ⟨x, ⟨hx, hmx⟩, rfl⟩; exact hRle x hx hmx) hCR
  have hLB : leftResistanceConstant I p m ≤ leftLogResistanceConstant I p m :=
    Real.sSup_le (by rintro _ ⟨x, ⟨hx, hxm⟩, rfl⟩; exact hLle x hx hxm) hCL
  obtain ⟨hgi, hmem, hG4, -⟩ := anchored_half_line_resistance_poincare hIo hIc hm hp hp0 hBp' hBm'
    hf hf' hE
  have hG4' : ∫ x, (f x - f m) ^ 2 ∂μ ≤ 4 * C * ∫ x, f' x ^ 2 ∂μ := by
    have hmx : max (rightResistanceConstant I p m) (leftResistanceConstant I p m) ≤ C :=
      max_le_max hRB hLB
    refine hG4.trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hE0
  set G := ∫ x, (f x - f m) ^ 2 ∂μ with hGd
  have hG0 : 0 ≤ G := integral_nonneg fun x => sq_nonneg _
  rcases hG0.eq_or_lt with hGz | hGpos
  · -- degenerate case: `f` is a.e. constant
    have hae : (fun x => (f x - f m) ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hgi).1 hGz.symm
    have hcongr : (fun x => f x ^ 2) =ᵐ[μ] fun _ => f m ^ 2 := by
      filter_upwards [hae] with x hx
      have : f x - f m = 0 := by simpa using hx
      have : f x = f m := by linarith
      simp [this]
    rw [DGPS.homogeneousEntropy_congr_ae hcongr]
    have hconst : DGPS.homogeneousEntropy μ (fun _ => f m ^ 2) = 0 := by
      by_cases hc : f m ^ 2 = 0
      · exact DGPS.homogeneousEntropy_of_integral_eq_zero (by simp [hc])
      · rw [DGPS.homogeneousEntropy_of_integral_ne_zero (by simpa using hc)]
        simp [DGPS.entropyIntegrand, hc]
    rw [hconst]
    exact bot_le
  · obtain ⟨hHi, hH8⟩ := weighted_log_hardy hIo hIc hm hp hp0 hBp hBm hf hf' hGpos hGd.symm hgi hE
    set s := f m ^ 2 + G with hs
    have hs0 : 0 < s := by positivity
    have hfa : AEMeasurable f μ :=
      ((continuousOn_of_ftc hIo hf hf').aemeasurable hIo.measurableSet).mono_ac
        (withDensity_absolutelyContinuous _ _)
    have hvi : Integrable (fun x => f x ^ 2) μ := hmem.integrable_sq
    have hpt : ∀ x, DGPS.entropyIntegrand s (f x ^ 2) ≤
        39 * (f x - f m) ^ 2 + 3 * G +
          4 * ((f x - f m) ^ 2 * Real.log (1 + (f x - f m) ^ 2 / G)) := by
      intro x
      have := entropyIntegrand_sq_add_le (c := f m) (x := f x - f m) hGpos
      rwa [add_sub_cancel] at this
    have hUi : Integrable (fun x => 39 * (f x - f m) ^ 2 + 3 * G +
        4 * ((f x - f m) ^ 2 * Real.log (1 + (f x - f m) ^ 2 / G))) μ :=
      ((hgi.const_mul 39).add (integrable_const _)).add (hHi.const_mul 4)
    have hmeas : AEMeasurable (fun x => DGPS.entropyIntegrand s (f x ^ 2)) μ := by
      have hv : AEMeasurable (fun x => f x ^ 2) μ := hfa.pow_const 2
      unfold DGPS.entropyIntegrand
      exact ((hv.mul ((hv.div_const s).log)).sub hv).add_const s
    have hEi : Integrable (fun x => DGPS.entropyIntegrand s (f x ^ 2)) μ :=
      Integrable.mono' hUi hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (DGPS.entropyIntegrand_nonneg hs0 (sq_nonneg _))]
          exact hpt x)
    have hmain := homogeneousEntropy_le_ofReal_integral hs0 (fun x => sq_nonneg (f x)) hvi hEi
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 := integral_mono hEi hUi hpt
    have e1 : ∫ x, (39 * (f x - f m) ^ 2 + 3 * G) ∂μ = 39 * G + 3 * G := by
      refine (integral_add (hgi.const_mul 39) (integrable_const _)).trans ?_
      rw [integral_const_mul, integral_const, ← hGd]
      simp
    have e2 : ∫ x, 4 * ((f x - f m) ^ 2 * Real.log (1 + (f x - f m) ^ 2 / G)) ∂μ =
        4 * ∫ x, (f x - f m) ^ 2 * Real.log (1 + (f x - f m) ^ 2 / G) ∂μ :=
      integral_const_mul _ _
    have h2 : ∫ x, (39 * (f x - f m) ^ 2 + 3 * G +
        4 * ((f x - f m) ^ 2 * Real.log (1 + (f x - f m) ^ 2 / G))) ∂μ =
        39 * G + 3 * G + 4 * ∫ x, (f x - f m) ^ 2 * Real.log (1 + (f x - f m) ^ 2 / G) ∂μ :=
      (integral_add ((hgi.const_mul 39).add (integrable_const _)) (hHi.const_mul 4)).trans
        (congrArg₂ (· + ·) e1 e2)
    rw [h2] at h1
    rw [← hC] at hH8
    linarith

end Median

end LogHardy

end DGPS.FiniteN
