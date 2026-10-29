import FullLabeledLSI.Nonvacuity.Prop82.CProfile
import FullLabeledLSI.Nonvacuity.Prop82.CAbs
import FullLabeledLSI.Nonvacuity.Prop82.Subthreshold

/-!
# Lane C, module C4 (part 2): the first variation and the Euler–Lagrange equation

For a nonnegative bounded `H¹` function `u` with `u² ` a raw optimizer and a smooth `φ`
orthogonal to the five test functions, the profile `Fb` of `CProfile.lean` is nonnegative near
`0` and vanishes at `0`; hence its derivative `8 ∫ g φ' - 4 R ∫ u φ log u²` vanishes.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

open SharpLSI

section Competitor

variable {u φ : Torus 1 → ℝ} {t : ℝ}

/-- The competitor density `ρ_t = (u + tφ)² / N(t)`. -/
noncomputable def rho (u φ : Torus 1 → ℝ) (t : ℝ) (x : Torus 1) : ℝ :=
  (u x + t * φ x) ^ 2 / NN u φ t

theorem NN_eq (hu : BM u) (hφ : BM φ) (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1)
    (h0 : ∫ x, 1 * (u x * φ x) ∂haar 1 = 0) (t : ℝ) :
    NN u φ t = 1 + t ^ 2 * ∫ x, φ x ^ 2 ∂haar 1 := by
  unfold NN MM
  rw [integral_quad (BM.const 1) hu hφ t, h0]
  simp [hmass]

theorem one_le_NN (hu : BM u) (hφ : BM φ) (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1)
    (h0 : ∫ x, 1 * (u x * φ x) ∂haar 1 = 0) (t : ℝ) : 1 ≤ NN u φ t := by
  rw [NN_eq hu hφ hmass h0 t]
  have : 0 ≤ ∫ x, φ x ^ 2 ∂haar 1 := integral_nonneg fun x => sq_nonneg _
  nlinarith [sq_nonneg t]

theorem integral_w_sq (t : ℝ) : ∫ x, (u x + t * φ x) ^ 2 ∂haar 1 = NN u φ t := by
  unfold NN MM; simp

theorem rho_integral_mul (hN : NN u φ t ≠ 0) {e : Torus 1 → ℝ} (he : BM e) (hu : BM u)
    (hφ : BM φ) :
    ∫ x, e x * rho u φ t x ∂haar 1 = MM u φ e t / NN u φ t := by
  unfold rho MM
  have : ∀ x, e x * ((u x + t * φ x) ^ 2 / NN u φ t) =
      (NN u φ t)⁻¹ * (e x * (u x + t * φ x) ^ 2) := fun x => by field_simp
  simp_rw [this]
  rw [integral_const_mul]; ring

theorem bddDens_rho (hu : BM u) (hφ : BM φ) (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1)
    (h0 : ∫ x, 1 * (u x * φ x) ∂haar 1 = 0) (t : ℝ) :
    ∃ B, BddDens (rho u φ t) B := by
  obtain ⟨K, hK⟩ := hu.bdd
  obtain ⟨L, hL⟩ := hφ.bdd
  have hN1 := one_le_NN hu hφ hmass h0 t
  have hNpos : 0 < NN u φ t := lt_of_lt_of_le one_pos hN1
  refine ⟨(K + |t| * L) ^ 2, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact ((hu.meas.add (measurable_const.mul hφ.meas)).pow_const 2).div_const _
  · exact fun x => div_nonneg (sq_nonneg _) hNpos.le
  · intro x
    unfold rho
    refine (div_le_self (sq_nonneg _) hN1).trans ?_
    rw [sq_le_sq]
    have hKx := hK x
    have hLx := hL x
    have hK0 : 0 ≤ K := (abs_nonneg _).trans hKx
    have hL0 : 0 ≤ L := (abs_nonneg _).trans hLx
    rw [abs_of_nonneg (by positivity : 0 ≤ K + |t| * L)]
    calc |u x + t * φ x| ≤ |u x| + |t * φ x| := abs_add_le _ _
      _ ≤ K + |t| * L := by
        rw [abs_mul]
        exact add_le_add hKx (mul_le_mul_of_nonneg_left hLx (abs_nonneg _))
  · unfold rho
    rw [integral_div, integral_w_sq]
    exact div_self hNpos.ne'

theorem BM.memLp {f : Torus 1 → ℝ} (h : BM f) : MemLp f 2 (haar 1) := by
  obtain ⟨C, hC⟩ := h.bdd
  exact MemLp.of_bound h.meas.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem BM.w (hu : BM u) (hφ : BM φ) (t : ℝ) : BM (fun x => u x + t * φ x) :=
  hu.add (hφ.const_mul t)

theorem integral_rho_log (hu : BM u) (hφ : BM φ) (hN : 0 < NN u φ t) :
    ∫ x, rho u φ t x * Real.log (rho u φ t x) ∂haar 1 =
      EE u φ t / NN u φ t - Real.log (NN u φ t) := by
  have hw := BM.w hu hφ t
  have i1 : Integrable (fun x => (u x + t * φ x) ^ 2 * Real.log ((u x + t * φ x) ^ 2)) (haar 1) := by
    have := (hw.mul hw.mul_log_sq).integrable
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only; ring
  have i2 : Integrable (fun x => (u x + t * φ x) ^ 2) (haar 1) := hw.sq.integrable
  have hpt : ∀ x, rho u φ t x * Real.log (rho u φ t x) =
      (NN u φ t)⁻¹ * ((u x + t * φ x) ^ 2 * Real.log ((u x + t * φ x) ^ 2)) -
        ((NN u φ t)⁻¹ * Real.log (NN u φ t)) * (u x + t * φ x) ^ 2 := by
    intro x
    unfold rho
    by_cases h0 : u x + t * φ x = 0
    · simp [h0]
    · rw [Real.log_div (pow_ne_zero 2 h0) hN.ne']
      field_simp
  simp_rw [hpt]
  rw [integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_w_sq]
  unfold EE
  field_simp

theorem isWeakGrad_smooth_zero {φ : Torus 1 → ℝ} (hφ : IsSmoothT φ) :
    IsWeakGrad φ (fun y _ => dpart_appA φ 0 y) := by
  have h := isWeakGrad_of_contDiff (f := φ) (hφ.of_le (by simp))
  have e : (fun (y : Torus 1) (_ : Fin 1) => dpart_appA φ 0 y) =
      fun y k => fderiv ℝ (φ ∘ liftT) (secT y) (Pi.single k 1) := by
    funext y k; rw [Subsingleton.elim k 0]; rfl
  rw [e]; exact h

theorem memH1_w (hH : MemH1 (haar 1) u) (hu : BM u) (hφ : IsSmoothT φ) (t : ℝ) :
    MemH1 (haar 1) (fun x => u x + t * φ x) ∧
      (fun x => weakGrad (fun x => u x + t * φ x) x 0) =ᵐ[haar 1]
        fun x => weakGrad u x 0 + t * dpart_appA φ 0 x := by
  have hφb := BM.of_isSmoothT hφ
  have hφ'b := BM.of_isSmoothT (isSmoothT_dpart hφ 0)
  have hw : IsWeakGrad (fun x => u x + t * φ x)
      (fun y _ => weakGrad u y 0 + t * dpart_appA φ 0 y) := by
    have := (isWeakGrad_zero_of_memH1 hH).add ((isWeakGrad_smooth_zero hφ).cmul t)
    exact this
  exact memH1_of_isWeakGrad hw (BM.w hu hφb t).memLp
    ((memLp_weakGrad_zero hH).add (hφ'b.memLp.const_mul t))

theorem sqrt_rho_eq (hN : 0 < NN u φ t) :
    (fun x => Real.sqrt (rho u φ t x)) =
      fun x => |u x + t * φ x| / Real.sqrt (NN u φ t) := by
  funext x
  unfold rho
  rw [Real.sqrt_div' _ hN.le, Real.sqrt_sq_eq_abs]

/-- `√ρ_t ∈ H¹` and the gradient energy of `√ρ_t` is at most `Wd(t)/N(t)`. -/
theorem sqrt_rho_memH1_and_energy (hH : MemH1 (haar 1) u) (hu : BM u) (hφ : IsSmoothT φ)
    (hN : 0 < NN u φ t) :
    MemH1 (haar 1) (fun x => Real.sqrt (rho u φ t x)) ∧
      ∫ x, weakGrad (fun y => Real.sqrt (rho u φ t y)) x 0 ^ 2 ∂haar 1 ≤
        Wd u φ t / NN u φ t := by
  obtain ⟨hw, hwg⟩ := memH1_w hH hu hφ t
  have hc : 0 < Real.sqrt (NN u φ t) := Real.sqrt_pos.2 hN
  rw [sqrt_rho_eq hN]
  obtain ⟨hA, hB⟩ := memH1_abs_div hw hc
  refine ⟨hA, ?_⟩
  have hφ'b := BM.of_isSmoothT (isSmoothT_dpart hφ 0)
  have hG2 : MemLp (fun x => weakGrad u x 0 + t * dpart_appA φ 0 x) 2 (haar 1) :=
    (memLp_weakGrad_zero hH).add (hφ'b.memLp.const_mul t)
  have hsq : Real.sqrt (NN u φ t) ^ 2 = NN u φ t := Real.sq_sqrt hN.le
  unfold Wd
  rw [← integral_div]
  refine integral_mono_ae (memLp_weakGrad_zero hA).integrable_sq (hG2.integrable_sq.div_const _) ?_
  filter_upwards [hB, hwg] with x h1 h2
  rw [hsq, h2] at h1
  exact h1

/-- The upper bound `Fb` for `realDiss - 2 R realGap` of the competitor. -/
theorem realDiss_sub_le_Fb (hH : MemH1 (haar 1) u) (hu : BM u) (hφ : IsSmoothT φ)
    (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1) (ho : Orth u φ) (t : ℝ) :
    ∃ B, ∃ hB : BddDens (rho u φ t) B, ∃ hS : MemH1 (haar 1) (fun x => Real.sqrt (rho u φ t x)),
      realGap (rho u φ t) = GG u φ t ∧
      realDiss (rho u φ t) - 2 * realRate * realGap (rho u φ t) ≤ Fb u φ t := by
  have hφb := BM.of_isSmoothT hφ
  have hN1 := one_le_NN hu hφb hmass ho.o0 t
  have hN : 0 < NN u φ t := lt_of_lt_of_le one_pos hN1
  obtain ⟨B, hB⟩ := bddDens_rho hu hφb hmass ho.o0 t
  obtain ⟨hS, hE⟩ := sqrt_rho_memH1_and_energy hH hu hφ hN
  refine ⟨B, hB, hS, ?_, ?_⟩
  · rw [realGap_eq hB, integral_rho_log hu hφb hN]
    unfold GG momC momS
    have h1 := rho_integral_mul hN.ne' BM.eC hu hφb
    have h2 := rho_integral_mul hN.ne' BM.eS hu hφb
    simp only [eC, eS] at h1 h2
    rw [h1, h2]; rfl
  · rw [realDiss_sub_eq hB hS, integral_rho_log hu hφb hN]
    have h1 := rho_integral_mul hN.ne' BM.eC hu hφb
    have h2 := rho_integral_mul hN.ne' BM.eS hu hφb
    have h3 := rho_integral_mul hN.ne' BM.eP hu hφb
    have h4 := rho_integral_mul hN.ne' BM.eQ hu hφb
    simp only [eC, eS, eP, eQ] at h1 h2 h3 h4
    have e : momC (rho u φ t) = MM u φ eC t / NN u φ t := h1
    have e2 : momS (rho u φ t) = MM u φ eS t / NN u φ t := h2
    have e3 : momP (rho u φ t) = MM u φ eP t / NN u φ t := h3
    have e4 : momQ (rho u φ t) = MM u φ eQ t / NN u φ t := h4
    rw [e, e2, e3, e4]
    unfold Fb
    linarith

theorem bddDens_sq (hu : BM u) (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1) :
    ∃ B, BddDens (fun x => u x ^ 2) B := by
  obtain ⟨K, hK⟩ := hu.bdd
  refine ⟨K ^ 2, hu.sq.meas, fun x => sq_nonneg _, fun x => ?_, hmass⟩
  have := hK x
  exact (sq_le_sq.2 (by rw [abs_of_nonneg ((abs_nonneg _).trans (hK x))]; exact hK x))

/-- At `t = 0` the competitor is the optimizer itself: `Fb 0 = 0` and `GG 0 = realGap`. -/
theorem Fb_zero_and_GG_zero (hu : BM u) (hu0 : ∀ x, 0 ≤ u x) (hH : MemH1 (haar 1) u)
    (hopt : RawOptimizer (fun x => u x ^ 2)) (hφ : IsSmoothT φ) (ho : Orth u φ)
    (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1) :
    Fb u φ 0 = 0 ∧ GG u φ 0 = realGap (fun x => u x ^ 2) := by
  have hφb := BM.of_isSmoothT hφ
  have hφ'b := BM.of_isSmoothT (isSmoothT_dpart hφ 0)
  obtain ⟨B, hB⟩ := bddDens_sq hu hmass
  obtain ⟨hN, hN0⟩ := NN_facts hu hφb hmass ho.o0
  have hu0' : ∫ x, u x * φ x ∂haar 1 = 0 := by simpa using ho.o0
  obtain ⟨_, hE0⟩ := EE_hasDerivAt_zero hu hφb hu0'
  obtain ⟨_, hC0⟩ := MM_hasDerivAt_zero BM.eC hu hφb ho.oC
  obtain ⟨_, hS0⟩ := MM_hasDerivAt_zero BM.eS hu hφb ho.oS
  obtain ⟨_, hP0⟩ := MM_hasDerivAt_zero BM.eP hu hφb ho.oP
  obtain ⟨_, hQ0⟩ := MM_hasDerivAt_zero BM.eQ hu hφb ho.oQ
  have hW0 := (Wd_hasDerivAt_zero (u := u) (φ := φ) (memLp_weakGrad_zero hH) hφ'b).2
  have e : (fun x => Real.sqrt (u x ^ 2)) = u := funext fun x => Real.sqrt_sq (hu0 x)
  have hsq : MemH1 (haar 1) (fun x => Real.sqrt (u x ^ 2)) := by rw [e]; exact hH
  have h1 := realDiss_sub_eq hB hsq
  have h2 := hopt.real_equation
  rw [e] at h1
  have hg := realGap_eq hB
  constructor
  · have h3 : realDiss (fun x => u x ^ 2) - 2 * realRate * realGap (fun x => u x ^ 2) = 0 := by
      rw [h2]; ring
    rw [h1] at h3
    unfold Fb
    rw [hN0, hW0, hE0, hC0, hS0, hP0, hQ0]
    unfold momC momS momP momQ at h3
    simp only [eC, eS, eP, eQ] at *
    simpa using h3
  · unfold GG
    rw [hN0, hE0, hC0, hS0]
    rw [hg]
    unfold momC momS
    simp [eC, eS]

theorem GG_continuousAt (hu : BM u) (hφ : IsSmoothT φ) (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1)
    (ho : Orth u φ) : ContinuousAt (GG u φ) 0 := by
  have hφb := BM.of_isSmoothT hφ
  have hu0' : ∫ x, u x * φ x ∂haar 1 = 0 := by simpa using ho.o0
  obtain ⟨hN, hN0⟩ := NN_facts hu hφb hmass ho.o0
  obtain ⟨hE, _⟩ := EE_hasDerivAt_zero hu hφb hu0'
  obtain ⟨hMC, _⟩ := MM_hasDerivAt_zero BM.eC hu hφb ho.oC
  obtain ⟨hMS, _⟩ := MM_hasDerivAt_zero BM.eS hu hφb ho.oS
  have hN1 : NN u φ 0 ≠ 0 := by rw [hN0]; exact one_ne_zero
  have cN := hN.continuousAt
  unfold GG
  exact (((hE.continuousAt.div cN hN1).sub (cN.log hN1)).add
    ((((hMC.continuousAt.div cN hN1).pow 2).add ((hMS.continuousAt.div cN hN1).pow 2)).div_const 2))

/-- Nonnegativity of the profile near `0`. -/
theorem Fb_eventually_nonneg (hu : BM u) (hu0 : ∀ x, 0 ≤ u x) (hH : MemH1 (haar 1) u)
    (hopt : RawOptimizer (fun x => u x ^ 2)) (hφ : IsSmoothT φ) (ho : Orth u φ)
    (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1) : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ Fb u φ t := by
  have hφb := BM.of_isSmoothT hφ
  obtain ⟨_, hG0⟩ := Fb_zero_and_GG_zero hu hu0 hH hopt hφ ho hmass
  have hpos : 0 < realGap (fun x => u x ^ 2) := realGap_pos hopt.1
  have hc := GG_continuousAt hu hφ hmass ho
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < GG u φ t :=
    hc.eventually (lt_mem_nhds (by rw [hG0]; exact hpos))
  filter_upwards [hev] with t ht
  obtain ⟨B, hB, hS, hGap, hle⟩ := realDiss_sub_le_Fb hH hu hφ hmass ho t
  have hadm : Admissible cosV (cosW 1) (rho u φ t) :=
    admissible_of_realGap_pos hB.nonneg hB.mass hS (by rw [hGap]; exact ht)
  have hq := realRate_le_realQuotient hadm
  have hgp : 0 < realGap (rho u φ t) := realGap_pos hadm
  have : 2 * realRate * realGap (rho u φ t) ≤ realDiss (rho u φ t) := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * realGap (rho u φ t))).1 hq
    linarith
  linarith

theorem first_variation (hu : BM u) (hu0 : ∀ x, 0 ≤ u x) (hH : MemH1 (haar 1) u)
    (hopt : RawOptimizer (fun x => u x ^ 2)) (hφ : IsSmoothT φ) (ho : Orth u φ) :
    8 * (∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1) -
      4 * realRate * ∫ x, u x * φ x * Real.log (u x ^ 2) ∂haar 1 = 0 := by
  have hmass : ∫ x, u x ^ 2 ∂haar 1 = 1 := hopt.1.2.1
  have hφb := BM.of_isSmoothT hφ
  have hφ'b := BM.of_isSmoothT (isSmoothT_dpart hφ 0)
  have hd := Fb_hasDerivAt hu hφb hmass (memLp_weakGrad_zero hH) hφ'b ho
  obtain ⟨hF0, _⟩ := Fb_zero_and_GG_zero hu hu0 hH hopt hφ ho hmass
  have hmin : IsLocalMin (Fb u φ) 0 := by
    filter_upwards [Fb_eventually_nonneg hu hu0 hH hopt hφ ho hmass] with t ht
    rw [hF0]; exact ht
  exact hmin.hasDerivAt_eq_zero hd

end Competitor

section Multipliers

theorem exists_multipliers {V : Type*} [AddCommGroup V] [Module ℝ V] (L : Fin 5 → V →ₗ[ℝ] ℝ)
    (l : V →ₗ[ℝ] ℝ) (h : ∀ v, (∀ j, L j v = 0) → l v = 0) :
    ∃ c : Fin 5 → ℝ, ∀ v, l v = ∑ j, c j * L j v := by
  have hker : ⨅ i, LinearMap.ker (L i) ≤ LinearMap.ker l := by
    intro v hv
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hv
    exact h v hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1
    (mem_span_of_iInf_ker_le_ker hker)
  refine ⟨c, fun v => ?_⟩
  rw [← hc]
  simp

/-- Smooth periodic functions as a real vector space. -/
def smoothSub : Submodule ℝ (Torus 1 → ℝ) where
  carrier := {φ | IsSmoothT φ}
  add_mem' := fun {a b} (ha : IsSmoothT a) (hb : IsSmoothT b) => by
    show IsSmoothT (a + b)
    unfold IsSmoothT at *
    exact ha.add hb
  zero_mem' := by
    show IsSmoothT 0
    unfold IsSmoothT
    exact contDiff_const
  smul_mem' := fun c a (ha : IsSmoothT a) => by
    show IsSmoothT (c • a)
    unfold IsSmoothT at *
    exact ha.const_smul c

theorem mem_smoothSub {φ : Torus 1 → ℝ} : φ ∈ smoothSub ↔ IsSmoothT φ := Iff.rfl

theorem dpart_appA_add {φ ψ : Torus 1 → ℝ} (hφ : IsSmoothT φ) (hψ : IsSmoothT ψ) (y : Torus 1) :
    dpart_appA (φ + ψ) 0 y = dpart_appA φ 0 y + dpart_appA ψ 0 y := by
  unfold dpart_appA
  have h : ((φ + ψ) ∘ liftT) = (φ ∘ liftT) + (ψ ∘ liftT) := rfl
  rw [h, fderiv_add ((hφ.differentiable (by simp)) _) ((hψ.differentiable (by simp)) _)]
  rfl

theorem dpart_appA_smul {φ : Torus 1 → ℝ} (hφ : IsSmoothT φ) (c : ℝ) (y : Torus 1) :
    dpart_appA (c • φ) 0 y = c * dpart_appA φ 0 y := by
  unfold dpart_appA
  have h : ((c • φ) ∘ liftT) = c • (φ ∘ liftT) := rfl
  rw [h, fderiv_const_smul ((hφ.differentiable (by simp)) _)]
  rfl

theorem integrable_g_mul {u φ : Torus 1 → ℝ} (hH : MemH1 (haar 1) u) (hφ : IsSmoothT φ) :
    Integrable (fun x => weakGrad u x 0 * dpart_appA φ 0 x) (haar 1) := by
  obtain ⟨C, hC⟩ := (BM.of_isSmoothT (isSmoothT_dpart hφ 0)).bdd
  exact (integrable_weakGrad_zero hH).mul_bdd
    (BM.of_isSmoothT (isSmoothT_dpart hφ 0)).meas.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem integrable_ulog {u φ : Torus 1 → ℝ} (hu : BM u) (hφ : BM φ) :
    Integrable (fun x => u x * φ x * Real.log (u x ^ 2)) (haar 1) := by
  have := (hφ.mul hu.mul_log_sq).integrable
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only; ring

/-- The first variation functional on smooth functions. -/
noncomputable def ellMap (u : Torus 1 → ℝ) (hu : BM u) (hH : MemH1 (haar 1) u) :
    smoothSub →ₗ[ℝ] ℝ where
  toFun v := 8 * (∫ x, weakGrad u x 0 * dpart_appA (v : Torus 1 → ℝ) 0 x ∂haar 1) -
    4 * realRate * ∫ x, u x * (v : Torus 1 → ℝ) x * Real.log (u x ^ 2) ∂haar 1
  map_add' := by
    intro v w
    have hv : IsSmoothT (v : Torus 1 → ℝ) := v.2
    have hw : IsSmoothT (w : Torus 1 → ℝ) := w.2
    have e1 : ∀ x, dpart_appA ((v + w : smoothSub) : Torus 1 → ℝ) 0 x =
        dpart_appA (v : Torus 1 → ℝ) 0 x + dpart_appA (w : Torus 1 → ℝ) 0 x :=
      fun x => dpart_appA_add hv hw x
    simp_rw [e1]
    have i1 := integrable_g_mul hH hv
    have i2 := integrable_g_mul hH hw
    have i3 := integrable_ulog hu (BM.of_isSmoothT hv)
    have i4 := integrable_ulog hu (BM.of_isSmoothT hw)
    have e2 : ∀ x, u x * ((v + w : smoothSub) : Torus 1 → ℝ) x * Real.log (u x ^ 2) =
        u x * (v : Torus 1 → ℝ) x * Real.log (u x ^ 2) +
          u x * (w : Torus 1 → ℝ) x * Real.log (u x ^ 2) := fun x => by
      simp only [Submodule.coe_add, Pi.add_apply]; ring
    simp_rw [e2, mul_add]
    rw [integral_add i1 i2, integral_add i3 i4]
    ring
  map_smul' := by
    intro c v
    have hv : IsSmoothT (v : Torus 1 → ℝ) := v.2
    have e1 : ∀ x, dpart_appA ((c • v : smoothSub) : Torus 1 → ℝ) 0 x =
        c * dpart_appA (v : Torus 1 → ℝ) 0 x := fun x => dpart_appA_smul hv c x
    simp_rw [e1]
    have e2 : ∀ x, u x * ((c • v : smoothSub) : Torus 1 → ℝ) x * Real.log (u x ^ 2) =
        c * (u x * (v : Torus 1 → ℝ) x * Real.log (u x ^ 2)) := fun x => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring
    simp_rw [e2]
    have e3 : ∀ x, weakGrad u x 0 * (c * dpart_appA (v : Torus 1 → ℝ) 0 x) =
        c * (weakGrad u x 0 * dpart_appA (v : Torus 1 → ℝ) 0 x) := fun x => by ring
    simp_rw [e3]
    rw [integral_const_mul, integral_const_mul]
    simp only [RingHom.id_apply, smul_eq_mul]
    ring

/-- The constraint functionals `φ ↦ ∫ e_j u φ`. -/
noncomputable def orthMap (u : Torus 1 → ℝ) (hu : BM u) (j : Fin 5) : smoothSub →ₗ[ℝ] ℝ where
  toFun v := ∫ x, eTest j x * (u x * (v : Torus 1 → ℝ) x) ∂haar 1
  map_add' := by
    intro v w
    have hv := BM.of_isSmoothT v.2
    have hw := BM.of_isSmoothT w.2
    have i1 := ((BM.eTest j).mul (hu.mul hv)).integrable
    have i2 := ((BM.eTest j).mul (hu.mul hw)).integrable
    simp only [Submodule.coe_add, Pi.add_apply, mul_add]
    exact integral_add i1 i2
  map_smul' := by
    intro c v
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1; funext x; ring

theorem eTest_zero : eTest 0 = fun _ => 1 := by funext x; rfl
theorem eTest_one : eTest 1 = eC := by funext x; rfl
theorem eTest_two : eTest 2 = eS := by funext x; rfl
theorem eTest_three : eTest 3 = eP := by funext x; rfl
theorem eTest_four : eTest 4 = eQ := by funext x; rfl

theorem orth_of_orthMap {u φ : Torus 1 → ℝ} (hu : BM u) (hφ : IsSmoothT φ)
    (h : ∀ j, orthMap u hu j ⟨φ, hφ⟩ = 0) : Orth u φ := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  simp only [orthMap, LinearMap.coe_mk, AddHom.coe_mk, eTest_zero, eTest_one, eTest_two,
    eTest_three, eTest_four] at h0 h1 h2 h3 h4
  exact ⟨h0, h1, h2, h3, h4⟩

/-- **Euler–Lagrange equation** (weak form, against smooth periodic tests). -/
theorem euler_lagrange {u : Torus 1 → ℝ} (hu : BM u) (hu0 : ∀ x, 0 ≤ u x)
    (hH : MemH1 (haar 1) u) (hopt : RawOptimizer (fun x => u x ^ 2)) :
    ∃ c : Fin 5 → ℝ, ∀ φ : Torus 1 → ℝ, IsSmoothT φ →
      8 * (∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1) -
        4 * realRate * (∫ x, u x * φ x * Real.log (u x ^ 2) ∂haar 1) =
      ∫ x, (∑ j, c j * eTest j x) * (u x * φ x) ∂haar 1 := by
  obtain ⟨c, hc⟩ := exists_multipliers (orthMap u hu) (ellMap u hu hH) (by
    intro v hv
    exact first_variation hu hu0 hH hopt v.2 (orth_of_orthMap hu v.2 (by simpa using hv)))
  refine ⟨c, fun φ hφ => ?_⟩
  have := hc ⟨φ, hφ⟩
  simp only [ellMap, orthMap, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this]
  have hφb := BM.of_isSmoothT hφ
  have : ∀ x, (∑ j, c j * eTest j x) * (u x * φ x) = ∑ j, c j * (eTest j x * (u x * φ x)) :=
    fun x => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  rw [integral_finset_sum _ (fun j _ => (((BM.eTest j).mul (hu.mul hφb)).integrable.const_mul (c j)))]
  exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul]

end Multipliers

end SharpLSI.FL.Prop82
