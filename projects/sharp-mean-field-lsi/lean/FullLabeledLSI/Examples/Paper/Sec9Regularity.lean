import FullLabeledLSI.Examples.Paper.Sec9RegularityB
import FullLabeledLSI.Examples.Paper.Sec9RegularityC
import FullLabeledLSI.Examples.E01_AttractiveStatements

/-!
# Section 9 regularity (H8): minimizers of `S_{r,A}` and weak Euler solutions are smooth and positive

Lane C of the Section 9 formalization.  Steps 1 and 4-7 of `Audit/FLX/laneC/PLAN_C.md`:

* a continuous representative `F∘secT` of an `H¹` function (module A);
* from the weak Euler equation `4∫u'φ' + ∫Auφ - 4r∫u log u φ = η∫uφ` (module C proves it for
  minimizers) the representative is `C²`, solves `F'' = F((A-η)/4 - r log F)`;
* positivity for `r ≥ 0` (module B), smoothness bootstrap for `A` smooth (module B).

Exports (namespace `SharpLSI.FL.Ex`):
* `weakEL_regularity_ae`, `weakEL_regularity_ae_smooth`: regularity of a nonnegative `H¹` solution of
  the weak Euler equation (`WeakEL`), needed by lane D (critical points, not only minimizers);
* `sMin_regularity_ae`, `sMin_regularity_ae_smooth` (the latter has exactly the statement of the
  E01a stub `sMin_regularity`), `sMin_regularity_of_continuous` (pointwise form for continuous `f`).

Small copies from `FullLabeledLSI/Nonvacuity/Prop82/{CRegularity,CVariation,CFinal}.lean` (branch
`claude/prop82-lane-c-s8pz05`, commit `ce7043d`; namespace changed, otherwise unmodified):
`nonneg_of_continuous_ae`, `memH1_congr_ae'`, `hasDerivAt_of_integral_rel`, `BM.ofF`, `F_secT_lineT`,
`integrable_g_mul`, `integrable_ulog`, `exists_pos_of_integral_sq`; `regular_core` is an adaptation of
`CRegularity.regular_core`.
-/

open MeasureTheory InformationTheory Filter Topology Set
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Ex.Reg

open SharpLSI

/-! ### Copies -/

theorem nonneg_of_continuous_ae {f : ℝ → ℝ} (hf : Continuous f) (h : ∀ᵐ x : ℝ, 0 ≤ f x) :
    ∀ x, 0 ≤ f x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := hcon
  have hopen : IsOpen {y | f y < 0} := isOpen_lt hf continuous_const
  have hpos : 0 < volume {y | f y < 0} := hopen.measure_pos volume ⟨x, hx⟩
  have h0 : volume {y | ¬ 0 ≤ f y} = 0 := ae_iff.1 h
  have : {y | f y < 0} ⊆ {y | ¬ 0 ≤ f y} := fun y hy => not_le.2 hy
  exact absurd (measure_mono_null this h0) hpos.ne'

theorem memH1_congr_ae' {u v : Torus 1 → ℝ} (hu : MemH1 (haar 1) u) (huv : u =ᵐ[haar 1] v) :
    MemH1 (haar 1) v ∧ (fun x => weakGrad v x 0) =ᵐ[haar 1] fun x => weakGrad u x 0 := by
  obtain ⟨hg, hgg⟩ := weakGrad_congr_ae hu.1 huv
  refine ⟨⟨hg, hu.2.1.ae_eq huv, hu.2.2.ae_eq ?_⟩, ?_⟩
  · filter_upwards [hgg] with y hy
    rw [hy]
  · filter_upwards [hgg] with y hy
    rw [hy]

theorem hasDerivAt_of_integral_rel {F H : ℝ → ℝ} (hH : Continuous H)
    (hrel : ∀ s t, F t - F s = ∫ r in s..t, H r) (t : ℝ) : HasDerivAt F (H t) t := by
  have h1 := (hH.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (F 0)
  convert h1 using 1
  funext x
  have := hrel 0 x
  linarith

theorem BM.ofF {F : ℝ → ℝ} (hc : Continuous F) : BM (fun y : Torus 1 => F (secT y 0)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    (s := Icc (0 : ℝ) 1)
  exact ⟨hc.measurable.comp (measurable_secT.eval (a := 0)),
    ⟨C, fun y => by simpa using hC _ (secT_mem_Icc y)⟩⟩

theorem F_secT_lineT {F : ℝ → ℝ} (hp : Function.Periodic F 1) (r : ℝ) :
    F (secT (lineT r) 0) = F r := by
  obtain ⟨m, hm⟩ := secT_lineT_sub r
  rw [hm]
  simpa using hp.int_mul m r

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

/-- If `∫₀¹ F² = 1` and `F ≥ 0` is a function then `F` is somewhere positive. -/
theorem exists_pos_of_integral_sq {F : ℝ → ℝ} (h : ∫ x in (0 : ℝ)..1, F x ^ 2 = 1) :
    ∃ x, 0 < F x ∨ F x < 0 := by
  by_contra hcon
  have hcon' : ∀ x, ¬(0 < F x ∨ F x < 0) := fun x hx => hcon ⟨x, hx⟩
  simp only [not_or, not_lt] at hcon'
  have hz : ∀ x, F x = 0 := fun x => le_antisymm (hcon' x).1 (hcon' x).2
  have h0 : (fun x => F x ^ 2) = fun _ => (0 : ℝ) := by funext x; rw [hz x]; norm_num
  rw [h0] at h
  simp at h


/-! ### Torus/line bookkeeping -/

theorem continuous_lineT : Continuous lineT :=
  continuous_liftT.comp (continuous_pi fun _ => continuous_id)

theorem periodic_deriv {G : ℝ → ℝ} (hp : Function.Periodic G 1) : Function.Periodic (deriv G) 1 := by
  intro x
  have h := deriv_comp_add_const G 1 x
  have e : (fun y => G (y + 1)) = G := funext hp
  rw [e] at h
  exact h.symm

/-- A 1-periodic function of `secT` is its own lift. -/
theorem comp_secT_lift {G : ℝ → ℝ} (hp : Function.Periodic G 1) :
    (fun y : Torus 1 => G (secT y 0)) ∘ liftT = fun z : Fin 1 → ℝ => G (z 0) := by
  funext z
  obtain ⟨m, hm⟩ := secT_liftT_eq z
  simp only [Function.comp_apply, hm]
  have h0 : (z + intVec m) 0 = z 0 + (m 0 : ℝ) := by simp [intVec]
  rw [h0]
  have h1 := (hp.int_mul (m 0)) (z 0)
  simp only [mul_one] at h1
  rw [h1]

theorem rep_eq_secT_add (y : Torus 1) : ∃ n : ℤ, rep y = secT y 0 + n := by
  have h1 : ((rep y : ℝ) : UnitAddCircle) = y 0 :=
    Classical.choose_spec (QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ)) (y 0))
  have h2 : ((secT y 0 : ℝ) : UnitAddCircle) = y 0 := congrFun (liftT_secT y) 0
  have h3 : ((rep y - secT y 0 : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, h1, h2, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
  refine ⟨n, ?_⟩
  simp only [zsmul_eq_mul, mul_one] at hn
  linarith

theorem periodic_rep {H : ℝ → ℝ} (hp : Function.Periodic H 1) (y : Torus 1) :
    H (rep y) = H (secT y 0) := by
  obtain ⟨n, hn⟩ := rep_eq_secT_add y
  rw [hn]
  have h1 := (hp.int_mul n) (secT y 0)
  simpa using h1

/-- `dT` of a 1-periodic function composed with `secT`. -/
theorem dT_comp_secT {G : ℝ → ℝ} (hp : Function.Periodic G 1) (y : Torus 1) :
    dT (fun y : Torus 1 => G (secT y 0)) y = deriv G (secT y 0) := by
  have h : (fun t : ℝ => (fun y : Torus 1 => G (secT y 0)) (liftT (fun _ : Fin 1 => t))) = G := by
    funext t
    exact congrFun (comp_secT_lift hp) (fun _ : Fin 1 => t)
  unfold dT
  rw [h]
  exact periodic_rep (periodic_deriv hp) y

theorem dT_dT_comp_secT {G : ℝ → ℝ} (hp : Function.Periodic G 1) (y : Torus 1) :
    dT (dT (fun y : Torus 1 => G (secT y 0))) y = deriv (deriv G) (secT y 0) := by
  have h : dT (fun y : Torus 1 => G (secT y 0)) = fun y : Torus 1 => deriv G (secT y 0) :=
    funext (dT_comp_secT hp)
  rw [h]
  exact dT_comp_secT (periodic_deriv hp) y

/-! ### The weak Euler equation -/

/-- The weak Euler--Lagrange equation `4∫f'φ' + ∫Afφ - 4r∫f log f φ = η∫fφ` for smooth tests `φ`
(`-4f'' + Af - 4r f log f = ηf` in the weak sense). -/
def WeakEL (r : ℝ) (A f : Torus 1 → ℝ) (η : ℝ) : Prop :=
  ∀ φ : Torus 1 → ℝ, IsSmoothT φ →
    ∫ x, (4 * weakGrad f x 0 * dpart_appA φ 0 x + A x * f x * φ x -
        4 * r * f x * Real.log (f x) * φ x) ∂haar 1 = η * ∫ x, f x * φ x ∂haar 1

/-- Splitting the integral of `WeakEL` for bounded `u ∈ H¹`. -/
theorem weakEL_integral_eq {r : ℝ} {A u φ : Torus 1 → ℝ} (hA : BM A) (hu : BM u)
    (hH : MemH1 (haar 1) u) (hφ : IsSmoothT φ) :
    ∫ x, (4 * weakGrad u x 0 * dpart_appA φ 0 x + A x * u x * φ x -
        4 * r * u x * Real.log (u x) * φ x) ∂haar 1 =
      4 * (∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1) +
        (∫ x, A x * (u x * φ x) ∂haar 1) -
        2 * r * (∫ x, u x * φ x * Real.log (u x ^ 2) ∂haar 1) := by
  have hφb := BM.of_isSmoothT hφ
  have i1 := integrable_g_mul hH hφ
  have i2 : Integrable (fun x => A x * (u x * φ x)) (haar 1) := (hA.mul (hu.mul hφb)).integrable
  have i3 := integrable_ulog hu hφb
  have e : ∀ x, 4 * weakGrad u x 0 * dpart_appA φ 0 x + A x * u x * φ x -
        4 * r * u x * Real.log (u x) * φ x =
      4 * (weakGrad u x 0 * dpart_appA φ 0 x) + A x * (u x * φ x) -
        2 * r * (u x * φ x * Real.log (u x ^ 2)) := by
    intro x
    rw [Real.log_pow]
    push_cast
    ring
  simp_rw [e]
  have j : Integrable (fun x => 4 * (weakGrad u x 0 * dpart_appA φ 0 x) + A x * (u x * φ x))
      (haar 1) := (i1.const_mul 4).add i2
  rw [integral_sub j (i3.const_mul (2 * r)), integral_add (i1.const_mul 4) i2, integral_const_mul,
    integral_const_mul]

/-- A bounded measurable minimizer satisfies the weak Euler equation, with `η = S(u)`. -/
theorem weakEL_of_min {r : ℝ} {A u : Torus 1 → ℝ} (hA : BM A) (hu : BM u)
    (hH : MemH1 (haar 1) u) (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1)
    (hmin : ∀ g : Torus 1 → ℝ, (∀ x, 0 ≤ g x) → MemH1 (haar 1) g → ∫ x, g x ^ 2 ∂haar 1 = 1 →
      Sfun r A u ≤ Sfun r A g) : WeakEL r A u (Sfun r A u) := by
  intro φ hφ
  rw [weakEL_integral_eq hA hu hH hφ]
  exact weak_euler hA hu hH hmass hmin hφ

/-! ### Regularity of a continuous periodic solution -/

/-- Core of the regularity argument, for a continuous periodic representative (adapted from
`CRegularity.regular_core`). -/
theorem regular_core {F : ℝ → ℝ} (hc : Continuous F) (hp : Function.Periodic F 1)
    {A : Torus 1 → ℝ} (hA : Continuous A) {r η : ℝ} {g₀ : Torus 1 → ℝ}
    (hrel : ∀ s t, F t - F s = ∫ s' in s..t, g₀ (lineT s'))
    (hu : MemH1 (haar 1) (fun y => F (secT y 0)))
    (hgu : (fun y => weakGrad (fun y => F (secT y 0)) y 0) =ᵐ[haar 1] g₀)
    (hweak : WeakEL r A (fun y => F (secT y 0)) η) :
    ContDiff ℝ 2 F ∧
      ∀ x, deriv (deriv F) x = F x * ((A (lineT x) - η) / 4 - r * Real.log (F x)) := by
  set ũ : Torus 1 → ℝ := fun y => F (secT y 0) with hũ
  have hBM : BM ũ := BM.ofF hc
  have hAb : BM A := BM.of_continuous hA
  set ht : Torus 1 → ℝ := fun y =>
    (1 / 4) * (ũ y * A y - η * ũ y - 2 * r * (ũ y * Real.log (ũ y ^ 2))) with hht
  have hhtBM : BM ht :=
    (BM.const (1 / 4)).mul (((hBM.mul hAb).sub ((BM.const η).mul hBM)).sub
      ((BM.const (2 * r)).mul hBM.mul_log_sq))
  have hweak' : IsWeakGrad (fun y => weakGrad ũ y 0) (fun y _ => ht y) := by
    refine isWeakGrad_of_smooth_tests (memLp_weakGrad_zero hu) hhtBM.memLp ?_
    intro φ hφ
    have hφb := BM.of_isSmoothT hφ
    have h1 := hweak φ hφ
    rw [weakEL_integral_eq hAb hBM hu hφ] at h1
    have i2 : Integrable (fun y => A y * (ũ y * φ y)) (haar 1) := (hAb.mul (hBM.mul hφb)).integrable
    have j2 : Integrable (fun y => ũ y * φ y) (haar 1) := (hBM.mul hφb).integrable
    have i3 := integrable_ulog hBM hφb
    have e1 : ∀ y, ht y * φ y = (1 / 4) * (A y * (ũ y * φ y)) - (η / 4) * (ũ y * φ y) -
        (r / 2) * (ũ y * φ y * Real.log (ũ y ^ 2)) := fun y => by simp only [hht]; ring
    simp_rw [e1]
    have k1 : Integrable (fun y => (1 / 4) * (A y * (ũ y * φ y)) - (η / 4) * (ũ y * φ y))
        (haar 1) := (i2.const_mul _).sub (j2.const_mul _)
    rw [integral_sub k1 (i3.const_mul (r / 2)), integral_sub (i2.const_mul (1 / 4)) (j2.const_mul (η / 4)),
      integral_const_mul, integral_const_mul, integral_const_mul]
    linarith
  -- continuous representative of the derivative
  obtain ⟨G, hGc, hGp, hGrel, hGae, -⟩ := exists_continuous_rep hweak'
    ((memLp_weakGrad_zero hu).integrable one_le_two) hhtBM.integrable
  have hlin : ∀ s, ũ (lineT s) = F s := by
    intro s
    obtain ⟨m, hm⟩ := secT_lineT_sub s
    simp only [hũ, hm]
    simpa using hp.int_mul m s
  set Hn : ℝ → ℝ := fun s =>
    F s * ((A (lineT s) - η) / 4) - r * (F s * Real.log (F s)) with hHn
  have hHnc : Continuous Hn :=
    (hc.mul (((hA.comp continuous_lineT).sub continuous_const).div_const 4)).sub
      (continuous_const.mul (Real.continuous_mul_log.comp hc))
  have hhtline : ∀ s, ht (lineT s) = Hn s := by
    intro s
    simp only [hht, hlin, hHn]
    rw [Real.log_pow]
    push_cast
    ring
  have hGrel' : ∀ s t, G t - G s = ∫ s' in s..t, Hn s' := by
    intro s t
    rw [hGrel]
    exact intervalIntegral.integral_congr (fun s' _ => hhtline s')
  have hGd : ∀ t, HasDerivAt G (Hn t) t := hasDerivAt_of_integral_rel hHnc hGrel'
  have hae1 : ∀ᵐ s : ℝ, g₀ (lineT s) = G s := by
    have h0 : ∀ᵐ y ∂haar 1, g₀ y = G (secT y 0) := by
      filter_upwards [hgu, hGae] with y h1 h2
      rw [← h1]; exact h2
    filter_upwards [ae_real_of_ae_torus h0] with s hs
    rw [hs]
    obtain ⟨m, hm⟩ := secT_lineT_sub s
    rw [hm]
    simpa using hGp.int_mul m s
  have hFrel : ∀ s t, F t - F s = ∫ s' in s..t, G s' := by
    intro s t
    rw [hrel]
    exact intervalIntegral.integral_congr_ae (hae1.mono fun s' hs' _ => hs')
  have hFd : ∀ t, HasDerivAt F (G t) t := hasDerivAt_of_integral_rel hGc hFrel
  have hdF : deriv F = G := funext fun t => (hFd t).deriv
  have hdG : deriv G = Hn := funext fun t => (hGd t).deriv
  have hG1 : ContDiff ℝ 1 G :=
    contDiff_one_iff_deriv.2 ⟨fun t => (hGd t).differentiableAt, by rw [hdG]; exact hHnc⟩
  refine ⟨?_, ?_⟩
  · have : ContDiff ℝ ((1 : ℕ) + 1 : ℕ) F := by
      refine (contDiff_succ_iff_deriv (n := 1)).2 ⟨fun t => (hFd t).differentiableAt, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · rw [hdF]; exact hG1
    simpa using this
  · intro x
    rw [hdF, hdG]
    simp only [hHn]; ring

/-! ### Positivity and smoothness: the master theorem -/

theorem weakEL_master {r : ℝ} (hr : 0 ≤ r) {A : Torus 1 → ℝ} (hA : Continuous A)
    {f : Torus 1 → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : MemH1 (haar 1) f)
    (hf1 : ∫ x, f x ^ 2 ∂haar 1 = 1) {η : ℝ} (hweak : WeakEL r A f η) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ Function.Periodic F 1 ∧ (∀ x, 0 < F x) ∧
      (∀ x, deriv (deriv F) x = F x * ((A (lineT x) - η) / 4 - r * Real.log (F x))) ∧
      (IsSmoothT A → ContDiff ℝ ∞ F) ∧ (fun y => F (secT y 0)) =ᵐ[haar 1] f := by
  obtain ⟨F, hc, hp, hrel, hae, haeR⟩ := exists_continuous_rep_memH1 hf
  have hnn : ∀ x, 0 ≤ F x := by
    refine nonneg_of_continuous_ae hc ?_
    filter_upwards [haeR] with s hs
    rw [← hs]; exact hf0 _
  have hae' : f =ᵐ[haar 1] fun y => F (secT y 0) := hae
  obtain ⟨hu, hgu⟩ := memH1_congr_ae' hf hae'
  have hweak' : WeakEL r A (fun y => F (secT y 0)) η := by
    intro φ hφ
    have h1 := hweak φ hφ
    show ∫ x, (4 * weakGrad (fun y => F (secT y 0)) x 0 * dpart_appA φ 0 x +
        A x * F (secT x 0) * φ x - 4 * r * F (secT x 0) * Real.log (F (secT x 0)) * φ x) ∂haar 1 =
      η * ∫ x, F (secT x 0) * φ x ∂haar 1
    have e1 : ∫ x, (4 * weakGrad (fun y => F (secT y 0)) x 0 * dpart_appA φ 0 x +
        A x * F (secT x 0) * φ x - 4 * r * F (secT x 0) * Real.log (F (secT x 0)) * φ x) ∂haar 1 =
        ∫ x, (4 * weakGrad f x 0 * dpart_appA φ 0 x + A x * f x * φ x -
          4 * r * f x * Real.log (f x) * φ x) ∂haar 1 := by
      refine integral_congr_ae ?_
      filter_upwards [hae, hgu] with x h1 h2
      rw [h2, h1]
    have e2 : ∫ x, F (secT x 0) * φ x ∂haar 1 = ∫ x, f x * φ x ∂haar 1 := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    rw [e1, e2]
    exact h1
  obtain ⟨hF2, hode⟩ := regular_core hc hp hA (g₀ := fun y => weakGrad f y 0) hrel hu hgu hweak'
  -- boundedness of the zeroth-order coefficient
  obtain ⟨CA, hCA⟩ := (BM.of_continuous hA).bdd
  have hB : ∀ x, |(A (lineT x) - η) / 4| ≤ (CA + |η|) / 4 := by
    intro x
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    calc |A (lineT x) - η| ≤ |A (lineT x)| + |η| := abs_sub _ _
      _ ≤ CA + |η| := by linarith [hCA (lineT x)]
  have hBMu : BM (fun y : Torus 1 => F (secT y 0)) := BM.ofF hc
  have hint : ∫ x in (0 : ℝ)..1, F x ^ 2 = 1 := by
    calc ∫ x in (0 : ℝ)..1, F x ^ 2
        = ∫ x in (0 : ℝ)..1, (fun y : Torus 1 => F (secT y 0) ^ 2) (lineT x) := by
          refine intervalIntegral.integral_congr fun x _ => ?_
          simp only [F_secT_lineT hp]
      _ = ∫ y, F (secT y 0) ^ 2 ∂haar 1 :=
          intervalIntegral_lineT hBMu.sq.integrable.aestronglyMeasurable
      _ = ∫ y, f y ^ 2 ∂haar 1 := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with y hy
          rw [hy]
      _ = 1 := hf1
  have hex : ∃ x, 0 < F x := by
    obtain ⟨x, hx | hx⟩ := exists_pos_of_integral_sq hint
    · exact ⟨x, hx⟩
    · exact absurd (hnn x) (not_le.2 hx)
  have hdF : Differentiable ℝ F := hF2.differentiable (by norm_num)
  have hF1 : ContDiff ℝ 1 (deriv F) := contDiff_one_deriv_of_two hF2
  have hd1 : ∀ x, HasDerivAt F (deriv F x) x := fun x => (hdF x).hasDerivAt
  have hd2 : ∀ x, HasDerivAt (deriv F) (deriv (deriv F) x) x :=
    fun x => ((hF1.differentiable one_ne_zero) x).hasDerivAt
  have hpos : ∀ x, 0 < F x :=
    pos_of_ode_of_nonneg hr hB hd1 hd2 hnn hode hp hex
  refine ⟨F, hF2, hp, hpos, hode, ?_, hae'.symm⟩
  intro hAs
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => A (lineT s)) :=
    hAs.comp (contDiff_pi.2 fun _ => contDiff_id)
  have hBs : ContDiff ℝ ∞ (fun x : ℝ => (A (lineT x) - η) / 4) :=
    (h1.sub contDiff_const).div_const 4
  exact contDiff_top_of_ode hBs hF2 hpos hode

/-! ### Minimizers: continuous representative and weak equation -/

theorem Sfun_congr_ae {r : ℝ} {A f u : Torus 1 → ℝ} (hf : MemH1 (haar 1) f)
    (hae : f =ᵐ[haar 1] u) : Sfun r A f = Sfun r A u := by
  obtain ⟨_, hg⟩ := memH1_congr_ae' hf hae
  have e1 : ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 = ∫ x, weakGrad u x 0 ^ 2 ∂haar 1 := by
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx]
  have e2 : ∫ x, A x * f x ^ 2 ∂haar 1 = ∫ x, A x * u x ^ 2 ∂haar 1 := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have e3 : densMeasure (fun x => f x ^ 2) = densMeasure (fun x => u x ^ 2) :=
    densMeasure_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
  unfold Sfun
  rw [e1, e2, e3]

/-- A minimizer has a continuous representative `u` (bounded, nonnegative, in `H¹`) satisfying the
weak Euler equation with `η = S(f)`. -/
theorem sMin_weakEL {r : ℝ} {A : Torus 1 → ℝ} (hA : Continuous A) {f : Torus 1 → ℝ}
    (hf : IsSMin r A f) :
    ∃ u : Torus 1 → ℝ, u =ᵐ[haar 1] f ∧ (∀ x, 0 ≤ u x) ∧ MemH1 (haar 1) u ∧
      ∫ x, u x ^ 2 ∂haar 1 = 1 ∧ WeakEL r A u (sFunctional r A f) := by
  obtain ⟨hf0, hfH, hf1, hfmin⟩ := hf
  obtain ⟨F, hc, hp, hrel, hae, haeR⟩ := exists_continuous_rep_memH1 hfH
  have hnn : ∀ x, 0 ≤ F x := by
    refine nonneg_of_continuous_ae hc ?_
    filter_upwards [haeR] with s hs
    rw [← hs]; exact hf0 _
  have hae' : f =ᵐ[haar 1] fun y => F (secT y 0) := hae
  obtain ⟨hu, _⟩ := memH1_congr_ae' hfH hae'
  have hBM : BM (fun y : Torus 1 => F (secT y 0)) := BM.ofF hc
  have hmass : ∫ x, F (secT x 0) ^ 2 ∂haar 1 = 1 := by
    refine Eq.trans ?_ hf1
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have hS : Sfun r A (fun y => F (secT y 0)) = sFunctional r A f :=
    (Sfun_congr_ae hfH hae').symm
  have hmin : ∀ g : Torus 1 → ℝ, (∀ x, 0 ≤ g x) → MemH1 (haar 1) g → ∫ x, g x ^ 2 ∂haar 1 = 1 →
      Sfun r A (fun y => F (secT y 0)) ≤ Sfun r A g := by
    intro g hg0 hgH hg1
    rw [hS]
    exact hfmin g hg0 hgH hg1
  have := weakEL_of_min (BM.of_continuous hA) hBM hu hmass hmin
  rw [hS] at this
  exact ⟨_, hae'.symm, fun x => hnn _, hu, hmass, this⟩

end SharpLSI.FL.Ex.Reg

/-! ### Exported statements -/

namespace SharpLSI.FL.Ex

open SharpLSI

/-- **Regularity of nonnegative weak Euler solutions** (lane D, Lemma 9.9(ii); also the second half of
H8): `f ≥ 0` in `H¹`, `∫ f² = 1`, solving the weak equation
`4∫f'φ' + ∫Afφ - 4r∫f log f φ = η∫fφ` for all smooth `φ`, agrees a.e. with a `C²` strictly positive
`g` solving `-4g'' + Ag - 4r g log g = ηg` pointwise (`r ≥ 0`, `A` continuous). -/
theorem weakEL_regularity_ae {r : ℝ} (hr : 0 ≤ r) {A : Torus 1 → ℝ} (hA : Continuous A)
    {f : Torus 1 → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : MemH1 (haar 1) f)
    (hf1 : ∫ x, f x ^ 2 ∂haar 1 = 1) {η : ℝ} (hweak : Reg.WeakEL r A f η) :
    ∃ g : Torus 1 → ℝ, g =ᵐ[haar 1] f ∧ ContDiff ℝ 2 (g ∘ liftT) ∧ (∀ x, 0 < g x) ∧
      ∀ x : Torus 1, -4 * dT (dT g) x + A x * g x - 4 * r * g x * Real.log (g x) = η * g x := by
  obtain ⟨F, hF2, hp, hpos, hode, -, hae⟩ := Reg.weakEL_master hr hA hf0 hf hf1 hweak
  refine ⟨fun y => F (secT y 0), hae, ?_, fun y => hpos _, ?_⟩
  · rw [Reg.comp_secT_lift hp]
    exact hF2.comp (contDiff_apply ℝ ℝ 0)
  · intro x
    show -4 * dT (dT (fun y => F (secT y 0))) x + A x * F (secT x 0) -
      4 * r * F (secT x 0) * Real.log (F (secT x 0)) = η * F (secT x 0)
    rw [Reg.dT_dT_comp_secT hp x]
    have h := hode (secT x 0)
    have hA' : A x = A (lineT (secT x 0)) := by rw [Reg.lineT_secT]
    rw [hA', h]
    ring

/-- Same as `weakEL_regularity_ae` for smooth `A`: the representative is smooth. -/
theorem weakEL_regularity_ae_smooth {r : ℝ} (hr : 0 ≤ r) {A : Torus 1 → ℝ} (hA : IsSmoothT A)
    {f : Torus 1 → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : MemH1 (haar 1) f)
    (hf1 : ∫ x, f x ^ 2 ∂haar 1 = 1) {η : ℝ} (hweak : Reg.WeakEL r A f η) :
    ∃ g : Torus 1 → ℝ, g =ᵐ[haar 1] f ∧ IsSmoothT g ∧ (∀ x, 0 < g x) ∧
      ∀ x : Torus 1, -4 * dT (dT g) x + A x * g x - 4 * r * g x * Real.log (g x) = η * g x := by
  have hAc : Continuous A := continuous_of_isSmoothT hA
  obtain ⟨F, hF2, hp, hpos, hode, hsm, hae⟩ := Reg.weakEL_master hr hAc hf0 hf hf1 hweak
  refine ⟨fun y => F (secT y 0), hae, ?_, fun y => hpos _, ?_⟩
  · show ContDiff ℝ ∞ ((fun y : Torus 1 => F (secT y 0)) ∘ liftT)
    rw [Reg.comp_secT_lift hp]
    exact (hsm hA).comp (contDiff_apply ℝ ℝ 0)
  · intro x
    show -4 * dT (dT (fun y => F (secT y 0))) x + A x * F (secT x 0) -
      4 * r * F (secT x 0) * Real.log (F (secT x 0)) = η * F (secT x 0)
    rw [Reg.dT_dT_comp_secT hp x]
    have h := hode (secT x 0)
    have hA' : A x = A (lineT (secT x 0)) := by rw [Reg.lineT_secT]
    rw [hA', h]
    ring

/-- The weak equation tested against `weakGrad φ` instead of `dpart_appA φ 0` (equivalent for smooth
`φ`); same conclusion as `weakEL_regularity_ae`. -/
theorem weakEL_regularity_ae_of_weakGrad {r : ℝ} (hr : 0 ≤ r) {A : Torus 1 → ℝ}
    (hA : Continuous A) {f : Torus 1 → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : MemH1 (haar 1) f)
    (hf1 : ∫ x, f x ^ 2 ∂haar 1 = 1) {η : ℝ}
    (hweak : ∀ φ : Torus 1 → ℝ, IsSmoothT φ →
      ∫ x, (4 * weakGrad f x 0 * weakGrad φ x 0 + A x * f x * φ x -
        4 * r * f x * Real.log (f x) * φ x) ∂haar 1 = η * ∫ x, f x * φ x ∂haar 1) :
    ∃ g : Torus 1 → ℝ, g =ᵐ[haar 1] f ∧ ContDiff ℝ 2 (g ∘ liftT) ∧ (∀ x, 0 < g x) ∧
      ∀ x : Torus 1, -4 * dT (dT g) x + A x * g x - 4 * r * g x * Real.log (g x) = η * g x := by
  refine weakEL_regularity_ae hr hA hf0 hf hf1 (fun φ hφ => ?_)
  have hφw : weakGrad φ =ᵐ[haar 1] fun y _ => dpart_appA φ 0 y :=
    weakGrad_ae_eq (Reg.isWeakGrad_smooth_zero hφ)
  rw [← hweak φ hφ]
  refine integral_congr_ae ?_
  filter_upwards [hφw] with x hx
  rw [congrFun hx 0]

/-- **H8 (a.e. form).** A minimizer `f` of `S_{r,A}` (`r ≥ 0`, `A` continuous) agrees a.e. with a
`C²` strictly positive `g` solving `-4g'' + Ag - 4r g log g = ηg`, `η = S_{r,A}(f)`. -/
theorem sMin_regularity_ae {r : ℝ} (hr : 0 ≤ r) {A : Torus 1 → ℝ} (hA : Continuous A)
    {f : Torus 1 → ℝ} (hf : IsSMin r A f) :
    ∃ g : Torus 1 → ℝ, g =ᵐ[haar 1] f ∧ ContDiff ℝ 2 (g ∘ liftT) ∧ (∀ x, 0 < g x) ∧
      ∀ x : Torus 1, -4 * dT (dT g) x + A x * g x - 4 * r * g x * Real.log (g x) =
        sFunctional r A f * g x := by
  obtain ⟨u, hu, hu0, huH, hu1, hweak⟩ := Reg.sMin_weakEL hA hf
  obtain ⟨g, hg, rest⟩ := weakEL_regularity_ae hr hA hu0 huH hu1 hweak
  exact ⟨g, hg.trans hu, rest⟩

/-- **H8**, exactly the statement of the E01a stub `sMin_regularity`: for smooth `A` the
representative is smooth. -/
theorem sMin_regularity_ae_smooth {r : ℝ} (hr : 0 ≤ r) {A : Torus 1 → ℝ} (hA : IsSmoothT A)
    {f : Torus 1 → ℝ} (hf : IsSMin r A f) :
    ∃ g : Torus 1 → ℝ, g =ᵐ[haar 1] f ∧ IsSmoothT g ∧ (∀ x, 0 < g x) ∧
      ∀ x : Torus 1, -4 * dT (dT g) x + A x * g x - 4 * r * g x * Real.log (g x) =
        sFunctional r A f * g x := by
  obtain ⟨u, hu, hu0, huH, hu1, hweak⟩ := Reg.sMin_weakEL (continuous_of_isSmoothT hA) hf
  obtain ⟨g, hg, rest⟩ := weakEL_regularity_ae_smooth hr hA hu0 huH hu1 hweak
  exact ⟨g, hg.trans hu, rest⟩

/-- **H8, pointwise form** for a continuous minimizer and smooth `A`. -/
theorem sMin_regularity_of_continuous {r : ℝ} (hr : 0 ≤ r) {A : Torus 1 → ℝ} (hA : IsSmoothT A)
    {f : Torus 1 → ℝ} (hf : IsSMin r A f) (hfc : Continuous f) :
    IsSmoothT f ∧ (∀ x, 0 < f x) ∧
      ∀ x : Torus 1, -4 * dT (dT f) x + A x * f x - 4 * r * f x * Real.log (f x) =
        sFunctional r A f * f x := by
  obtain ⟨g, hg, hgs, hgp, hgeq⟩ := sMin_regularity_ae_smooth hr hA hf
  have hgc : Continuous g := continuous_of_isSmoothT hgs
  have : g = f := (hgc.ae_eq_iff_eq (haar 1) hfc).1 hg
  subst this
  exact ⟨hgs, hgp, hgeq⟩

end SharpLSI.FL.Ex
