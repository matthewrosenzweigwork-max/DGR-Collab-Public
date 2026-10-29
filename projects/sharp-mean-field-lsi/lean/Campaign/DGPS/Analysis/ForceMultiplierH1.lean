import DGPS.Analysis.ForceMultiplier
import DGPS.Analysis.ForceMultiplierSmooth
import DGPS.Analysis.PeriodicMollification

/-!
# Full `H¹` force multiplier closure (H1025)

For every real `Q ∈ H¹(𝕋)`, every `ψ ∈ H¹(𝕋^N)` and every `N ≥ 1`, with the weak derivative `Q'`
of `Q` and the weak gradient of `ψ`, the force `B_i(x) = N⁻¹ ∑_{j ≠ i} Q'(x_i - x_j)` satisfies
`ψ B ∈ L²(𝕋^N; ℝ^N)` (Euclidean norm on `ℝ^N`) and, with `L = ‖Q‖_∞`, `β = ‖Q'‖₂`, `u = ‖ψ‖₂`,
`v = ‖∇ψ‖₂`,
`‖ψ B‖₂ ≤ 2 L v + β √(u² + 2 u v / √N) ≤ (2 L + β) v + β u`.

Route: stage 1 (smooth `ψ`) mollifies `Q` (the sup norm does not increase, `Q_h' → Q'` in `L²`),
applies H1024 to `Q_h` and passes to the limit with Fatou along an a.e. convergent subsequence
(the pair maps `x ↦ x_i - x_j` are Haar preserving); stage 2 approximates `ψ` in `H¹` by smooth
functions and again applies Fatou.
-/

open MeasureTheory Filter Topology
open DGPS.Analysis.ForceMultiplier

namespace DGPS.Analysis.ForceMultiplierH1

/-! ### Generic lemmas -/

/-- Fatou for `L²` norms along an a.e. convergent sequence with convergent bounds. -/
theorem eLpNorm_le_of_ae_tendsto_real {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : ℕ → α → E} {g : α → E} {c : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hb : ∀ n, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (c n)) (hc : Tendsto c atTop (𝓝 C)) :
    eLpNorm g 2 μ ≤ ENNReal.ofReal C := by
  calc eLpNorm g 2 μ ≤ atTop.liminf fun n => eLpNorm (f n) 2 μ :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm hf g hg hlim
    _ ≤ atTop.liminf fun n => ENNReal.ofReal (c n) :=
        liminf_le_liminf (Eventually.of_forall hb)
    _ = ENNReal.ofReal C := (ENNReal.tendsto_ofReal hc).liminf_eq

/-- `‖F‖₂ = √(∫ ‖F‖²)` for `F ∈ L²`, in `eLpNorm` form. -/
theorem eLpNorm_two_eq_ofReal_sqrt {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {F : α → E} (hF : MemLp F 2 μ) :
    eLpNorm F 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, ‖F x‖ ^ 2 ∂μ)) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  norm_num

theorem toReal_eLpNorm_two {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {F : α → E} (hF : MemLp F 2 μ) :
    (eLpNorm F 2 μ).toReal = Real.sqrt (∫ x, ‖F x‖ ^ 2 ∂μ) := by
  rw [eLpNorm_two_eq_ofReal_sqrt hF, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]


/-! ### The force field and the bound functions -/

section force

variable {N : ℕ}

/-- The force vector `B(x) = (N⁻¹ ∑_{j ≠ i} Q'(x_i - x_j))_i ∈ ℝ^N` (Euclidean), for a derivative
profile `Qp = Q'` on the circle. -/
noncomputable def forceB (Qp : Torus 1 → ℝ) (x : Torus N) : Tangent N :=
  WithLp.toLp 2 fun i => (N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, Qp (fun _ => x i - x j)

@[simp] theorem forceB_apply (Qp : Torus 1 → ℝ) (x : Torus N) (i : Fin N) :
    forceB Qp x i = (N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, Qp (fun _ => x i - x j) := rfl

theorem continuous_pair (i j : Fin N) :
    Continuous (fun x : Torus N => (fun _ : Fin 1 => x i - x j : Torus 1)) :=
  continuous_pi fun _ => (continuous_apply i).sub (continuous_apply j)

theorem continuous_forceB {Qp : Torus 1 → ℝ} (hQp : Continuous Qp) :
    Continuous (forceB Qp : Torus N → Tangent N) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    continuous_const.mul (continuous_finsetSum _ fun j _ => hQp.comp (continuous_pair i j)))

/-- The first bound `2 L v + β √(u² + 2 u v / √N)`. -/
noncomputable def bound1 (N : ℕ) (L β u v : ℝ) : ℝ :=
  2 * L * v + β * Real.sqrt (u ^ 2 + 2 * (u * v) / Real.sqrt N)

/-- The second bound `(2 L + β) v + β u`. -/
noncomputable def bound2 (L β u v : ℝ) : ℝ := (2 * L + β) * v + β * u

theorem continuous_bound1 (N : ℕ) : Continuous (fun p : ℝ × ℝ × ℝ × ℝ =>
    bound1 N p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold bound1
  fun_prop

theorem bound1_mono {N : ℕ} {L L' β u v : ℝ} (hv : 0 ≤ v) (h : L ≤ L') :
    bound1 N L β u v ≤ bound1 N L' β u v := by
  unfold bound1
  nlinarith

theorem bound1_nonneg {N : ℕ} {L β u v : ℝ} (hL : 0 ≤ L) (hβ : 0 ≤ β) (hv : 0 ≤ v) :
    0 ≤ bound1 N L β u v := by
  unfold bound1
  positivity

theorem bound1_le_bound2 (hN : 1 ≤ N) {L β u v : ℝ} (hβ0 : 0 ≤ β) (hu0 : 0 ≤ u)
    (hv0 : 0 ≤ v) : bound1 N L β u v ≤ bound2 L β u v := by
  have hs1 : 1 ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hsN : 0 < Real.sqrt N := lt_of_lt_of_le one_pos hs1
  have hq : 2 * (u * v) / Real.sqrt N ≤ 2 * (u * v) := by
    rw [div_le_iff₀ hsN]; nlinarith [mul_nonneg hu0 hv0]
  have hroot : Real.sqrt (u ^ 2 + 2 * (u * v) / Real.sqrt N) ≤ u + v := by
    apply Real.sqrt_le_iff.2
    exact ⟨by positivity, by nlinarith [sq_nonneg v]⟩
  unfold bound1 bound2
  nlinarith [mul_le_mul_of_nonneg_left hroot hβ0]

/-- The H1024 bound in `eLpNorm` form for smooth `Q` and smooth `ψ`. -/
theorem smooth_bridge (hN : 1 ≤ N) {Q : Torus 1 → ℝ} (hQ : IsSmoothPeriodic Q) {ψ : Torus N → ℝ}
    (hψ : IsSmoothPeriodic ψ) :
    eLpNorm (fun x => ψ x • forceB (coordPartial 0 Q) x) 2 (haar N) ≤
      ENNReal.ofReal (bound1 N (⨆ t, |Q t|) (Real.sqrt (∫ t, coordPartial 0 Q t ^ 2 ∂haar 1))
        (Real.sqrt (∫ x, ψ x ^ 2 ∂haar N)) (Real.sqrt (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂haar N))) := by
  have hc : Continuous (fun x => ψ x • forceB (coordPartial 0 Q) x) :=
    hψ.continuous_torus.smul (continuous_forceB (hQ.continuous_coordPartial 0))
  have hmem : MemLp (fun x => ψ x • forceB (coordPartial 0 Q) x) 2 (haar N) :=
    hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [eLpNorm_two_eq_ofReal_sqrt hmem]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := (smooth_force_multiplier_bound hN hQ hψ (b := Real.sqrt (∫ x, ∑ i, (ψ x *
    ((N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, pairFun (coordPartial 0 Q) i j x)) ^ 2 ∂haar N))
    (β := Real.sqrt (∫ t, coordPartial 0 Q t ^ 2 ∂haar 1)) (u := Real.sqrt (∫ x, ψ x ^ 2 ∂haar N))
    (v := Real.sqrt (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂haar N)) (L := ⨆ t, |Q t|)
    rfl rfl rfl rfl rfl).1
  have e : ∫ x, ‖ψ x • forceB (coordPartial 0 Q) x‖ ^ 2 ∂haar N = ∫ x, ∑ i, (ψ x *
      ((N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, pairFun (coordPartial 0 Q) i j x)) ^ 2 ∂haar N := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [tangent_norm_sq, PiLp.smul_apply, forceB_apply, smul_eq_mul, pairFun]
  rw [e]
  exact h

end force


/-! ### Mollification does not increase the sup norm -/

section moll

open DGPS.Analysis.PeriodicMollification

theorem abs_mollify_le {h : ℝ} (hh : 0 < h) {g : Torus 1 → ℝ} {M : ℝ}
    (hM : ∀ᵐ x ∂haar 1, |g x| ≤ M) (y : Torus 1) : |mollify h g y| ≤ M := by
  have hM0 : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hM.exists
    exact (abs_nonneg _).trans hx
  rw [mollify_eq_integral_fin1]
  have : (haar 1).IsNegInvariant := Pi.isNegInvariant_volume
  have h1 : ∀ᵐ x ∂haar 1, |g (y - x)| ≤ M :=
    ((haar 1).measurePreserving_sub_left y).quasiMeasurePreserving.ae hM
  have hpsi : Integrable (psi h) :=
    (contDiff_psi hh).continuous.integrable_of_hasCompactSupport (hasCompactSupport_psi hh)
  have hint : ∫ s : Fin 1 → ℝ, psi h s = 1 := by
    have := integral_fin1 (phiH h)
    simpa [psi, integral_phiH hh] using this
  rw [← Real.norm_eq_abs]
  calc ‖∫ s : Fin 1 → ℝ, psi h s * g (y - torusLift s)‖
      ≤ ∫ s : Fin 1 → ℝ, psi h s * M := by
        refine norm_integral_le_of_norm_le (hpsi.mul_const M) ?_
        filter_upwards [SharpLSI.ae_liftT_of_ae h1] with s hs
        have hp0 : 0 ≤ psi h s := phiH_nonneg hh _
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0]
        exact mul_le_mul_of_nonneg_left hs hp0
    _ = M := by rw [integral_mul_const, hint, one_mul]

end moll

/-! ### `L^∞` control of `H¹(𝕋)` -/

section linfty

theorem ae_abs_le_eLpNorm_top {Q : Torus 1 → ℝ} (hQ : MemH1 Q) :
    eLpNorm Q ⊤ (haar 1) ≠ ⊤ ∧ ∀ᵐ x ∂haar 1, |Q x| ≤ (eLpNorm Q ⊤ (haar 1)).toReal := by
  obtain ⟨G, hG⟩ := hQ
  have h1 := (circle_slice_sup_norm.1 Q G hG)
  have hb : ∀ᵐ x ∂haar 1, ‖Q x‖ ≤ Real.sqrt ((Real.sqrt (∫ t, Q t ^ 2 ∂haar 1)) ^ 2 +
      2 * (Real.sqrt (∫ t, Q t ^ 2 ∂haar 1) * Real.sqrt (∫ t, ‖G t‖ ^ 2 ∂haar 1))) := by
    filter_upwards [h1] with x hx
    rw [Real.norm_eq_abs]; exact Real.abs_le_sqrt hx
  have hle := eLpNormEssSup_le_of_ae_bound hb
  have hfin : eLpNorm Q ⊤ (haar 1) ≠ ⊤ := by
    rw [eLpNorm_exponent_top hG.memLp.aestronglyMeasurable]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hfin, ?_⟩
  filter_upwards [enorm_ae_le_eLpNormEssSup Q (haar 1)] with x hx
  rw [eLpNorm_exponent_top hG.memLp.aestronglyMeasurable] at hfin ⊢
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
  simpa [Real.enorm_eq_ofReal_abs] using hx

end linfty

/-! ### Stage 1: smooth `ψ`, general `Q ∈ H¹(𝕋)` -/

section stage1

open DGPS.Analysis.PeriodicMollification

variable {N : ℕ}

theorem tendsto_forceB {P : ℕ → Torus 1 → ℝ} {P0 : Torus 1 → ℝ} {x : Torus N}
    (h : ∀ i j : Fin N, i ≠ j →
      Tendsto (fun k => P k (fun _ => x i - x j)) atTop (𝓝 (P0 (fun _ => x i - x j)))) :
    Tendsto (fun k => forceB (P k) x) atTop (𝓝 (forceB P0 x)) := by
  refine ((PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).tendsto _).comp ?_
  refine tendsto_pi_nhds.2 fun i => ?_
  exact tendsto_const_nhds.mul (tendsto_finsetSum _ fun j hj =>
    h i j (Finset.ne_of_mem_erase hj).symm)

theorem stage1 (hN : 1 ≤ N) {Q : Torus 1 → ℝ} {G : Torus 1 → Tangent 1}
    (hG : IsWeakGradient Q G) {ψ : Torus N → ℝ} (hψ : IsSmoothPeriodic ψ) :
    MemLp (fun x => ψ x • forceB (fun t => G t 0) x) 2 (haar N) ∧
    eLpNorm (fun x => ψ x • forceB (fun t => G t 0) x) 2 (haar N) ≤
      ENNReal.ofReal (bound1 N (eLpNorm Q ⊤ (haar 1)).toReal
        (Real.sqrt (∫ t, ‖G t‖ ^ 2 ∂haar 1)) (Real.sqrt (∫ x, ψ x ^ 2 ∂haar N))
        (Real.sqrt (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂haar N))) := by
  set L := (eLpNorm Q ⊤ (haar 1)).toReal with hL
  set u := Real.sqrt (∫ x, ψ x ^ 2 ∂haar N) with hu
  set v := Real.sqrt (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂haar N) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  obtain ⟨-, hLae⟩ := ae_abs_le_eLpNorm_top ⟨G, hG⟩
  set hs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hs_def
  have hpos : ∀ n, 0 < hs n := fun n => by simp only [hs_def]; positivity
  have hlim : Tendsto hs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hGp := isWeakGradient_iff_isWeakGradientLp.mp hG
  have conv := (strong_sobolev_mollification_including_p_equals_one.2.2.2 hs hpos hlim 2
    one_le_two (by simp) Q G hGp).2
  set P : Torus 1 → ℝ := fun t => G t 0 with hP_def
  set Pn : ℕ → Torus 1 → ℝ := fun n => mollify (hs n) P with hPn_def
  have hQ1 : Integrable Q (haar 1) := hG.memLp.integrable one_le_two
  have hP2 : MemLp P 2 (haar 1) := memLp_coord hG.memLp_grad 0
  have hP1 : Integrable P (haar 1) := hP2.integrable one_le_two
  have hQn : ∀ n, IsSmoothPeriodic (mollify (hs n) Q) := fun n =>
    isSmoothPeriodic_mollify (hpos n) hQ1
  have hPns : ∀ n, IsSmoothPeriodic (Pn n) := fun n => isSmoothPeriodic_mollify (hpos n) hP1
  have hcp : ∀ n, coordPartial 0 (mollify (hs n) Q) = Pn n := fun n =>
    (isWeakGradientLp_mollify (hpos n) one_le_two hGp).1
  have hPn2 : ∀ n, MemLp (Pn n) 2 (haar 1) := fun n => memLp_two_of_smooth (hPns n)
  have hconv : Tendsto (fun n => eLpNorm (Pn n - P) 2 (haar 1)) atTop (𝓝 0) := by
    simpa [hPn_def, hP_def, Pi.sub_def] using conv
  -- convergence of the norms
  have hint := tendsto_integral_sq_of_eLpNorm hPn2 hP2 hconv
  have hβ : Tendsto (fun n => Real.sqrt (∫ t, Pn n t ^ 2 ∂haar 1)) atTop
      (𝓝 (Real.sqrt (∫ t, ‖G t‖ ^ 2 ∂haar 1))) := by
    rw [integral_norm_sq_one]
    exact (Real.continuous_sqrt.tendsto _).comp hint
  -- a.e. convergent subsequence
  have hinm : TendstoInMeasure (haar 1) Pn atTop P :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hconv
  obtain ⟨ns, hns, hae⟩ := hinm.exists_seq_tendsto_ae
  have hpairs : ∀ᵐ x ∂haar N, ∀ i j : Fin N, i ≠ j →
      Tendsto (fun k => Pn (ns k) (fun _ => x i - x j)) atTop (𝓝 (P (fun _ => x i - x j))) := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · filter_upwards [(measurePreserving_pairDiff hij).quasiMeasurePreserving.ae hae] with x hx _
      exact hx
  set F : ℕ → Torus N → Tangent N := fun k x => ψ x • forceB (Pn (ns k)) x with hF_def
  have hFc : ∀ k, Continuous (F k) := fun k =>
    hψ.continuous_torus.smul (continuous_forceB (hPns (ns k)).continuous_torus)
  have hFm : ∀ k, AEStronglyMeasurable (F k) (haar N) := fun k => (hFc k).aestronglyMeasurable
  have hlimF : ∀ᵐ x ∂haar N, Tendsto (fun k => F k x) atTop
      (𝓝 (ψ x • forceB P x)) := by
    filter_upwards [hpairs] with x hx
    exact (tendsto_forceB hx).const_smul (ψ x)
  have hmeasLim : AEStronglyMeasurable (fun x => ψ x • forceB P x) (haar N) :=
    aestronglyMeasurable_of_tendsto_ae atTop hFm hlimF
  have hbd : ∀ k, eLpNorm (F k) 2 (haar N) ≤ ENNReal.ofReal (bound1 N L
      (Real.sqrt (∫ t, Pn (ns k) t ^ 2 ∂haar 1)) u v) := by
    intro k
    have hb := smooth_bridge hN (hQn (ns k)) hψ
    rw [hcp (ns k)] at hb
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    refine bound1_mono hv0 (ciSup_le fun t => ?_)
    exact abs_mollify_le (hpos _) hLae t
  have hc : Tendsto (fun k => bound1 N L (Real.sqrt (∫ t, Pn (ns k) t ^ 2 ∂haar 1)) u v) atTop
      (𝓝 (bound1 N L (Real.sqrt (∫ t, ‖G t‖ ^ 2 ∂haar 1)) u v)) := by
    have h2 := (hβ.comp hns.tendsto_atTop)
    have h3 := (continuous_bound1 N).tendsto (L, Real.sqrt (∫ t, ‖G t‖ ^ 2 ∂haar 1), u, v)
    exact h3.comp (tendsto_const_nhds.prodMk_nhds (h2.prodMk_nhds
      (tendsto_const_nhds.prodMk_nhds tendsto_const_nhds)))
  have hfin := eLpNorm_le_of_ae_tendsto_real hFm hmeasLim hlimF hbd hc
  have hlt : eLpNorm (fun x => ψ x • forceB P x) 2 (haar N) < ⊤ :=
    lt_of_le_of_lt hfin ENNReal.ofReal_lt_top
  exact ⟨hlt, hfin⟩

end stage1

/-! ### Stage 2: general `ψ ∈ H¹(𝕋^N)` -/

section stage2

variable {N : ℕ}

theorem integral_norm_sq_eq_sum {g : Torus N → Tangent N} (hg : MemLp g 2 (haar N)) :
    ∫ x, ‖g x‖ ^ 2 ∂haar N = ∑ j, ∫ x, g x j ^ 2 ∂haar N := by
  simp_rw [tangent_norm_sq]
  exact integral_finsetSum _ fun j _ => (memLp_coord hg j).integrable_sq

theorem stage2 (hN : 1 ≤ N) {Q : Torus 1 → ℝ} {G : Torus 1 → Tangent 1}
    (hG : IsWeakGradient Q G) {ψ : Torus N → ℝ} {g : Torus N → Tangent N}
    (hψ : IsWeakGradient ψ g) :
    MemLp (fun x => ψ x • forceB (fun t => G t 0) x) 2 (haar N) ∧
    eLpNorm (fun x => ψ x • forceB (fun t => G t 0) x) 2 (haar N) ≤
      ENNReal.ofReal (bound1 N (eLpNorm Q ⊤ (haar 1)).toReal
        (Real.sqrt (∫ t, ‖G t‖ ^ 2 ∂haar 1)) (Real.sqrt (∫ x, ψ x ^ 2 ∂haar N))
        (Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂haar N))) := by
  set L := (eLpNorm Q ⊤ (haar 1)).toReal with hL
  set β := Real.sqrt (∫ t, ‖G t‖ ^ 2 ∂haar 1) with hβ
  set B : Torus N → Tangent N := forceB (fun t => G t 0) with hB
  obtain ⟨w, hws, -, hw0, hw1⟩ := exists_smooth_tendsto_H1 hψ
  have hw2 : ∀ k, MemLp (w k) 2 (haar N) := fun k => memLp_two_of_smooth (hws k)
  -- convergence of the norms
  have hu : Tendsto (fun k => Real.sqrt (∫ x, w k x ^ 2 ∂haar N)) atTop
      (𝓝 (Real.sqrt (∫ x, ψ x ^ 2 ∂haar N))) :=
    (Real.continuous_sqrt.tendsto _).comp (tendsto_integral_sq_of_eLpNorm hw2 hψ.memLp hw0)
  have hv : Tendsto (fun k => Real.sqrt (∫ x, ‖smoothGrad (w k) x‖ ^ 2 ∂haar N)) atTop
      (𝓝 (Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂haar N))) := by
    have hsm : ∀ k, MemLp (smoothGrad (w k)) 2 (haar N) := fun k =>
      ((hws k).isWeakGradient).memLp_grad
    have e1 : ∀ k, ∫ x, ‖smoothGrad (w k) x‖ ^ 2 ∂haar N =
        ∑ j, ∫ x, smoothGrad (w k) x j ^ 2 ∂haar N := fun k => integral_norm_sq_eq_sum (hsm k)
    simp_rw [e1, integral_norm_sq_eq_sum hψ.memLp_grad]
    refine (Real.continuous_sqrt.tendsto _).comp (tendsto_finsetSum _ fun j _ => ?_)
    exact tendsto_integral_sq_of_eLpNorm (fun k => memLp_coord (hsm k) j)
      (memLp_coord hψ.memLp_grad j) (hw1 j)
  -- a.e. convergent subsequence
  have hinm : TendstoInMeasure (haar N) w atTop ψ :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hw0
  obtain ⟨ns, hns, hae⟩ := hinm.exists_seq_tendsto_ae
  set F : ℕ → Torus N → Tangent N := fun k x => w (ns k) x • B x with hF_def
  have hst := fun k => stage1 hN hG (hws (ns k))
  have hFm : ∀ k, AEStronglyMeasurable (F k) (haar N) := fun k => (hst k).1.aestronglyMeasurable
  have hlimF : ∀ᵐ x ∂haar N, Tendsto (fun k => F k x) atTop (𝓝 (ψ x • B x)) := by
    filter_upwards [hae] with x hx
    exact hx.smul_const (B x)
  have hmeasLim : AEStronglyMeasurable (fun x => ψ x • B x) (haar N) :=
    aestronglyMeasurable_of_tendsto_ae atTop hFm hlimF
  have hc : Tendsto (fun k => bound1 N L β (Real.sqrt (∫ x, w (ns k) x ^ 2 ∂haar N))
      (Real.sqrt (∫ x, ‖smoothGrad (w (ns k)) x‖ ^ 2 ∂haar N))) atTop
      (𝓝 (bound1 N L β (Real.sqrt (∫ x, ψ x ^ 2 ∂haar N))
        (Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂haar N)))) := by
    have h3 := (continuous_bound1 N).tendsto (L, β, Real.sqrt (∫ x, ψ x ^ 2 ∂haar N),
      Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂haar N))
    exact h3.comp (tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds
      ((hu.comp hns.tendsto_atTop).prodMk_nhds (hv.comp hns.tendsto_atTop))))
  have hfin := eLpNorm_le_of_ae_tendsto_real hFm hmeasLim hlimF (fun k => (hst k).2) hc
  have hlt : eLpNorm (fun x => ψ x • B x) 2 (haar N) < ⊤ :=
    lt_of_le_of_lt hfin ENNReal.ofReal_lt_top
  exact ⟨hlt, hfin⟩

end stage2

/-! ### The full `H¹` force multiplier closure -/

/-- **H1025.** Full `H¹` force multiplier closure.  For every `N ≥ 1`, every real `Q ∈ H¹(𝕋)`
and every real `ψ ∈ H¹(𝕋^N)`, with the weak derivative `Q' = (weakGradient Q hQ) · 0` and the
weak gradient of `ψ`, the force `B_i(x) = N⁻¹ ∑_{j ≠ i} Q'(x_i - x_j)` (`forceB`) makes `ψ B` a
well-defined element of `L²(𝕋^N; ℝ^N)` (Euclidean norm), and, with `L = ‖Q‖_∞`, `β = ‖Q'‖₂`,
`u = ‖ψ‖₂`, `v = ‖∇ψ‖₂`,
`‖ψ B‖₂ ≤ 2 L v + β √(u² + 2 u v / √N) ≤ (2 L + β) v + β u`,
with constants independent of `N`. -/
theorem full_h1_force_multiplier_closure (N : ℕ) (hN : 1 ≤ N) (Q : Torus 1 → ℝ) (hQ : MemH1 Q)
    (ψ : Torus N → ℝ) (hψ : MemH1 ψ) {L β u v : ℝ}
    (hL : L = (eLpNorm Q ⊤ (haar 1)).toReal)
    (hβ : β = Real.sqrt (∫ t, ‖weakGradient Q hQ t‖ ^ 2 ∂haar 1))
    (hu : u = Real.sqrt (∫ x, ψ x ^ 2 ∂haar N))
    (hv : v = Real.sqrt (∫ x, ‖weakGradient ψ hψ x‖ ^ 2 ∂haar N)) :
    MemLp (fun x => ψ x • forceB (fun t => weakGradient Q hQ t 0) x) 2 (haar N) ∧
    (eLpNorm (fun x => ψ x • forceB (fun t => weakGradient Q hQ t 0) x) 2 (haar N)).toReal ≤
      2 * L * v + β * Real.sqrt (u ^ 2 + 2 * (u * v) / Real.sqrt N) ∧
    2 * L * v + β * Real.sqrt (u ^ 2 + 2 * (u * v) / Real.sqrt N) ≤ (2 * L + β) * v + β * u := by
  have hL0 : 0 ≤ L := hL ▸ ENNReal.toReal_nonneg
  have hβ0 : 0 ≤ β := hβ ▸ Real.sqrt_nonneg _
  have hu0 : 0 ≤ u := hu ▸ Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := hv ▸ Real.sqrt_nonneg _
  obtain ⟨hmem, hle⟩ := stage2 hN (isWeakGradient_weakGradient hQ) (isWeakGradient_weakGradient hψ)
  rw [← hL, ← hβ, ← hu, ← hv] at hle
  refine ⟨hmem, ?_, bound1_le_bound2 hN hβ0 hu0 hv0⟩
  exact ENNReal.toReal_le_of_le_ofReal (bound1_nonneg hL0 hβ0 hv0) hle

end DGPS.Analysis.ForceMultiplierH1
