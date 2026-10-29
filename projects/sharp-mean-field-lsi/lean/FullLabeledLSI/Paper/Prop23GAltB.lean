import FullLabeledLSI.Paper.Prop23GAltA
import FullLabeledLSI.Infra.SpectralMain
import FullLabeledLSI.Statements.S24_Lemma_6_2

/-!
# Proposition 2.3, WP-G (alt): the `J`-cut `(eq:J-cut)`

For `Ψ_N` bounded in `H¹ ∩ L^{2p}` (`ℰ⁰(Ψ) ≤ M₁`, `∫|Ψ|^{2p} ≤ M₂`) and fixed `R`: for every `ε > 0`
there is `t > 0` and `L₀` such that for all `L ≥ L₀` and all `N ≥ 1`
`𝒥_{N,R}(Π_L S_t Ψ) - ε ≤ 𝒥_{N,R}(Ψ)`.
Together with the statement that `Π_L S_t Ψ` lies in the spectral range with `L²` norm `≤ M₂^{1/(2p)}`.
The order of quantifiers is `∃ t, ∃ L₀, ∀ L ≥ L₀` (`eq:error-order`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-! ### `L^q` from the `2p`-moment -/

theorem ga_memLp_of_lintegral {α : Type*} [MeasurableSpace α] {ν : Measure α} {Ψ : α → ℝ}
    {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M) (hΨ : AEStronglyMeasurable Ψ ν)
    (h : ∫⁻ x, ENNReal.ofReal (|Ψ x| ^ q) ∂ν ≤ ENNReal.ofReal M) :
    MemLp Ψ (ENNReal.ofReal q) ν ∧ eLpNorm Ψ (ENNReal.ofReal q) ν ≤ ENNReal.ofReal (M ^ (1 / q)) := by
  have hpt : ∀ x, ‖Ψ x‖ₑ ^ q = ENNReal.ofReal (|Ψ x| ^ q) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq.le]
  have hnorm : eLpNorm Ψ (ENNReal.ofReal q) ν ≤ ENNReal.ofReal (M ^ (1 / q)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top hΨ,
      ENNReal.toReal_ofReal hq.le]
    simp_rw [hpt]
    rw [← ENNReal.ofReal_rpow_of_nonneg hM (by positivity)]
    exact ENNReal.rpow_le_rpow h (by positivity)
  have hlt : eLpNorm Ψ (ENNReal.ofReal q) ν < ⊤ := hnorm.trans_lt ENNReal.ofReal_lt_top
  exact ⟨hlt, hnorm⟩

/-! ### Integrability and splitting for squares against `L^s` weights -/

theorem ga_integrable_sq_mul {α : Type*} [MeasurableSpace α] {ν : Measure α} {Ψ g : α → ℝ}
    {q : ℝ} (hq : 2 < q) (hΨ : MemLp Ψ (ENNReal.ofReal q) ν)
    (hg : MemLp g (ENNReal.ofReal ((q / 2) / (q / 2 - 1))) ν) :
    Integrable (fun x => Ψ x ^ 2 * g x) ν := by
  have hp : 1 < q / 2 := by linarith
  have hq0 : 0 < q := by linarith
  have hpt : ∀ x, ENNReal.ofReal (|Ψ x| ^ (2 * (q / 2))) = ‖Ψ x‖ₑ ^ q := fun x => by
    rw [show 2 * (q / 2) = q by ring, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
  have hlin : ∫⁻ x, ENNReal.ofReal (|Ψ x| ^ (2 * (q / 2))) ∂ν < ⊤ := by
    have h1 := hΨ.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top
      hΨ.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le] at h1
    have h2 := (ENNReal.rpow_lt_top_iff_of_pos (by positivity : 0 < 1 / q)).1 h1
    simp_rw [hpt]
    exact h2
  have hH := holder_sq_mul ν hp hΨ.aemeasurable hg.aemeasurable
  have hfin : ∫⁻ x, ENNReal.ofReal (Ψ x ^ 2 * |g x|) ∂ν < ⊤ := by
    refine lt_of_le_of_lt hH (ENNReal.mul_lt_top ?_ hg.eLpNorm_lt_top)
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hlin.ne
  refine ⟨(hΨ.aestronglyMeasurable.pow 2).mul hg.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ x, ‖Ψ x ^ 2 * g x‖ₑ = ENNReal.ofReal (Ψ x ^ 2 * |g x|) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  simp_rw [this]
  exact hfin

theorem ga_split {α : Type*} [MeasurableSpace α] {ν : Measure α} {X Y W : α → ℝ} {q : ℝ}
    (hq : 2 < q) (hX : MemLp X (ENNReal.ofReal q) ν) (hY : MemLp Y (ENNReal.ofReal q) ν)
    (hW : ∀ s : ℝ≥0∞, 1 ≤ s → s ≠ ⊤ → MemLp W s ν) :
    ∫ x, (X x ^ 2 - Y x ^ 2) * W x ∂ν = ∫ x, X x ^ 2 * W x ∂ν - ∫ x, Y x ^ 2 * W x ∂ν := by
  have hp1 : 0 < q / 2 - 1 := by linarith
  have hW' : MemLp W (ENNReal.ofReal ((q / 2) / (q / 2 - 1))) ν :=
    hW _ (ENNReal.one_le_ofReal.2 ((one_le_div hp1).2 (by linarith))) ENNReal.ofReal_ne_top
  have i1 := ga_integrable_sq_mul hq hX hW'
  have i2 := ga_integrable_sq_mul hq hY hW'
  simp_rw [sub_mul]
  exact integral_sub i1 i2

/-! ### Real bookkeeping -/

theorem ga_alg {EΨ EF vΨ vt vF eΨ et eF uΨ ut uF nΨ nt nF cc lg e' : ℝ} (hE : EF ≤ EΨ)
    (hv1 : |vΨ - vt| ≤ e') (hv2 : |vt - vF| ≤ e')
    (he1 : |eΨ - et| ≤ e') (he2 : |et - eF| ≤ e')
    (hu1 : |uΨ - ut| ≤ e') (hu2 : |ut - uF| ≤ e')
    (hn1 : |nΨ - nt| ≤ e') (hn2 : |nt - nF| ≤ e') (hcc : 0 ≤ cc) :
    (EF + vF - cc * (eF + uF + lg * nF)) - 2 * e' * (1 + 2 * cc + cc * |lg|) ≤
      EΨ + vΨ - cc * (eΨ + uΨ + lg * nΨ) := by
  have he0 : 0 ≤ e' := (abs_nonneg _).trans hv1
  have a1 : -(2 * e') ≤ vΨ - vF := by
    linarith [(abs_le.1 hv1).1, (abs_le.1 hv2).1]
  have a2 : -(2 * e') ≤ eF - eΨ := by
    linarith [(abs_le.1 he1).2, (abs_le.1 he2).2]
  have a3 : -(2 * e') ≤ uF - uΨ := by
    linarith [(abs_le.1 hu1).2, (abs_le.1 hu2).2]
  have a4 : |nF - nΨ| ≤ 2 * e' := by
    rw [abs_le]; constructor <;> linarith [(abs_le.1 hn1).1, (abs_le.1 hn1).2, (abs_le.1 hn2).1,
      (abs_le.1 hn2).2]
  have a5 : -(|lg| * (2 * e')) ≤ lg * (nF - nΨ) := by
    have : |lg * (nF - nΨ)| ≤ |lg| * (2 * e') := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left a4 (abs_nonneg _)
    linarith [(abs_le.1 this).1]
  have b : cc * (-(2 * e') + -(2 * e') + -(|lg| * (2 * e'))) ≤
      cc * ((eF - eΨ) + (uF - uΨ) + lg * (nF - nΨ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hcc
  nlinarith [b, a1, hE]

theorem ga_two_lt {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (2 : ℝ≥0∞) < ENNReal.ofReal (1 + Real.exp (a * t)) := by
  have h1 : 1 < Real.exp (a * t) := by have := Real.add_one_lt_exp (ne_of_gt (mul_pos ha ht)); have := mul_pos ha ht; linarith
  have : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [this]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)

/-- Unfolding of `Jexpr` (definitional). -/
theorem Jexpr_unfold {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
    (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (CR : ℕ → ℕ → ℝ) (R : ℕ) {N : ℕ}
    (Ψ : Config N d → ℝ) :
    Jexpr A lam CR R Ψ =
      (refEnergy μ Ψ).toReal +
        ∫ X, Ψ X ^ 2 * vR A lam R (fun n => fluct e N n X) ∂QN μ N -
        (bRate μ lam CR).toReal / 2 *
          ((ent (QN μ N) (fun X => Ψ X ^ 2)).toReal +
            ∫ X, Ψ X ^ 2 * URN A R N X ∂QN μ N +
            Real.log (kappaR A R) * ∫ X, Ψ X ^ 2 ∂QN μ N) := rfl

/-! ### The `J`-cut -/

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **WP-G, `(eq:J-cut)`.** -/
theorem J_cut_alt (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (CR : ℕ → ℕ → ℕ → ℝ) (R : ℕ)
    {p : ℝ} (hp : 1 < p) {M1 M2 : ℝ} (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧ ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ N : ℕ, 1 ≤ N →
      ∀ Ψ : Config N d → ℝ, MemH1C (QN (μ : Measure (Torus d)) N) Ψ →
        refEnergy (μ : Measure (Torus d)) Ψ ≤ ENNReal.ofReal M1 →
        ∫⁻ X, ENNReal.ofReal (|Ψ X| ^ (2 * p)) ∂QN (μ : Measure (Torus d)) N ≤
          ENNReal.ofReal M2 →
        InSpectralRange e lam L (Spectral.Fcut (μ : Measure (Torus d)) e lam t L Ψ) ∧
        eLpNorm (Spectral.Fcut (μ : Measure (Torus d)) e lam t L Ψ) 2 (QN (μ : Measure (Torus d)) N) ≤
          ENNReal.ofReal (M2 ^ (1 / (2 * p))) ∧
        Jexpr A lam (CR R) R (Spectral.Fcut (μ : Measure (Torus d)) e lam t L Ψ) - ε ≤
          Jexpr A lam (CR R) R Ψ := by
  intro ε hε
  have hac := minimizer_ac hyp hμ
  obtain ⟨eC', a, Cu, Cl, c, ha, hrls, hup, hlow, hC1, hae, hlam0, hc, hweyl, hpkg⟩ :=
    Spectral.cut_package_main hd hyp hr μ hμ e lam he
  set s : ℝ := 2 * p with hs
  have hs2 : 2 ≤ s := by rw [hs]; linarith
  have hs0 : 0 < s := by linarith
  set Bs : ℝ := M2 ^ (1 / s) with hBs
  have hBs0 : 0 ≤ Bs := Real.rpow_nonneg hM2 _
  -- weights and their uniform bounds
  have hUBv := UB_vR hyp hμ he hφ heC A R (lam := lam)
  have hUBu := UB_uR hyp hμ he hφ heC A R
  have hBw : ∀ {g : (N : ℕ) → Config N d → ℝ}, UB (μ : Measure (Torus d)) g →
      ∃ Bw : ℝ≥0∞ → ℝ, ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ → ∀ N : ℕ, 1 ≤ N →
        MemLp (g N) q (QN (μ : Measure (Torus d)) N) ∧
          eLpNorm (g N) q (QN (μ : Measure (Torus d)) N) ≤ ENNReal.ofReal (Bw q) := by
    intro g hg
    have : ∀ q : ℝ≥0∞, ∃ K : ℝ, 1 ≤ q → q ≠ ⊤ → ∀ N : ℕ, 1 ≤ N →
        MemLp (g N) q (QN (μ : Measure (Torus d)) N) ∧
          eLpNorm (g N) q (QN (μ : Measure (Torus d)) N) ≤ ENNReal.ofReal K := by
      intro q
      by_cases h : 1 ≤ q ∧ q ≠ ⊤
      · obtain ⟨K, -, hK⟩ := hg q h.1 h.2
        exact ⟨K, fun _ _ => hK⟩
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
    choose Bw hBw using this
    exact ⟨Bw, fun q h1 h2 => hBw q h1 h2⟩
  obtain ⟨Bv, hBv⟩ := hBw hUBv
  obtain ⟨Bu, hBu⟩ := hBw hUBu
  -- constants
  set cc : ℝ := (bRate (μ : Measure (Torus d)) lam (CR R)).toReal / 2 with hcc
  have hcc0 : 0 ≤ cc := by rw [hcc]; positivity
  set lg : ℝ := Real.log (kappaR A R) with hlg
  have hden : 0 < 2 * (1 + 2 * cc + cc * |lg|) := by positivity
  set e' : ℝ := ε / (2 * (1 + 2 * cc + cc * |lg|)) with he'
  have he'0 : 0 < e' := by rw [he']; positivity
  have hfin : e' * 2 * (1 + 2 * cc + cc * |lg|) = ε := by rw [he']; field_simp
  -- step 1 moduli
  have hq1 : (2 : ℝ≥0∞) < ENNReal.ofReal s := by
    have : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [this]
    exact (ENNReal.ofReal_lt_ofReal_iff hs0).2 (by rw [hs]; linarith)
  obtain ⟨δe1, hδe1, hE1⟩ := entropy_continuity (ENNReal.ofReal s) hq1 ENNReal.ofReal_ne_top
    Bs e' he'0
  obtain ⟨δv1, hδv1, hV1⟩ := weighted_continuity (ENNReal.ofReal s) hq1 ENNReal.ofReal_ne_top
    Bs Bv e' he'0
  obtain ⟨δu1, hδu1, hU1⟩ := weighted_continuity (ENNReal.ofReal s) hq1 ENNReal.ofReal_ne_top
    Bs Bu e' he'0
  set δ1 : ℝ := min δe1 (min δv1 δu1) with hδ1
  have hδ10 : 0 < δ1 := lt_min hδe1 (lt_min hδv1 hδu1)
  set t : ℝ := min 1 (δ1 ^ 2 / (M1 + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have htM : Real.sqrt (t * M1) ≤ δ1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨hδ10.le, ?_⟩
    have h1 : t ≤ δ1 ^ 2 / (M1 + 1) := min_le_right _ _
    calc t * M1 ≤ δ1 ^ 2 / (M1 + 1) * M1 := mul_le_mul_of_nonneg_right h1 hM1
      _ ≤ δ1 ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg δ1]
  -- step 2 moduli
  have hq2 := ga_two_lt ha ht0
  obtain ⟨δe2, hδe2, hE2⟩ := entropy_continuity (ENNReal.ofReal (1 + Real.exp (a * t))) hq2
    ENNReal.ofReal_ne_top Bs e' he'0
  obtain ⟨δv2, hδv2, hV2⟩ := weighted_continuity (ENNReal.ofReal (1 + Real.exp (a * t))) hq2
    ENNReal.ofReal_ne_top Bs Bv e' he'0
  obtain ⟨δu2, hδu2, hU2⟩ := weighted_continuity (ENNReal.ofReal (1 + Real.exp (a * t))) hq2
    ENNReal.ofReal_ne_top Bs Bu e' he'0
  set δ2 : ℝ := min δe2 (min δv2 δu2) with hδ2
  have hδ20 : 0 < δ2 := lt_min hδe2 (lt_min hδv2 hδu2)
  refine ⟨t, ht0, -Real.log (δ2 / (Bs + 1)) / t, fun L hL N hN Ψ hΨH hE hΨp => ?_⟩
  -- the cut package
  have hΨ2 : MemLp Ψ 2 (QN (μ : Measure (Torus d)) N) :=
    (memLp_map_measure_iff hΨH.2.1.aestronglyMeasurable measurable_flat.aemeasurable).1 hΨH.2.1
  obtain ⟨hΨs, hΨsn⟩ := ga_memLp_of_lintegral hs0 hM2 hΨ2.aestronglyMeasurable hΨp
  have hP := hpkg N L Ψ hs2 ht0 hΨH hΨs hΨsn
  have hq2r : (2 : ℝ) < 1 + Real.exp (a * t) := by
    have h1 : 1 < Real.exp (a * t) := by
      have := Real.add_one_lt_exp (ne_of_gt (mul_pos ha ht0)); have := mul_pos ha ht0; linarith
    linarith
  have hs2' : (2 : ℝ) < s := by rw [hs]; linarith
  have hF2 : eLpNorm (Spectral.Fcut (μ : Measure (Torus d)) e lam t L Ψ) 2
      (QN (μ : Measure (Torus d)) N) ≤ ENNReal.ofReal (M2 ^ (1 / (2 * p))) :=
    (eLpNorm_le_eLpNorm_of_exponent_le hq2.le).trans hP.eLpNorm_F_q_le_B
  refine ⟨hP.inRange, hF2, ?_⟩
  set Ψt := Spectral.Sfun he t Ψ with hΨt
  set F := Spectral.Fcut (μ : Measure (Torus d)) e lam t L Ψ with hF
  -- distances
  have hd1 : eLpNorm (Ψ - Ψt) 2 (QN (μ : Measure (Torus d)) N) ≤ ENNReal.ofReal δ1 := by
    refine hP.eLpNorm_sub_le.trans (ENNReal.ofReal_le_ofReal ?_)
    refine le_trans (Real.sqrt_le_sqrt ?_) htM
    have : (refEnergy (μ : Measure (Torus d)) Ψ).toReal ≤ M1 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
      rwa [ENNReal.toReal_ofReal hM1] at this
    exact mul_le_mul_of_nonneg_left this ht0.le
  have hd2 : eLpNorm (Ψt - F) 2 (QN (μ : Measure (Torus d)) N) ≤ ENNReal.ofReal δ2 := by
    refine hP.eLpNorm_cut_le_B.trans (ENNReal.ofReal_le_ofReal ?_)
    have hL' : -Real.log (δ2 / (Bs + 1)) ≤ t * L := by
      have := (div_le_iff₀ ht0).1 hL
      linarith
    have hex : Real.exp (-(t * L)) ≤ δ2 / (Bs + 1) := by
      calc Real.exp (-(t * L)) ≤ Real.exp (Real.log (δ2 / (Bs + 1))) :=
            Real.exp_le_exp.2 (by linarith)
        _ = δ2 / (Bs + 1) := Real.exp_log (by positivity)
    calc Real.exp (-(t * L)) * Bs ≤ δ2 / (Bs + 1) * Bs :=
          mul_le_mul_of_nonneg_right hex hBs0
      _ ≤ δ2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  have wv : ∀ s' : ℝ≥0∞, 1 ≤ s' → s' ≠ ⊤ →
      MemLp (fun X : Config N d => vR A lam R (fun n => fluct e N n X)) s'
        (QN (μ : Measure (Torus d)) N) ∧
      eLpNorm (fun X : Config N d => vR A lam R (fun n => fluct e N n X)) s'
        (QN (μ : Measure (Torus d)) N) ≤ ENNReal.ofReal (Bv s') :=
    fun s' h1 h2 => hBv s' h1 h2 N hN
  have wu : ∀ s' : ℝ≥0∞, 1 ≤ s' → s' ≠ ⊤ →
      MemLp (fun X : Config N d => uR A R (fun n => fluct e N n X)) s'
        (QN (μ : Measure (Torus d)) N) ∧
      eLpNorm (fun X : Config N d => uR A R (fun n => fluct e N n X)) s'
        (QN (μ : Measure (Torus d)) N) ≤ ENNReal.ofReal (Bu s') :=
    fun s' h1 h2 => hBu s' h1 h2 N hN
  have wv1 : ∀ s' : ℝ≥0∞, 1 ≤ s' → s' ≠ ⊤ → MemLp
      (fun X : Config N d => vR A lam R (fun n => fluct e N n X)) s' (QN (μ : Measure (Torus d)) N) :=
    fun s' h1 h2 => (wv s' h1 h2).1
  have wu1 : ∀ s' : ℝ≥0∞, 1 ≤ s' → s' ≠ ⊤ → MemLp
      (fun X : Config N d => uR A R (fun n => fluct e N n X)) s' (QN (μ : Measure (Torus d)) N) :=
    fun s' h1 h2 => (wu s' h1 h2).1
  have m1 : δ1 ≤ δe1 := min_le_left _ _
  have m2 : δ1 ≤ δv1 := (min_le_right _ _).trans (min_le_left _ _)
  have m3 : δ1 ≤ δu1 := (min_le_right _ _).trans (min_le_right _ _)
  have n1 : δ2 ≤ δe2 := min_le_left _ _
  have n2 : δ2 ≤ δv2 := (min_le_right _ _).trans (min_le_left _ _)
  have n3 : δ2 ≤ δu2 := (min_le_right _ _).trans (min_le_right _ _)
  -- pair (Ψ, Ψt)
  obtain ⟨hent1, hnorm1⟩ := hE1 _ (QN (μ : Measure (Torus d)) N) Ψ Ψt hΨs hP.memLp_Ψt_s hΨsn
    hP.eLpNorm_Ψt_s_le (hd1.trans (ENNReal.ofReal_le_ofReal m1))
  have hv1 := hV1 _ (QN (μ : Measure (Torus d)) N) Ψ Ψt _ hΨs hP.memLp_Ψt_s hΨsn
    hP.eLpNorm_Ψt_s_le wv (hd1.trans (ENNReal.ofReal_le_ofReal m2))
  have hu1 := hU1 _ (QN (μ : Measure (Torus d)) N) Ψ Ψt _ hΨs hP.memLp_Ψt_s hΨsn
    hP.eLpNorm_Ψt_s_le wu (hd1.trans (ENNReal.ofReal_le_ofReal m3))
  -- pair (Ψt, F)
  obtain ⟨hent2, hnorm2⟩ := hE2 _ (QN (μ : Measure (Torus d)) N) Ψt F hP.memLp_Ψt_q hP.memLp_F_q
    hP.eLpNorm_Ψt_q_le_B hP.eLpNorm_F_q_le_B (hd2.trans (ENNReal.ofReal_le_ofReal n1))
  have hv2 := hV2 _ (QN (μ : Measure (Torus d)) N) Ψt F _ hP.memLp_Ψt_q hP.memLp_F_q
    hP.eLpNorm_Ψt_q_le_B hP.eLpNorm_F_q_le_B wv (hd2.trans (ENNReal.ofReal_le_ofReal n2))
  have hu2 := hU2 _ (QN (μ : Measure (Torus d)) N) Ψt F _ hP.memLp_Ψt_q hP.memLp_F_q
    hP.eLpNorm_Ψt_q_le_B hP.eLpNorm_F_q_le_B wu (hd2.trans (ENNReal.ofReal_le_ofReal n3))
  rw [ga_split (ν := QN (μ : Measure (Torus d)) N) hs2' hΨs hP.memLp_Ψt_s wv1] at hv1
  rw [ga_split (ν := QN (μ : Measure (Torus d)) N) hs2' hΨs hP.memLp_Ψt_s wu1] at hu1
  rw [ga_split (ν := QN (μ : Measure (Torus d)) N) hq2r hP.memLp_Ψt_q hP.memLp_F_q wv1] at hv2
  rw [ga_split (ν := QN (μ : Measure (Torus d)) N) hq2r hP.memLp_Ψt_q hP.memLp_F_q wu1] at hu2
  have hEle : (refEnergy (μ : Measure (Torus d)) F).toReal ≤
      (refEnergy (μ : Measure (Torus d)) Ψ).toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE) hP.refEnergy_le
  have key := ga_alg (EΨ := (refEnergy (μ : Measure (Torus d)) Ψ).toReal)
    (EF := (refEnergy (μ : Measure (Torus d)) F).toReal)
    (vΨ := ∫ X, Ψ X ^ 2 * vR A lam R (fun n => fluct e N n X) ∂QN (μ : Measure (Torus d)) N)
    (vt := ∫ X, Ψt X ^ 2 * vR A lam R (fun n => fluct e N n X) ∂QN (μ : Measure (Torus d)) N)
    (vF := ∫ X, F X ^ 2 * vR A lam R (fun n => fluct e N n X) ∂QN (μ : Measure (Torus d)) N)
    (eΨ := (ent (QN (μ : Measure (Torus d)) N) (fun X => Ψ X ^ 2)).toReal)
    (et := (ent (QN (μ : Measure (Torus d)) N) (fun X => Ψt X ^ 2)).toReal)
    (eF := (ent (QN (μ : Measure (Torus d)) N) (fun X => F X ^ 2)).toReal)
    (uΨ := ∫ X, Ψ X ^ 2 * URN A R N X ∂QN (μ : Measure (Torus d)) N)
    (ut := ∫ X, Ψt X ^ 2 * URN A R N X ∂QN (μ : Measure (Torus d)) N)
    (uF := ∫ X, F X ^ 2 * URN A R N X ∂QN (μ : Measure (Torus d)) N)
    (nΨ := ∫ X, Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N)
    (nt := ∫ X, Ψt X ^ 2 ∂QN (μ : Measure (Torus d)) N)
    (nF := ∫ X, F X ^ 2 ∂QN (μ : Measure (Torus d)) N)
    (cc := cc) (lg := lg) (e' := e') hEle hv1 hv2 hent1 hent2 hu1 hu2 hnorm1 hnorm2 hcc0
  rw [Jexpr_unfold, Jexpr_unfold, ← hcc, ← hlg]
  have : 2 * e' * (1 + 2 * cc + cc * |lg|) = ε := by rw [← hfin]; ring
  linarith

end SharpLSI.FL
