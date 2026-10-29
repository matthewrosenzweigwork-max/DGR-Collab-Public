import SharpSymmetricLSI.Paper.GroundT17
import SharpSymmetricLSI.Paper.TestEnergy4
import SharpSymmetricLSI.Paper.LipChain3
import SharpSymmetricLSI.Paper.Prop23Defs
import SharpSymmetricLSI.Statements.R02_Prop_2_1
import SharpSymmetricLSI.Statements.R03_Prop_2_2
import SharpSymmetricLSI.Statements.R19_Lemma_5_2
import SharpSymmetricLSI.Statements.R20_Lemma_5_3

/-!
# (8.20), (2.5)–(2.7) (lane s42): `CompactnessProperty'` from the core lower bound

`form_liminf_of_core`: given the core lower bound `hcore` (the form lower bound along sequences
converging jointly in law with the fluctuations, with uniformly integrable squares), the
compactness statement of Proposition 2.3 holds with `γ_∞ = γ` and `ℰ_∞ = gaussForm`:
* the extraction, the law, uniform integrability, mean and second moment come from Section 7.2
  (`gibbs_compactness_of`, with the inputs of R02, R03, R19, R20, assembled as in R30), with
  `gammaInfOf W μ Q = γ` (`eq_of_isCenteredGaussianCov`);
* (2.7) for `f` is `hcore` along the extraction;
* (2.7) for `χ ∘ f`, `χ` Lipschitz: for `b` above the `liminf`, a further extraction with
  energies `< b`; `χ ∘ f ∈ H¹` with `ℰ(χ ∘ f) ≤ L² ℰ(f)` (`memH1C_comp_lipschitz`), the `L²` bound
  and uniform integrability from `(χ t)² ≤ 2χ(0)² + 2L²t²`, and the joint law of
  `(χ ∘ f, Z)` from that of `(f, Z)`; then `hcore`.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace SharpLSI

variable {d : ℕ}

theorem sq_lipschitz_le {χ : ℝ → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ) (t : ℝ) :
    χ t ^ 2 ≤ 2 * χ 0 ^ 2 + 2 * (L : ℝ) ^ 2 * t ^ 2 := by
  have h := hχ.dist_le_mul t 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at h
  have h1 : |χ t| ≤ |χ 0| + L * |t| := by
    have := abs_sub_abs_le_abs_sub (χ t) (χ 0); linarith
  have h2 : χ t ^ 2 ≤ (|χ 0| + L * |t|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith [sq_nonneg (|χ 0| - L * |t|), sq_abs (χ 0), sq_abs t]

section
variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
  (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
  {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
  {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
include hd hyp hr hμ he hC hγ

set_option maxHeartbeats 1600000 in
/-- **`CompactnessProperty'` from the core lower bound.** -/
theorem form_liminf_of_core
    (hcore : ∀ (Ns : ℕ → ℕ), Tendsto Ns atTop atTop → ∀ (f : (k : ℕ) → Config (Ns k) d → ℝ),
      (∀ k, MemH1C (gibbs V W (Ns k)) (f k)) →
      (∃ B : NNReal, ∀ k, (∫⁻ X, ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k)) +
        energy V W (Ns k) (f k) ≤ B) →
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k, ∫⁻ X in {X | M < f k X ^ 2},
        ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k) ≤ ENNReal.ofReal ε) →
      ∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ →
      (∀ (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ), Tendsto (fun k => ∫ X, g (f k X,
        fun n => fluct e (Ns k) n X) ∂gibbs V W (Ns k)) atTop
          (𝓝 (∫ z, g (F z, fun n => z n) ∂γ))) →
      gaussForm (lamShift lam) γ F ≤ liminf (fun k => energy V W (Ns k) (f k)) atTop) :
    CompactnessProperty' V W γ (gaussForm (lamShift lam) γ) := by
  intro Ns hNs f hf hB
  haveI := hγ.1
  -- Section 7.2 (as in R30)
  obtain ⟨a₀, CF, -, hF⟩ := force_exponential hd hyp hr hμ
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hr
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr1
  obtain ⟨B0, hB0⟩ := prop_defective hd hyp hr r hrpos hr2
  obtain ⟨Cp, p, hp, hCp⟩ := reference_entropy hd hyp hr hμ
  obtain ⟨Q, hQ⟩ := exists_secondChaos_Tmat hyp hμ he
  have h21 := prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ
  obtain ⟨φ, hφ, F, hF2, hlaw, hUI, hsq, hmean⟩ := gibbs_compactness_of hyp h21 he hQ
    ⟨Cp, p, hp, fun N hN => ⟨(hCp N hN).2.1, (hCp N hN).2.2⟩⟩ (CF := CF)
    (fun N hN ν h1 h2 h3 => ((hF N hN).2 ν h1 h2 h3).1) hrpos hB0 Ns hNs f hf hB
  -- `γ_∞ = γ`
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  have hγeq : gammaInfOf W (μ : Measure (Torus d)) Q = γ :=
    eq_of_isCenteredGaussianCov (isCenteredGaussianCov_gammaInf hT hS hσ0 hσ hQ hC) hγ
  rw [hγeq] at hF2 hlaw hsq hmean
  obtain ⟨B, hBB⟩ := hB
  have hP : ∀ N, IsProbabilityMeasure (gibbs V W N) := fun N => gibbs_isProbabilityMeasure hyp N
  refine ⟨φ, hφ, F, hF2, fun g => ?_, hUI, hmean, hsq, ?_, ?_⟩
  · -- the law of `f`
    have := hlaw 0 (g.compContinuous ⟨Prod.fst, continuous_fst⟩)
    simpa using this
  · -- (2.7) for `f`
    exact hcore (fun k => Ns (φ k)) (hNs.comp hφ.tendsto_atTop) (fun k => f (φ k))
      (fun k => (hf (φ k)).1) ⟨B, fun k => hBB (φ k)⟩ hUI F hF2 hlaw
  · -- (2.7) for `χ ∘ f`
    rintro χ ⟨L, hχ⟩
    refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
    obtain ⟨ψ, hψ, hψb⟩ := extraction_of_frequently_atTop
      (frequently_lt_of_liminf_lt (by isBoundedDefault) hb)
    set c : ℝ := χ 0 ^ 2
    have hc0 : 0 ≤ c := sq_nonneg _
    set L2 : ℝ := 2 * (L : ℝ) ^ 2
    have hL20 : 0 ≤ L2 := by positivity
    -- the functions along the extraction
    set g : (k : ℕ) → Config (Ns (φ (ψ k))) d → ℝ := fun k => χ ∘ f (φ (ψ k))
    have hg1 : ∀ k, MemH1C (gibbs V W (Ns (φ (ψ k)))) (g k) ∧
        energy V W (Ns (φ (ψ k))) (g k) ≤ (L : ℝ≥0∞) ^ 2 * energy V W (Ns (φ (ψ k))) (f (φ (ψ k))) :=
      fun k => memH1C_comp_lipschitz hyp (hf (φ (ψ k))).1 hχ
    have hfm : ∀ k, AEMeasurable (f k) (gibbs V W (Ns k)) := fun k =>
      ((hf k).1.2.1.aestronglyMeasurable.aemeasurable).comp_measurable measurable_flat
    have hpt : ∀ k X, ENNReal.ofReal (g k X ^ 2) ≤
        ENNReal.ofReal (2 * c) + ENNReal.ofReal L2 * ENNReal.ofReal (f (φ (ψ k)) X ^ 2) :=
      fun k X => by
        rw [← ENNReal.ofReal_mul hL20, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by
          have := sq_lipschitz_le hχ (f (φ (ψ k)) X); simp only [g, Function.comp_apply, c, L2]
          linarith)
    have hf2B : ∀ k, ∫⁻ X, ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k) ≤ B := fun k =>
      le_trans le_self_add (hBB k)
    -- the `L²` + energy bound
    have hbound : ∃ B' : NNReal, ∀ k, (∫⁻ X, ENNReal.ofReal (g k X ^ 2) ∂gibbs V W (Ns (φ (ψ k)))) +
        energy V W (Ns (φ (ψ k))) (g k) ≤ B' := by
      refine ⟨Real.toNNReal (2 * c) + (Real.toNNReal L2 + L ^ 2) * B, fun k => ?_⟩
      have h1 : ∫⁻ X, ENNReal.ofReal (g k X ^ 2) ∂gibbs V W (Ns (φ (ψ k))) ≤
          ENNReal.ofReal (2 * c) + ENNReal.ofReal L2 * B := by
        calc ∫⁻ X, ENNReal.ofReal (g k X ^ 2) ∂gibbs V W (Ns (φ (ψ k)))
            ≤ ∫⁻ X, (ENNReal.ofReal (2 * c) + ENNReal.ofReal L2 *
                ENNReal.ofReal (f (φ (ψ k)) X ^ 2)) ∂gibbs V W (Ns (φ (ψ k))) :=
              lintegral_mono (hpt k)
          _ = ENNReal.ofReal (2 * c) + ENNReal.ofReal L2 *
                ∫⁻ X, ENNReal.ofReal (f (φ (ψ k)) X ^ 2) ∂gibbs V W (Ns (φ (ψ k))) := by
              rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          _ ≤ ENNReal.ofReal (2 * c) + ENNReal.ofReal L2 * B := by
              gcongr; exact hf2B _
      have h2 : energy V W (Ns (φ (ψ k))) (g k) ≤ (L : ℝ≥0∞) ^ 2 * B :=
        (hg1 k).2.trans (by gcongr; exact le_trans le_add_self (hBB _))
      calc _ ≤ ENNReal.ofReal (2 * c) + ENNReal.ofReal L2 * B + (L : ℝ≥0∞) ^ 2 * B :=
            add_le_add h1 h2
        _ = _ := by
            simp only [ENNReal.ofReal, ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_pow]
            ring
    -- uniform integrability
    have hUIg : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k, ∫⁻ X in {X | M < g k X ^ 2},
        ENNReal.ofReal (g k X ^ 2) ∂gibbs V W (Ns (φ (ψ k))) ≤ ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨M₁, hM₁⟩ := hUI (ε / 2 / (L2 + 1)) (by positivity)
      set M : ℝ := max M₁ (max 1 (4 * c * B / ε + 1))
      have hM1 : 1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
      have hMM₁ : M₁ ≤ M := le_max_left _ _
      have hMc : 4 * c * B / ε ≤ M := by
        have := (le_max_right 1 (4 * c * B / ε + 1)).trans (le_max_right M₁ _); linarith
      refine ⟨2 * c + L2 * M, fun k => ?_⟩
      set P := gibbs V W (Ns (φ (ψ k)))
      set S := {X | M < f (φ (ψ k)) X ^ 2}
      have hsub : {X | 2 * c + L2 * M < g k X ^ 2} ⊆ S := fun X hX => by
        simp only [Set.mem_setOf_eq] at hX ⊢
        have h := sq_lipschitz_le hχ (f (φ (ψ k)) X)
        simp only [g, Function.comp_apply] at hX
        rcases lt_or_ge M (f (φ (ψ k)) X ^ 2) with hlt | hn
        · exact hlt
        exfalso
        have : L2 * f (φ (ψ k)) X ^ 2 ≤ L2 * M := mul_le_mul_of_nonneg_left hn hL20
        simp only [c, L2] at this hX
        linarith
      -- Markov
      have hmark : ENNReal.ofReal M * P S ≤ B := by
        refine le_trans ?_ (hf2B (φ (ψ k)))
        have hss : S ⊆ {X | ENNReal.ofReal M ≤ ENNReal.ofReal (f (φ (ψ k)) X ^ 2)} :=
          fun X hX => by
            simp only [Set.mem_setOf_eq, S] at hX ⊢
            exact ENNReal.ofReal_le_ofReal hX.le
        calc ENNReal.ofReal M * P S
            ≤ ENNReal.ofReal M * P {X | ENNReal.ofReal M ≤ ENNReal.ofReal (f (φ (ψ k)) X ^ 2)} := by
              gcongr
          _ ≤ _ := mul_meas_ge_le_lintegral₀ ((ENNReal.measurable_ofReal.comp_aemeasurable
              ((hfm (φ (ψ k))).pow_const 2))) _
      have hPS : ENNReal.ofReal (2 * c) * P S ≤ ENNReal.ofReal (ε / 2) := by
        rcases eq_or_lt_of_le hc0 with h0 | hcpos
        · rw [← h0]; simp
        have hMpos : 0 < M := by linarith
        have hPS' : P S ≤ (B : ℝ≥0∞) / ENNReal.ofReal M := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hMpos)) (Or.inl ENNReal.ofReal_ne_top),
            mul_comm]
          exact hmark
        calc ENNReal.ofReal (2 * c) * P S ≤ ENNReal.ofReal (2 * c) * ((B : ℝ≥0∞) / ENNReal.ofReal M) := by
              gcongr
          _ = ENNReal.ofReal (2 * c * B / M) := by
              rw [show (B : ℝ≥0∞) = ENNReal.ofReal B by simp, ← ENNReal.ofReal_div_of_pos hMpos,
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1; ring
          _ ≤ ENNReal.ofReal (ε / 2) := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [div_le_iff₀ hMpos]
              have := mul_le_mul_of_nonneg_right hMc hε.le
              rw [div_mul_cancel₀ _ hε.ne'] at this
              linarith
      calc ∫⁻ X in {X | 2 * c + L2 * M < g k X ^ 2}, ENNReal.ofReal (g k X ^ 2) ∂P
          ≤ ∫⁻ X in S, (ENNReal.ofReal (2 * c) + ENNReal.ofReal L2 *
              ENNReal.ofReal (f (φ (ψ k)) X ^ 2)) ∂P :=
            (lintegral_mono_set hsub).trans (lintegral_mono (hpt k))
        _ = ENNReal.ofReal (2 * c) * P S + ENNReal.ofReal L2 *
              ∫⁻ X in S, ENNReal.ofReal (f (φ (ψ k)) X ^ 2) ∂P := by
            rw [lintegral_add_left measurable_const, setLIntegral_const,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal L2 * ENNReal.ofReal (ε / 2 / (L2 + 1)) := by
            gcongr
            exact (lintegral_mono_set (fun X hX => by
              simp only [S, Set.mem_setOf_eq] at hX ⊢; linarith)).trans (hM₁ (ψ k))
        _ ≤ ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_mul hL20, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have : L2 * (ε / 2 / (L2 + 1)) ≤ ε / 2 := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
            linarith
    -- the limit `χ ∘ F`
    have hχF : MemLp (χ ∘ F) 2 γ := by
      have hdom : MemLp ((fun _ => |χ 0|) + fun z => (L : ℝ) * ‖F z‖) 2 γ :=
        (memLp_const (|χ 0|)).add (hF2.norm.const_mul (L : ℝ))
      refine hdom.of_le (hχ.continuous.comp_aestronglyMeasurable hF2.aestronglyMeasurable)
        (Eventually.of_forall fun z => ?_)
      have h := hχ.dist_le_mul (F z) 0
      rw [Real.dist_eq, Real.dist_eq, sub_zero] at h
      rw [Pi.add_apply, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Function.comp_apply,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ |χ 0| + L * |F z|)]
      have := abs_sub_abs_le_abs_sub (χ (F z)) (χ 0)
      linarith
    have hlawg : ∀ (J : ℕ) (h : ℝ × (Fin J → ℝ) →ᵇ ℝ), Tendsto (fun k => ∫ X, h (g k X,
        fun n => fluct e (Ns (φ (ψ k))) n X) ∂gibbs V W (Ns (φ (ψ k)))) atTop
          (𝓝 (∫ z, h ((χ ∘ F) z, fun n => z n) ∂γ)) := fun J h => by
      have := (hlaw J (h.compContinuous ⟨fun q => (χ q.1, q.2),
        (hχ.continuous.comp continuous_fst).prodMk continuous_snd⟩)).comp hψ.tendsto_atTop
      simpa [Function.comp_def, g] using this
    have hNs' : Tendsto (fun k => Ns (φ (ψ k))) atTop atTop := hNs.comp (hφ.comp hψ).tendsto_atTop
    have hg1' : ∀ k, MemH1C (gibbs V W (Ns (φ (ψ k)))) (g k) := fun k => (hg1 k).1
    have hcore' : gaussForm (lamShift lam) γ (χ ∘ F) ≤
        liminf (fun k => energy V W (Ns (φ (ψ k))) (g k)) atTop :=
      hcore (fun k => Ns (φ (ψ k))) hNs' g hg1' hbound hUIg (χ ∘ F) hχF hlawg
    refine hcore'.trans ?_
    calc liminf (fun k => energy V W (Ns (φ (ψ k))) (g k)) atTop
        ≤ liminf (fun _ : ℕ => b) atTop := liminf_le_liminf (Eventually.of_forall fun k =>
          (hψb k).le)
      _ = b := liminf_const b

end

end SharpLSI
