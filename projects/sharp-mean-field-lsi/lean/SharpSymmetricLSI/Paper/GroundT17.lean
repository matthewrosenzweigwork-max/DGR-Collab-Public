import SharpSymmetricLSI.Paper.GroundT16
import SharpSymmetricLSI.Paper.R29Main

/-!
# R30: `gibbs_compactness_of` (Section 7.2), conditional on Prop. 2.1, Lemma 5.2, (5.14), Prop. 2.2
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem abs_integral_sub_clip_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {u : Ω → ℝ} (hu : MemLp u 2 P) {M : ℝ} (hM : 0 < M) :
    |∫ x, u x ∂P - ∫ x, clipB M (u x) ∂P| ≤ (∫ x, u x ^ 2 ∂P) / M := by
  have hui : Integrable u P := hu.integrable one_le_two
  have hci : Integrable (fun x => clipB M (u x)) P :=
    Integrable.of_bound ((clipB M).continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable)
      ‖clipB M‖ (Eventually.of_forall fun x => (clipB M).norm_coe_le_norm _)
  rw [← integral_sub hui hci, ← integral_div]
  refine (abs_integral_le_integral_abs).trans (integral_mono (hui.sub hci).abs
    (hu.integrable_sq.div_const M) fun x => abs_sub_clipB_le hM (u x))

/-- **Section 7.2**: compactness, joint convergence, uniform integrability and (7.10). -/
theorem gibbs_compactness_of (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (h21 : Prop21Conclusion V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos (Tmat W μ e) Q)
    (hpart : ∃ B p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      |Real.log (centeredPartition W μ N)| ≤ B ∧
      ∫ X, (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ B)
    {CF : ℝ}
    (hForce : ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      IsSymmetricMeasure ν → klDiv ν (gibbs V W N) ≠ ⊤ →
      ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν ≤
        ENNReal.ofReal CF * (klDiv ν (gibbs V W N) + 1))
    {r : ℝ} (hr : 0 < r) {B0 : ℝ≥0}
    (hDef : ∀ N : ℕ, 1 ≤ N → ∀ f : Config N d → ℝ, MemH1C (gibbs V W N) f → IsSymmetric f →
      ent (gibbs V W N) (fun X => f X ^ 2) ≤
        ENNReal.ofReal (2 / r) * energy V W N f + (B0 : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N)
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop) (f : (k : ℕ) → Config (Ns k) d → ℝ)
    (hf : ∀ k, MemH1C (gibbs V W (Ns k)) (f k) ∧ IsSymmetric (f k))
    (hB : ∃ B : NNReal, ∀ k,
      (∫⁻ X, ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k)) + energy V W (Ns k) (f k) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : (ℕ → ℝ) → ℝ, MemLp F 2 (gammaInfOf W μ Q) ∧
      (∀ (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ),
        Tendsto (fun k => ∫ X, g (f (φ k) X, fun n => fluct e (Ns (φ k)) n X)
            ∂gibbs V W (Ns (φ k))) atTop
          (𝓝 (∫ z, g (F z, fun n => z n) ∂gammaInfOf W μ Q))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k,
        ∫⁻ X in {X | M < f (φ k) X ^ 2}, ENNReal.ofReal (f (φ k) X ^ 2) ∂gibbs V W (Ns (φ k))
          ≤ ENNReal.ofReal ε) ∧
      Tendsto (fun k => ∫ X, f (φ k) X ^ 2 ∂gibbs V W (Ns (φ k))) atTop
        (𝓝 (∫ z, F z ^ 2 ∂gammaInfOf W μ Q)) ∧
      Tendsto (fun k => ∫ X, f (φ k) X ∂gibbs V W (Ns (φ k))) atTop
        (𝓝 (∫ z, F z ∂gammaInfOf W μ Q)) := by
  set μm := (μ : Measure (Torus d))
  have hμ := h21.minimizer
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  obtain ⟨hKN, hKpos, hint, q, Bq, hq, hBq⟩ := partition_limit_of hyp h21 he hQ hpart
  obtain ⟨Bp, p, -, hpB⟩ := hpart
  obtain ⟨Cr, hCr0, hCr⟩ := rescaled_ground_state hyp hμ hForce hr hDef
  obtain ⟨CU, hCU⟩ := integral_Ucentered_sq_le hyp hμ he
  obtain ⟨B, hB⟩ := hB
  set K' := Kinf W μm Q
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 (hNs.eventually (eventually_ge_atTop 1))
  set Ns' : ℕ → ℕ := fun k => Ns (k + k0)
  have hNs' : Tendsto Ns' atTop atTop := hNs.comp (tendsto_add_atTop_nat k0)
  have hN1 : ∀ k, 1 ≤ Ns' k := fun k => hk0 _ (Nat.le_add_left _ _)
  set f' : (k : ℕ) → Config (Ns' k) d → ℝ := fun k => f (k + k0)
  set Ψ' : (k : ℕ) → Config (Ns' k) d → ℝ := fun k X =>
    f' k X * Real.sqrt (rexp (-Ucentered W μ (Ns' k) X) / K')
  have hRS := fun k => hCr (Ns' k) (hN1 k) K' hKpos (f' k) (hf _).1 (hf _).2
  have hKle : ∀ N : ℕ, 1 ≤ N → centeredPartition W μ N ≤ rexp Bp := fun N hN => by
    have hK := centeredPartition_pos hyp μm N
    rw [← Real.exp_log hK]; exact Real.exp_le_exp.2 ((le_abs_self _).trans (hpB N hN).1)
  have hKge : ∀ N : ℕ, 1 ≤ N → rexp (-Bp) ≤ centeredPartition W μ N := fun N hN => by
    have hK := centeredPartition_pos hyp μm N
    rw [← Real.exp_log hK]; exact Real.exp_le_exp.2 (by
      have := (abs_le.1 (hpB N hN).1).1; linarith)
  have hB' : ∃ Bb : NNReal, ∀ k, ∫⁻ X, ENNReal.ofReal (Ψ' k X ^ 2 + gradSqC (Ψ' k) X)
      ∂Measure.pi (fun _ : Fin (Ns' k) => μm) ≤ Bb := by
    refine ⟨(rexp Bp / K' * Cr).toNNReal * B, fun k => (hRS k).2.2.trans ?_⟩
    rw [ENNReal.coe_mul, show (((rexp Bp / K' * Cr).toNNReal : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (rexp Bp / K' * Cr) from rfl, add_comm (energy _ _ _ _)]
    gcongr
    · exact hKle _ (hN1 k)
    · exact hB _
  obtain ⟨φ, hφ, Ψinf, hΨL2, -, hnorm, hjoint, hui⟩ :=
    reference_compactness_aux hyp hμ he Ns' hNs' Ψ' (fun k => ⟨(hRS k).1, (hRS k).2.1⟩) hB'
  have hjointQ := hjoint Q hQ
  set F : (ℕ → ℝ) → ℝ := fun z => Ψinf z / Real.sqrt (wK K' (Uinf W μm Q z))
  have hKsub : Tendsto (fun k => centeredPartition W μ (Ns' (φ k))) atTop (𝓝 K') :=
    hKN.comp (hNs'.comp hφ.tendsto_atTop)
  have hratio : Tendsto (fun k => K' / centeredPartition W μ (Ns' (φ k))) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := K')).div hKsub hKpos.ne'
    rwa [div_self hKpos.ne'] at this
  have hΨm : ∀ k, AEStronglyMeasurable (Ψ' k) (Measure.pi fun _ : Fin (Ns' k) => μm) :=
    fun k => (memLp_of_memH1C_pi (hRS k).2.1).aestronglyMeasurable
  have hΨinfm : AEStronglyMeasurable Ψinf gammaRef := hΨL2.aestronglyMeasurable
  have hgI : ∀ G : (ℕ → ℝ) → ℝ, ∫ z, G z ∂gammaInfOf W μm Q =
      ∫ z, rexp (-Uinf W μm Q z) / K' * G z ∂gammaRef := integral_gammaInf hT hS hσ0 hσ hQ
  have hprob : IsProbabilityMeasure (gammaInfOf W μm Q) :=
    isProbabilityMeasure_gammaInf hT hS hσ0 hσ hQ
  have hFm : AEStronglyMeasurable F gammaRef := by
    have hc : Continuous fun p : ℝ × ℝ => p.1 / Real.sqrt (wK K' p.2) :=
      continuous_fst.div (Real.continuous_sqrt.comp ((continuous_wK K').comp continuous_snd))
        fun p => (Real.sqrt_pos.2 (wK_pos hKpos _)).ne'
    exact hc.comp_aestronglyMeasurable (hΨinfm.prodMk (aestronglyMeasurable_Uinf hQ))
  have hFsq : ∀ z, rexp (-Uinf W μm Q z) / K' * F z ^ 2 = Ψinf z ^ 2 := fun z => by
    simp only [F]
    rw [div_pow, Real.sq_sqrt (wK_pos hKpos _).le]
    have := wK_pos hKpos (Uinf W μm Q z)
    unfold wK at this ⊢
    field_simp
  -- `F ∈ L²(γ_∞)`
  have hF2 : MemLp F 2 (gammaInfOf W μm Q) := by
    refine memLp_two_of_lintegral (hFm.mono_ac (withDensity_absolutelyContinuous _ _)) ?_
    unfold gammaInfOf
    rw [lintegral_withDensity_eq_lintegral_mul₀ (g := fun z => ENNReal.ofReal (F z ^ 2))
      (aemeasurable_dens (W := W) (μ := μm) hT hS hσ0 hσ hQ)
      (hFm.pow 2).aemeasurable.ennreal_ofReal]
    have : ∀ z, (fun z => ENNReal.ofReal (rexp (-Uinf W μm Q z) / Kinf W μm Q)) z *
        ENNReal.ofReal (F z ^ 2) = ENNReal.ofReal (Ψinf z ^ 2) := fun z => by
      rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hKpos.le), hFsq]
    simp only [Pi.mul_apply, this]
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).1
      hΨL2.integrable_sq.2
  -- (i) the joint law
  have hjointG : ∀ (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun k => ∫ X, g (f (φ k + k0) X, fun n => fluct e (Ns (φ k + k0)) n X)
          ∂gibbs V W (Ns (φ k + k0))) atTop
        (𝓝 (∫ z, g (F z, fun n => z n) ∂gammaInfOf W μm Q)) := by
    intro J g
    have h1 := tendsto_gibbs_joint hyp hμ he hQ hKpos hq hBq hint (fun k => Ns' (φ k))
      (fun k => hN1 _) (fun k => f' (φ k)) (fun k => hΨm (φ k)) hΨinfm
      (fun J g => hjointQ J g) J g
    have h2 := hratio.mul h1
    rw [one_mul] at h2
    rw [hgI]
    refine h2.congr fun k => ?_
    rw [integral_gibbs_eq' hyp hμ, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    have hK := centeredPartition_pos hyp μm (Ns' (φ k))
    simp only [f']
    field_simp
    rfl
  -- (iii) the norms
  have hL2 : Tendsto (fun k => ∫ X, f (φ k + k0) X ^ 2 ∂gibbs V W (Ns (φ k + k0))) atTop
      (𝓝 (∫ z, F z ^ 2 ∂gammaInfOf W μm Q)) := by
    have h2 := hratio.mul hnorm
    rw [one_mul] at h2
    rw [hgI]
    simp_rw [hFsq]
    refine h2.congr fun k => ?_
    rw [integral_gibbs_eq' hyp hμ, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    have hK := centeredPartition_pos hyp μm (Ns' (φ k))
    simp only [Ψ', f']
    rw [mul_pow, Real.sq_sqrt (div_nonneg (Real.exp_pos _).le hKpos.le)]
    field_simp
    rfl
  -- (ii) uniform integrability
  have huiG : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k,
      ∫⁻ X in {X | M < f (φ k + k0) X ^ 2}, ENNReal.ofReal (f (φ k + k0) X ^ 2)
        ∂gibbs V W (Ns (φ k + k0)) ≤ ENNReal.ofReal ε := by
    intro ε hε
    set c0 := K' * rexp Bp
    have hc0 : 0 < c0 := by positivity
    set ε' := ε / (3 * c0)
    have hε' : 0 < ε' := by positivity
    obtain ⟨L0, hL0⟩ := hui ε' hε'
    set L := max L0 1
    have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    set CU' := max CU 0
    set t := Real.sqrt (L * CU' / ε') + 1
    have ht : 0 < t := by positivity
    have htb : L * (CU' / t ^ 2) ≤ ε' := by
      have h1 : L * CU' / ε' ≤ t ^ 2 := by
        have := Real.sq_sqrt (show 0 ≤ L * CU' / ε' by positivity)
        nlinarith [Real.sqrt_nonneg (L * CU' / ε')]
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hε'] at h1
      linarith
    refine ⟨L / wK K' t, fun k => ?_⟩
    have hfm := (memLp_of_memH1C hyp (hf (φ k + k0)).1).aestronglyMeasurable
    have hui' : ∫⁻ X in {X | L < (f (φ k + k0) X *
        Real.sqrt (rexp (-Ucentered W μ (Ns' (φ k)) X) / K')) ^ 2},
        ENNReal.ofReal ((f (φ k + k0) X *
          Real.sqrt (rexp (-Ucentered W μ (Ns' (φ k)) X) / K')) ^ 2)
        ∂Measure.pi (fun _ : Fin (Ns' (φ k)) => μm) ≤ ENNReal.ofReal ε' :=
      (lintegral_mono_set fun X (hX : L < _) => lt_of_le_of_lt (le_max_left _ _) hX).trans (hL0 k)
    have h := ui_transfer hyp hμ hKpos hfm hL ht ((hCU _ (hN1 (φ k))).trans (le_max_left CU 0))
      hui'
    refine h.trans ?_
    have hK := centeredPartition_pos hyp μm (Ns' (φ k))
    have hc : K' / centeredPartition W μ (Ns' (φ k)) ≤ c0 := by
      rw [div_le_iff₀ hK]
      have := hKge _ (hN1 (φ k))
      calc K' = K' * rexp Bp * rexp (-Bp) := by rw [mul_assoc, ← Real.exp_add]; simp
        _ ≤ c0 * centeredPartition W μ (Ns' (φ k)) := by
          simp only [c0]; exact mul_le_mul_of_nonneg_left this (by positivity)
    calc ENNReal.ofReal (K' / centeredPartition W μ (Ns' (φ k))) *
          (ENNReal.ofReal ε' + (ENNReal.ofReal ε' + ENNReal.ofReal (L * (CU' / t ^ 2))))
        ≤ ENNReal.ofReal c0 * (ENNReal.ofReal ε' + (ENNReal.ofReal ε' + ENNReal.ofReal ε')) := by
          gcongr
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add hε'.le hε'.le, ← ENNReal.ofReal_add hε'.le (by positivity),
            ← ENNReal.ofReal_mul hc0.le]
          congr 1
          simp only [ε']; field_simp; ring
  -- (iv) the means
  have hmean : Tendsto (fun k => ∫ X, f (φ k + k0) X ∂gibbs V W (Ns (φ k + k0))) atTop
      (𝓝 (∫ z, F z ∂gammaInfOf W μm Q)) := by
    have hfL : ∀ k, MemLp (f (φ k + k0)) 2 (gibbs V W (Ns (φ k + k0))) := fun k =>
      memLp_of_memH1C hyp (hf _).1
    have hfsq : ∀ k, ∫ X, f (φ k + k0) X ^ 2 ∂gibbs V W (Ns (φ k + k0)) ≤ B := fun k => by
      have := gibbs_isProbabilityMeasure hyp (Ns (φ k + k0))
      have h1 : ENNReal.ofReal (∫ X, f (φ k + k0) X ^ 2 ∂gibbs V W (Ns (φ k + k0))) ≤ B := by
        rw [ofReal_integral_eq_lintegral_ofReal (hfL k).integrable_sq
          (ae_of_all _ fun _ => sq_nonneg _)]
        exact le_self_add.trans (hB _)
      simpa using (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).1 h1
    set SF := ∫ z, F z ^ 2 ∂gammaInfOf W μm Q
    refine tendsto_of_trunc
      (b := fun M k => ∫ X, clipB M (f (φ k + k0) X) ∂gibbs V W (Ns (φ k + k0)))
      (b0 := fun M => ∫ z, clipB M (F z) ∂gammaInfOf W μm Q)
      (fun M => hjointG 0 ((clipB M).compContinuous ⟨Prod.fst, continuous_fst⟩))
      fun ε hε => ?_
    set A := max (B : ℝ) SF + 1
    have hA : 0 < A := by positivity
    refine ⟨A / ε, fun k => ?_, ?_⟩
    · have := gibbs_isProbabilityMeasure hyp (Ns (φ k + k0))
      refine (abs_integral_sub_clip_le (hfL k) (by positivity)).trans ?_
      rw [div_le_iff₀ (by positivity)]
      have : (∫ X, f (φ k + k0) X ^ 2 ∂gibbs V W (Ns (φ k + k0))) ≤ A := by
        have := hfsq k; have := le_max_left (B : ℝ) SF; linarith
      calc _ ≤ A := this
        _ = ε * (A / ε) := by field_simp
    · refine (abs_integral_sub_clip_le hF2 (by positivity)).trans ?_
      rw [div_le_iff₀ (by positivity)]
      have : SF ≤ A := by have := le_max_right (B : ℝ) SF; linarith
      calc _ ≤ A := this
        _ = ε * (A / ε) := by field_simp
  exact ⟨fun k => φ k + k0, fun a b hab => Nat.add_lt_add_right (hφ hab) k0, F, hF2,
    hjointG, huiG, hL2, hmean⟩

end SharpLSI
