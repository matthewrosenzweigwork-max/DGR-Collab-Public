import FullLabeledLSI.Paper.Prop23FAltA

/-!
# Proposition 2.3, WP-F (alt): `(reduce-J)`

For an admissible family `f` and `Ψ_N = psiG f_N`, the comparison expression `𝒥_{N,R}(Ψ_N)` is
eventually below `ℰ_N(f_N) - (b/2) Ent_{P_N}(f_N²) + ε`, for all `R ≥ R₁(ε)` (manuscript (eq:reduce-J)).
The rate `b` is an abstract real `b0`, the limit of the `b_R` along `R`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **WP-F, `(reduce-J)`.** -/
theorem reduce_J_alt (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (CR : ℕ → ℕ → ℕ → ℝ)
    {Kinf : ℝ} (hK0 : 0 < Kinf)
    (hKN : Tendsto (fun N => centeredPartition W (μ : Measure (Torus d)) N) atTop (𝓝 Kinf))
    (hκ : Tendsto (fun R => kappaR A R) atTop (𝓝 Kinf))
    (hU : ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ →
      Tendsto (fun R => ⨆ N ∈ {N : ℕ | 1 ≤ N},
          eLpNorm (fun X => Ucentered W (μ : Measure (Torus d)) N X - URN A R N X) q
            (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))) atTop (𝓝 0))
    {b0 : ℝ} (hb0 : 0 ≤ b0)
    (hbR : Tendsto (fun R => (bRate (μ : Measure (Torus d)) lam (CR R)).toReal) atTop (𝓝 b0))
    (f : (N : ℕ) → Config N d → ℝ) (hf : ∀ N, MemH1C (gibbs V W N) (f N)) (B : NNReal)
    (hB : ∀ N, (∀ᵐ X ∂gibbs V W N, |f N X| ≤ B) ∧ energy V W N (f N) ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ R₁ : ℕ, ∀ R ≥ R₁, ∀ᶠ N in atTop,
      Jexpr A lam (CR R) R (psiG W (μ : Measure (Torus d)) N (f N)) - ε ≤
        (energy V W N (f N)).toReal -
          b0 / 2 * (ent (gibbs V W N) (fun X => f N X ^ 2)).toReal := by
  intro ε hε
  have hac := minimizer_ac hyp hμ
  obtain ⟨p, Cg, hp, hCg, hG⟩ := ground_transform_nosym hd hyp hr hμ
  set M₂ : ℝ := Cg * (B : ℝ) ^ (2 * p) with hM₂
  set ME : ℝ := (B : ℝ) ^ 2 * |Real.log ((B : ℝ) ^ 2)| + 1 with hME
  have hME0 : 0 ≤ ME := by rw [hME]; positivity
  have hb1 : 0 < b0 + 1 := by linarith
  set ε₃ : ℝ := ε / (2 * (b0 + 1)) with hε₃
  have hε₃0 : 0 < ε₃ := by rw [hε₃]; positivity
  set η : ℝ := min 1 (ε / (2 * (ME + 1))) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  obtain ⟨R₁, hR₁⟩ := energy_replace hd hyp hr hμ he A (B : ℝ) (B : ℝ) (ε / 4) (by positivity)
  obtain ⟨R₂, hR₂⟩ := entropy_terms_replace A hK0 hKN hκ hU hp M₂ ε₃ hε₃0
  obtain ⟨R₃, hR₃⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hbR) η hη0)
  refine ⟨max (max R₁ R₂) R₃, fun R hR => ?_⟩
  have hRa : R ≥ R₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRb : R ≥ R₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hRc : R ≥ R₃ := le_trans (le_max_right _ _) hR
  have hbη : |(bRate (μ : Measure (Torus d)) lam (CR R)).toReal - b0| ≤ η := by
    have := hR₃ R hRc
    rw [Real.dist_eq] at this
    exact this.le
  have hbR0 : 0 ≤ (bRate (μ : Measure (Torus d)) lam (CR R)).toReal := ENNReal.toReal_nonneg
  have hbR1 : (bRate (μ : Measure (Torus d)) lam (CR R)).toReal ≤ b0 + 1 := by
    have h1 : η ≤ 1 := min_le_left _ _
    linarith [(abs_le.1 hbη).2]
  have hev3 := integral_VNR_sub_vR_small hyp hμ he hφ heC A R hp M₂ (ε / 4) (by positivity)
  filter_upwards [hR₁ R hRa, hR₂ R hRb, hev3, eventually_ge_atTop 1] with N hN1 hN2 hN3 hNge
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set Ψ : Config N d → ℝ := psiG W (μ : Measure (Torus d)) N (f N) with hΨdef
  obtain ⟨hΨH, -, -, hΨp⟩ := hG N hNge (f N) (B : ℝ) (hf N) (hB N).1
  have hΨ2 : MemLp Ψ 2 (QN (μ : Measure (Torus d)) N) :=
    (memLp_map_measure_iff hΨH.2.1.aestronglyMeasurable measurable_flat.aemeasurable).1 hΨH.2.1
  have hΨmeas := hΨ2.aestronglyMeasurable
  have hf2 : MemLp (f N) 2 (gibbs V W N) :=
    (memLp_map_measure_iff (hf N).2.1.aestronglyMeasurable measurable_flat.aemeasurable).1
      (hf N).2.1
  -- energy side
  have hshU : shEn (μ : Measure (Torus d)) Ψ (Ucentered W (μ : Measure (Torus d)) N) =
      energy V W N (f N) := (energy_ground_identity hyp hμ hNge (hf N)).symm
  have hshUle : shEn (μ : Measure (Torus d)) Ψ (Ucentered W (μ : Measure (Torus d)) N) ≤
      ENNReal.ofReal (B : ℝ) := by
    rw [hshU]
    refine (hB N).2.trans ?_
    rw [ENNReal.ofReal_coe_nnreal]
  have h1 := hN1 (f N) (hf N) (hB N).1 hshUle
  rw [hshU] at h1
  obtain ⟨-, h2⟩ := schrodinger_identity hyp hμ he hφ heC A R hNge hΨH
  have h3 := hN3 Ψ hΨmeas hΨp
  -- entropy side
  have h4 := entropy_ground_identity hyp hμ (hf N) (hB N).1
  have h5 := hN2 Ψ hΨmeas hΨp
  -- integrability
  have hUBM : BM (Ucentered W (μ : Measure (Torus d)) N) :=
    ⟨Ucentered_bdd hyp (μ : Measure (Torus d)) N, measurable_Ucentered hyp _ N⟩
  have iU : Integrable (fun X => Ψ X ^ 2 * Ucentered W (μ : Measure (Torus d)) N X)
      (QN (μ : Measure (Torus d)) N) := fa_integrable_sq_mul hΨ2 hUBM (Eventually.of_forall fun _ => rfl)
  have iR : Integrable (fun X => Ψ X ^ 2 * URN A R N X) (QN (μ : Measure (Torus d)) N) :=
    fa_integrable_sq_mul hΨ2 (fa_BM_uR hφ A R N)
      (fa_ae_comp hac heC N (uR A R))
  have iV : Integrable (fun X => Ψ X ^ 2 * VNR A lam eC R N X) (QN (μ : Measure (Torus d)) N) :=
    fa_integrable_sq_mul hΨ2 (fa_BM_VNR hφ A lam R N) (Eventually.of_forall fun _ => rfl)
  have iv : Integrable (fun X => Ψ X ^ 2 * vR A lam R (fun n => fluct e N n X))
      (QN (μ : Measure (Torus d)) N) :=
    fa_integrable_sq_mul hΨ2 (fa_BM_vR hφ A lam R N) (fa_ae_comp hac heC N (vR A lam R))
  have hsubV : ∫ X, Ψ X ^ 2 * (VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X))
        ∂QN (μ : Measure (Torus d)) N =
      ∫ X, VNR A lam eC R N X * Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N -
        ∫ X, Ψ X ^ 2 * vR A lam R (fun n => fluct e N n X) ∂QN (μ : Measure (Torus d)) N := by
    simp_rw [mul_sub]
    rw [integral_sub iV iv]
    simp_rw [mul_comm (Ψ _ ^ 2)]
  have hsubU : ∫ X, Ψ X ^ 2 * (Ucentered W (μ : Measure (Torus d)) N X - URN A R N X)
        ∂QN (μ : Measure (Torus d)) N =
      ∫ X, Ψ X ^ 2 * Ucentered W (μ : Measure (Torus d)) N X ∂QN (μ : Measure (Torus d)) N -
        ∫ X, Ψ X ^ 2 * URN A R N X ∂QN (μ : Measure (Torus d)) N := by
    simp_rw [mul_sub]
    exact integral_sub iU iR
  rw [hsubV] at h3
  rw [hsubU] at h5
  have hEgle := fa_ent_sq_toReal_le (gibbs V W N) hf2.aestronglyMeasurable (hB N).1
  have hJ : Jexpr A lam (CR R) R Ψ =
      (refEnergy (μ : Measure (Torus d)) Ψ).toReal +
        ∫ X, Ψ X ^ 2 * vR A lam R (fun n => fluct e N n X) ∂QN (μ : Measure (Torus d)) N -
        (bRate (μ : Measure (Torus d)) lam (CR R)).toReal / 2 *
          ((ent (QN (μ : Measure (Torus d)) N) (fun X => Ψ X ^ 2)).toReal +
            ∫ X, Ψ X ^ 2 * URN A R N X ∂QN (μ : Measure (Torus d)) N +
            Real.log (kappaR A R) * ∫ X, Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N) := rfl
  rw [hJ]
  have key := fa_alg (a1 := (energy V W N (f N)).toReal)
    (shR := (shEn (μ : Measure (Torus d)) Ψ (URN A R N)).toReal)
    (rE := (refEnergy (μ : Measure (Torus d)) Ψ).toReal)
    (IV := ∫ X, VNR A lam eC R N X * Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N)
    (IVe := ∫ X, Ψ X ^ 2 * vR A lam R (fun n => fluct e N n X) ∂QN (μ : Measure (Torus d)) N)
    (eQ := (ent (QN (μ : Measure (Torus d)) N) (fun X => Ψ X ^ 2)).toReal)
    (IU := ∫ X, Ψ X ^ 2 * URN A R N X ∂QN (μ : Measure (Torus d)) N)
    (IUN := ∫ X, Ψ X ^ 2 * Ucentered W (μ : Measure (Torus d)) N X ∂QN (μ : Measure (Torus d)) N)
    (lg := Real.log (kappaR A R)) (lK := Real.log (centeredPartition W (μ : Measure (Torus d)) N))
    (m := ∫ X, Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N)
    (Eg := (ent (gibbs V W N) (fun X => f N X ^ 2)).toReal)
    (ε₁ := ε / 4) (ε₂ := ε / 4) (ε₃ := ε₃) (η := η) (ME := ME)
    (bR := (bRate (μ : Measure (Torus d)) lam (CR R)).toReal) (b0 := b0)
    h1 h2 h3 h4 h5
    ENNReal.toReal_nonneg hEgle hbR0 hbR1 hbη hη0.le
  have hsum : ε / 4 + ε / 4 + (b0 + 1) / 2 * ε₃ + η / 2 * ME ≤ ε := by
    have e1 : (b0 + 1) / 2 * ε₃ = ε / 4 := by rw [hε₃]; field_simp; ring
    have e2 : η / 2 * ME ≤ ε / 4 := by
      have hη1 : η ≤ ε / (2 * (ME + 1)) := min_le_right _ _
      calc η / 2 * ME ≤ ε / (2 * (ME + 1)) / 2 * ME := by gcongr
        _ ≤ ε / 4 := by
          rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hε, hME0]
    linarith
  linarith

end SharpLSI.FL
