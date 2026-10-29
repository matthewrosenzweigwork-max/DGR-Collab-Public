import FullLabeledLSI.Paper.Sec5LNDefs

/-!
# Large-N assembly A: ScoreData for the regularized laws
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ## 1. Instantiation for the regularized laws -/

/-- **`ScoreData` for `Qreg`.**  Fields: `eq` is `rfl`; `dens` from `Qreg_bounds`, `measurable_Qreg`;
`gradW` from `isWeakGrad_Qreg` (needs `hgi`, from `hg2`); `gradM` from `hgm`; `gradL2` from
`memLp_GQreg`; `sM` from `measurable_sfun`; `sL2`: `∑ᵢ∑ₖ∫⁻ s² dν = (4/Z) ℰ_N(regF) < ∞` by
`fisher_Qreg_eq`, `energy_regF_le`, `energy_lt_top`, then `memLp_two_iff_integrable_sq`/`lintegral` to
`Integrable`; `score` from `GQreg_flat_eq` (`GQ(flat X)(i,k) = Q·(s - Gfun - ∇Φ)`, with `Q > 0`) and
`Gfun = gsG(flat X)(i,k) = weakGradC (Ucentered) = Gpart` ν-a.e. (`particle_force hd hyp hμ`.2.2 N hN,
`hG N hN`, `ν ≪ volume` via `withDensity_absolutelyContinuous`).  `bF_ae`/`G_ae` are `hbF`/`hG`.
Estimate: ~110 lines. -/
theorem scoreData_Qreg (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ}
    {Bb : ℝ} (hB : ForceRep bF bΔ Bb)
    (hbF : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k,
      bForce W (μ : Measure (Torus d)) p.1 p.2 k = bF p.1 p.2 k)
    (hG : ∀ N : ℕ, 1 ≤ N → ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ i k,
      weakGradC (Ucentered W (μ : Measure (Torus d)) N) X i k = Gpart bF bΔ N X i k)
    {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hfm : Measurable f)
    (hf : MemH1C (gibbs V W N) f)
    {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hw : IsWeakGrad (f ∘ unflat) g)
    (hgm : ∀ p, Measurable fun y => g y p) (hg2 : ∀ p, MemLp (fun y => g y p) 2 volume) (n : ℕ) :
    ∃ c C : ℝ, ScoreData V W (μ : Measure (Torus d))
      ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X))
      (Qreg V W n f) c C (GQreg V W (μ : Measure (Torus d)) n f g) (sfun n f g) bF bΔ Bb := by
  have hac : (μ : Measure (Torus d)) ≪ haar d := minimizer_ac hyp hμ
  have hgi : ∀ p, Integrable (fun y => g y p) volume := fun p => (hg2 p).integrable one_le_two
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  refine ⟨c, C, ?_⟩
  have hQm := measurable_Qreg hyp hf hfm n
  -- finiteness of the Fisher sum
  have hfin : ∀ i k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2)
      ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) ≠ ⊤ := by
    intro i k
    have h1 := fisher_Qreg_eq hyp hf hfm hw hgm n
    have h2 : energy V W N (regF n f) < ⊤ :=
      lt_of_le_of_lt (energy_regF_le hyp hf n) (energy_lt_top hyp hf)
    have h3 : (∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X))) ≠ ⊤ := by
      rw [h1]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2.ne
    refine ne_top_of_le_ne_top h3 ?_
    refine (Finset.single_le_sum (f := fun k => ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2)
      ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)))
      (fun _ _ => bot_le) (Finset.mem_univ k)).trans ?_
    exact Finset.single_le_sum (f := fun i => ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2)
      ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)))
      (fun _ _ => bot_le) (Finset.mem_univ i)
  -- a.e. identification of the force
  have hU := isWeakGrad_gsU hyp hac hN
  have hGw : ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ i k,
      Gfun W (μ : Measure (Torus d)) i k X = Gpart bF bΔ N X i k := by
    have h2 := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hU⟩) hU
    have h3 := (measurePreserving_flat' N).quasiMeasurePreserving.ae h2
    filter_upwards [h3, hG N hN] with X hX hX' i k
    rw [← hX' i k]
    have := congrFun hX (i, k)
    exact this.symm
  refine ⟨rfl, ⟨hQm, hc, fun X => (hb X).1, fun X => (hb X).2⟩,
    isWeakGrad_Qreg hyp hac hN hf hw hgi n,
    measurable_GQreg hyp hac hN hfm hf hw hgm hg2 hgi n,
    memLp_GQreg hyp hac hN hfm hf n hg2, hB, hbF, hG N hN,
    measurable_sfun hyp hac hN hfm hf hw hgm hg2 hgi n, ?_, ?_⟩
  · intro i k
    refine ⟨((measurable_sfun hyp hac hN hfm hf hw hgm hg2 hgi n i k).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)]
    exact lt_top_iff_ne_top.mpr (hfin i k)
  · have hν : ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X))
        ≪ volume := withDensity_absolutelyContinuous _ _
    filter_upwards [hν.ae_le hGw] with X hX i k
    rw [GQreg_flat_eq hyp hf n i k X, ← hX i k]
    have hQ : 0 < Qreg V W n f X := hc.trans_le (hb X).1
    field_simp

/-- `(Σᵢ Σₖ ∫⁻ ofReal (s²) dν).toReal = Σᵢ Σₖ ∫ s² dν` (converts the `ℝ≥0∞` Fisher sum of
`large_N_reg` into `fisherS`).  Proof: `ofReal_integral_eq_lintegral_ofReal` termwise (`sL2`) and
`ENNReal.toReal_sum`.  ~20 lines. -/
theorem fisher_toReal_eq {N : ℕ} {ν : Measure (Config N d)} [IsFiniteMeasure ν]
    {s : Fin N → Fin d → Config N d → ℝ} (hs : ∀ i k, Integrable (fun X => s i k X ^ 2) ν) :
    (∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (s i k X ^ 2) ∂ν).toReal = fisherS ν s := by
  have hfin : ∀ i k, ∫⁻ X, ENNReal.ofReal (s i k X ^ 2) ∂ν ≠ ⊤ := fun i k =>
    (hs i k).lintegral_lt_top.ne
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.sum_ne_top.mpr fun k _ => hfin i k)]
  unfold fisherS
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_sum (fun k _ => hfin i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
    (hs i k).aestronglyMeasurable).symm


end SharpLSI.FL
