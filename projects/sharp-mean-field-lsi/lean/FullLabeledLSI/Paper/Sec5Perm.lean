import FullLabeledLSI.Infra.RevealKL
import FullLabeledLSI.Paper.PermAvg
import SharpSymmetricLSI.Paper.R37Particle
import SharpSymmetricLSI.Paper.Sec5_6
import SharpSymmetricLSI.Statements.R19_Lemma_5_2
import SharpSymmetricLSI.Statements.R20_Lemma_5_3

/-!
# Section 5 without symmetry: the permutation-average identity and Lemma 5.2

* `klDiv_bind_decomp`: for a probability `lam` on a finite discrete space `ι`, a Markov kernel
  `κ : ι → α` and a probability `Q` on `α`,
  `∫ H(κ i | Q) dlam = H(κ ∘ₘ lam | Q) + ∫ H(κ i | κ ∘ₘ lam) dlam`.
* `klDiv_permAvgAux`: for an arbitrary probability `ν` on `(𝕋^d)^N` and a permutation-invariant
  probability `Q`, `H(ν|Q) = H(ν̄|Q) + H(ν|ν̄)`, in `ℝ≥0∞` with no finiteness assumption.
* `reference_all_aux`: Lemma 5.2 (5.3)–(5.5) without symmetry.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

section Abstract

variable {α ι : Type*} [MeasurableSpace α] [MeasurableSpace ι]

theorem klDiv_map_swap {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] (M R : Measure (A × B))
    [IsFiniteMeasure M] [IsFiniteMeasure R] :
    klDiv (M.map Prod.swap) (R.map Prod.swap) = klDiv M R :=
  SharpLSI.klDiv_map_equiv' M R MeasurableEquiv.prodComm

/-- Compensation identity: the mean relative entropy of a family of laws `κ i` to `Q` splits into
the relative entropy of the mixture to `Q` and the mean relative entropy to the mixture. -/
theorem klDiv_bind_decomp [Countable ι] [MeasurableSingletonClass ι] [Nonempty ι]
    (lam : Measure ι) [IsProbabilityMeasure lam]
    (κ : Kernel ι α) [IsMarkovKernel κ] (Q : Measure α) [IsProbabilityMeasure Q] :
    ∫⁻ i, klDiv (κ i) Q ∂lam =
      klDiv (κ ∘ₘ lam) Q + ∫⁻ i, klDiv (κ i) (κ ∘ₘ lam) ∂lam := by
  set νb := κ ∘ₘ lam with hνb
  have : IsProbabilityMeasure νb := by
    rw [hνb]; infer_instance
  have h1 := klDiv_compProd_same_all lam κ (Kernel.const ι Q)
  have h2 := klDiv_compProd_same_all lam κ (Kernel.const ι νb)
  simp only [Kernel.const_apply] at h1 h2
  rw [← h1]
  set M := lam ⊗ₘ κ with hM
  set M' := M.map Prod.swap with hM'
  have hfst : M'.fst = νb := by
    rw [hM', Measure.fst_map_swap, hM, Measure.snd_compProd]
  have hdis : νb ⊗ₘ M'.condKernel = M' := by
    have := Measure.disintegrate M' M'.condKernel
    rwa [hfst] at this
  have hchain := klDiv_compProd_eq_add νb Q M'.condKernel (Kernel.const α lam)
  rw [hdis, Measure.compProd_const, Measure.compProd_const] at hchain
  have e1 : Q.prod lam = (lam.prod Q).map Prod.swap := (Measure.prod_swap).symm
  have e2 : νb.prod lam = (lam.prod νb).map Prod.swap := (Measure.prod_swap).symm
  have hrw : (lam ⊗ₘ Kernel.const ι Q) = lam.prod Q := Measure.compProd_const
  have hrw2 : (lam ⊗ₘ Kernel.const ι νb) = lam.prod νb := Measure.compProd_const
  rw [e1, e2, hM', klDiv_map_swap, klDiv_map_swap] at hchain
  rw [hrw, hchain, ← hrw2, h2]

end Abstract

section Perm

variable {d N : ℕ}

theorem permAvgAux_isProbabilityMeasure (ν : Measure (Config N d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (permAvgAux ν) := by
  constructor
  unfold permAvgAux
  have hmap : ∀ σ : Equiv.Perm (Fin N), ((ν.map (fun X : Config N d => X ∘ σ)) Set.univ) = 1 := fun σ => by
    change (ν.map (permEquiv (d := d) σ)) Set.univ = 1
    rw [Measure.map_apply (permEquiv (d := d) σ).measurable MeasurableSet.univ]
    simp
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, hmap, smul_eq_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by simp [Nat.factorial_ne_zero]) (by simp)

theorem permAvgAux_isSymmetric (ν : Measure (Config N d)) :
    SharpLSI.IsSymmetricMeasure (permAvgAux ν) := by
  intro τ
  ext s hs
  have hmσ : ∀ σ : Equiv.Perm (Fin N), Measurable fun X : Config N d => X ∘ σ := fun σ =>
    (permEquiv (d := d) σ).measurable
  unfold permAvgAux
  rw [Measure.map_apply (hmσ τ) hs]
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  have : ∀ σ : Equiv.Perm (Fin N),
      (ν.map (fun X : Config N d => X ∘ σ)) ((fun X : Config N d => X ∘ τ) ⁻¹' s) =
        ν.map (fun X : Config N d => X ∘ (σ * τ)) s := fun σ => by
    rw [Measure.map_apply (hmσ σ) ((hmσ τ) hs), Measure.map_apply (hmσ (σ * τ)) hs]
    rfl
  simp_rw [this]
  exact Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ => rfl

/-- **Permutation-average identity** (no finiteness assumption): for an arbitrary probability
`ν` on `(𝕋^d)^N` and a permutation-invariant probability `Q`,
`H(ν|Q) = H(ν̄|Q) + H(ν|ν̄)` where `ν̄ = permAvgAux ν`. -/
theorem klDiv_permAvgAux (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (Q : Measure (Config N d)) [IsProbabilityMeasure Q] (hQ : SharpLSI.IsSymmetricMeasure Q) :
    klDiv ν Q = klDiv (permAvgAux ν) Q + klDiv ν (permAvgAux ν) := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin N)) := ⊤
  have : MeasurableSingletonClass (Equiv.Perm (Fin N)) := ⟨fun _ => trivial⟩
  have : Nonempty (Equiv.Perm (Fin N)) := ⟨1⟩
  have := permAvgAux_isProbabilityMeasure ν
  set lam : Measure (Equiv.Perm (Fin N)) :=
    ((Nat.factorial N : ℝ≥0∞)⁻¹) • ∑ σ : Equiv.Perm (Fin N), Measure.dirac σ with hlam
  have : IsProbabilityMeasure lam := by
    constructor
    simp only [hlam, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul,
      MeasurableSet.univ, Measure.dirac_apply', Set.indicator_univ, Pi.one_apply, Finset.sum_const,
      Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by simp [Nat.factorial_ne_zero]) (by simp)
  let κ : Kernel (Equiv.Perm (Fin N)) (Config N d) :=
    Kernel.ofFunOfCountable fun σ => ν.map (fun X : Config N d => X ∘ σ)
  have hκ : ∀ σ, κ σ = ν.map (fun X : Config N d => X ∘ σ) := fun σ => rfl
  have : IsMarkovKernel κ := ⟨fun σ => by
    rw [hκ]
    exact (Measure.isProbabilityMeasure_map_iff (f := fun X : Config N d => X ∘ σ)
      (permEquiv (d := d) σ).measurable.aemeasurable).mpr ‹_›⟩
  have hbind : κ ∘ₘ lam = permAvgAux ν := by
    ext s hs
    rw [Measure.bind_apply hs κ.aemeasurable]
    simp only [hlam, lintegral_smul_measure, lintegral_finsetSum_measure,
      lintegral_dirac, hκ, permAvgAux, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      smul_eq_mul]
  have hdec := klDiv_bind_decomp lam κ Q
  rw [hbind] at hdec
  have hsymbar := permAvgAux_isSymmetric ν
  have hQ' : ∀ σ, klDiv (κ σ) Q = klDiv ν Q := fun σ => by
    rw [hκ]
    conv_lhs => rw [← hQ σ]
    exact SharpLSI.klDiv_map_equiv' ν Q (permEquiv (d := d) σ)
  have hsymbar' : ∀ σ, klDiv (κ σ) (permAvgAux ν) = klDiv ν (permAvgAux ν) := fun σ => by
    rw [hκ]
    conv_lhs => rw [← hsymbar σ]
    exact SharpLSI.klDiv_map_equiv' ν (permAvgAux ν) (permEquiv (d := d) σ)
  simpa only [hQ', hsymbar', lintegral_const, measure_univ, mul_one] using hdec

end Perm

section force
open Real
variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
variable (hyp : SharpLSI.Hyp V W KV KW)
include hyp

/-- **(5.14)** without symmetry, conditional on the (5.3)-type entropy bound `hR`. -/
theorem force_under_nu_nosym (hd : 1 ≤ d) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (C19 : ℝ)
    (hR : ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      klDiv ν (gibbs V W N) ≠ ⊤ →
        klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
          ENNReal.ofReal C19 * (klDiv ν (gibbs V W N) + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      klDiv ν (gibbs V W N) ≠ ⊤ →
        ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν ≤
          ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) := by
  set μm := (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  obtain ⟨a₀, CE, ha₀, hCE⟩ := force_exp_moment hd hyp hμ
  set CE' := max CE 1
  set L := Real.log CE'
  have hL0 : 0 ≤ L := Real.log_nonneg (le_max_right _ _)
  set C19' := max C19 0
  set C := (C19' + L + 1) / a₀
  have hC : 0 < C := by positivity
  refine ⟨C, hC, fun N hN ν hν hfin => ?_⟩
  set P := Measure.pi fun _ : Fin N => μm
  have hH := klDiv_pi_ne_top_of_gibbs hyp hμ hfin
  have hνP : ν ≪ P := (klDiv_ne_top_iff.mp hH).1
  -- the measurable bounded representative
  obtain ⟨CG, hCG0, hCG⟩ := exists_bound_gsG hyp hac (μ := μm) (N := N)
  set G : Config N d → ℝ := fun X => sqNorm (gsG W μm N (flat X))
  have hGm : Measurable G := by
    refine Finset.measurable_sum _ fun q _ => ?_
    exact ((measurable_gsG hyp hac q).comp measurable_flat).pow_const 2
  have hG0 : ∀ X, 0 ≤ G X := fun X => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set BG : ℝ := (Fintype.card (Fin N × Fin d) : ℝ) * CG ^ 2
  have hGB : ∀ X, |G X| ≤ BG := fun X => by
    rw [abs_of_nonneg (hG0 X)]
    calc G X ≤ ∑ _q : Fin N × Fin d, CG ^ 2 := Finset.sum_le_sum fun q _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hCG _ _) 2
      _ = BG := by simp [BG]
  have hae := gradSqC_Ucentered_ae hyp hμ hN
  -- Donsker–Varadhan
  have hgB : ∀ X, |a₀ * G X| ≤ a₀ * BG := fun X => by
    rw [abs_mul, abs_of_pos ha₀]; exact mul_le_mul_of_nonneg_left (hGB X) ha₀.le
  have hdv := dvFun_le_klDiv (ρ := ν) (ν := P) (hGm.const_mul a₀) hgB
  rw [← ENNReal.ofReal_toReal hH, EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]
    at hdv
  have hdv' := EReal.coe_le_coe_iff.mp hdv
  unfold dvFun at hdv'
  -- the exponential moment
  have hexp_int : Integrable (fun X => exp (a₀ * G X)) P :=
    Integrable.of_bound (measurable_exp.comp (hGm.const_mul a₀)).aestronglyMeasurable
      (exp (a₀ * BG)) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr ((le_abs_self _).trans (hgB X)))
  have hZ1 : 1 ≤ ∫ X, exp (a₀ * G X) ∂P := by
    have := integral_mono (integrable_const (1 : ℝ)) hexp_int fun X =>
      Real.one_le_exp (mul_nonneg ha₀.le (hG0 X))
    simpa using this
  have hZle : ∫ X, exp (a₀ * G X) ∂P ≤ CE' := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun X => (exp_pos _).le)
      hexp_int.aestronglyMeasurable]
    have h1 : ∫⁻ X, ENNReal.ofReal (exp (a₀ * G X)) ∂P =
        ∫⁻ X, ENNReal.ofReal (exp (a₀ * gradSqC (Ucentered W μ N) X)) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with X hX
      rw [hX]
    rw [h1]
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hCE N hN)
    rw [ENNReal.toReal_ofReal'] at h2
    exact h2.trans (max_le_max le_rfl zero_le_one)
  have hlogZ : Real.log (∫ X, exp (a₀ * G X) ∂P) ≤ L :=
    Real.log_le_log (by linarith) hZle
  -- `a₀ E_ν G ≤ H_0 + L`
  have hGν : a₀ * ∫ X, G X ∂ν ≤ (klDiv ν P).toReal + L := by
    rw [← integral_const_mul]; linarith
  -- (5.6)
  have h56 := hR N hN ν hν hfin
  have hH0 : (klDiv ν P).toReal ≤ C19' * ((klDiv ν (gibbs V W N)).toReal + 1) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.one_ne_top⟩)) h56
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_add hfin ENNReal.one_ne_top,
      ENNReal.toReal_one] at this
  -- conclusion
  have hGi : Integrable G ν := Integrable.of_bound hGm.aestronglyMeasurable BG
    (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hGB X)
  have hlin : ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν = ENNReal.ofReal (∫ X, G X ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hGi (Filter.Eventually.of_forall hG0)]
    refine lintegral_congr_ae ?_
    filter_upwards [hνP.ae_le hae] with X hX
    rw [hX]
  rw [hlin]
  set HP := (klDiv ν (gibbs V W N)).toReal
  have hHP : 0 ≤ HP := ENNReal.toReal_nonneg
  have hfinal : ∫ X, G X ∂ν ≤ C * (HP + 1) := by
    have : ∫ X, G X ∂ν ≤ ((klDiv ν P).toReal + L) / a₀ := by
      rw [le_div_iff₀ ha₀]; linarith
    refine this.trans ?_
    simp only [C]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ha₀]
    nlinarith [le_max_right C19 0]
  calc ENNReal.ofReal (∫ X, G X ∂ν) ≤ ENNReal.ofReal (C * (HP + 1)) := ENNReal.ofReal_le_ofReal hfinal
    _ = ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_add hHP zero_le_one, ENNReal.ofReal_one,
          ENNReal.ofReal_toReal hfin]

end force

section assembly

variable {d : ℕ}

/-- (5.3) without symmetry. -/
theorem reference_entropy_nosym {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : SharpLSI.Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
        ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) := by
  obtain ⟨C19, p, -, hR⟩ := SharpLSI.reference_entropy hd hyp hr hμ
  refine ⟨max C19 1, le_max_right _ _, fun N hN ν hν => ?_⟩
  set Q := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  have : IsProbabilityMeasure (gibbs V W N) := SharpLSI.gibbs_isProbabilityMeasure hyp N
  have hQsym : SharpLSI.IsSymmetricMeasure Q := fun σ => SharpLSI.pi_map_perm _ σ
  have hPsym : SharpLSI.IsSymmetricMeasure (gibbs V W N) := fun σ => SharpLSI.gibbs_map_perm hyp σ
  have hQ := klDiv_permAvgAux ν Q hQsym
  have hP := klDiv_permAvgAux ν (gibbs V W N) hPsym
  have := permAvgAux_isProbabilityMeasure ν
  have h56 := (hR N hN).1 (permAvgAux ν) inferInstance (permAvgAux_isSymmetric ν)
  set a := klDiv (permAvgAux ν) (gibbs V W N)
  set b := klDiv ν (permAvgAux ν)
  set c := ENNReal.ofReal (max C19 1)
  have hc1 : (1 : ℝ≥0∞) ≤ c := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hc2 : ENNReal.ofReal C19 ≤ c := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  rw [hQ, hP]
  calc klDiv (permAvgAux ν) Q + b ≤ ENNReal.ofReal C19 * (a + 1) + b := by gcongr
    _ ≤ c * (a + 1) + c * b := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hc1
    _ = c * (a + b + 1) := by ring

/-- **Lemma 5.2** (5.3)–(5.5) without symmetry (auxiliary form). -/
theorem reference_all_aux {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      klDiv ν (gibbs V W N) ≠ ⊤ →
        klDiv ν (Measure.pi fun _ => (μ : Measure (Torus d))) ≤
            ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) ∧
        ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν ≤
            ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) ∧
        (fisherInfoC ν (gibbs V W N) < ⊤ →
          fisherInfoC ν (Measure.pi fun _ => (μ : Measure (Torus d))) ≤
            2 * fisherInfoC ν (gibbs V W N) + ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1)) := by
  obtain ⟨C1, hC1, h1⟩ := reference_entropy_nosym hd hyp hr hμ
  obtain ⟨C2, hC2, h2⟩ := force_under_nu_nosym hyp hd hμ C1 fun N hN ν hν _ => h1 N hN ν hν
  refine ⟨max C1 (max C2 (2 * C2)), fun N hN ν hν hfin => ?_⟩
  have hC2' : C2 ≤ max C1 (max C2 (2 * C2)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC2'' : 2 * C2 ≤ max C1 (max C2 (2 * C2)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hC1' : C1 ≤ max C1 (max C2 (2 * C2)) := le_max_left _ _
  have e2 := h2 N hN ν hν hfin
  refine ⟨(h1 N hN ν hν).trans (by gcongr), e2.trans (by gcongr), fun _ => ?_⟩
  refine (SharpLSI.fisher_ref_le hyp hμ hN ν).trans (add_le_add le_rfl ?_)
  calc ENNReal.ofReal 2 * ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν
      ≤ ENNReal.ofReal 2 * (ENNReal.ofReal C2 * (klDiv ν (gibbs V W N) + 1)) := by gcongr
    _ = ENNReal.ofReal (2 * C2) * (klDiv ν (gibbs V W N) + 1) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal (max C1 (max C2 (2 * C2))) * (klDiv ν (gibbs V W N) + 1) := by
        gcongr

end assembly

end SharpLSI.FL
