import SharpSymmetricLSI.Paper.ForceApprox12
import SharpSymmetricLSI.Paper.ForceApprox6
import SharpSymmetricLSI.Paper.ForceApprox7

/-!
# R31: (7.12), conditional on the uniform `L^p` bound of the centered density (Lemma 5.2)

`E_{P_N}|∇(U_N - U_N^{(R)})|² ≤ ‖p_N‖_{L^p} (E_{μ^N}|∇(U_N - U_N^{(R)})|²)^{1/(2q)} C`, with the
exponential moment of Section 7 for the constant, and `(7.11)` with `A_R → 0` for the middle factor.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem integrable_forceSum {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {n : ℕ}
    {c : Torus d → Torus d → Fin d → ℝ} {cΔ : Torus d → Fin d → ℝ}
    (hcm : ∀ k, Measurable (Function.uncurry fun x y => c x y k))
    (hΔm : ∀ k, Measurable fun x => cΔ x k) {M : ℝ}
    (hcb : ∀ x y k, |c x y k| ≤ M) (hΔb : ∀ x k, |cΔ x k| ≤ M) :
    Integrable (fun X : Fin (n + 1) → Torus d => ∑ i, ∑ k, ((((n + 1 : ℕ) : ℝ))⁻¹ *
        (∑ l ∈ Finset.univ.erase i, c (X i) (X l) k + cΔ (X i) k)) ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => ?_
  refine integrable_of_bdd (C := ((n + 1) * M) ^ 2) ?_ fun X => ?_
  · refine (measurable_const.mul ((Finset.measurable_sum _ fun l _ => ?_).add ((hΔm k).comp
        (measurable_pi_apply i)))).pow_const 2
    exact (hcm k).comp (by fun_prop : Measurable fun X : Fin (n + 1) → Torus d => (X i, X l))
  · rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [abs_mul, abs_of_pos (by positivity)]
    have hM : 0 ≤ M := (abs_nonneg _).trans (hΔb (X i) k)
    have hS : |∑ l ∈ Finset.univ.erase i, c (X i) (X l) k + cΔ (X i) k| ≤ (n + 1) * M := by
      refine (abs_add_le _ _).trans ?_
      refine (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (g := fun _ => M) fun l _ => hcb _ _ k)) (hΔb _ k)).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
      push_cast; nlinarith
    have h1 : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by push_cast; linarith)
    calc _ ≤ 1 * ((n + 1) * M) := mul_le_mul h1 hS (abs_nonneg _) zero_le_one
      _ = _ := one_mul _

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {KR : ℕ → Torus d → Torus d → ℝ}
  {eC : ℕ → Torus d → ℝ}
  (heC : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT) ∧ eC j =ᵐ[haar d] e j ∧
    eC j =ᵐ[(μ : Measure (Torus d))] e j)
  {s : ℕ → Finset ℕ} {a : ℕ → ℕ → ℕ → ℝ} (ha : ∀ R i j, a R i j = a R j i)
  (hK : ∀ R x y, KR R x y = ∑ i ∈ s R, ∑ j ∈ s R, a R i j * e (i + 1) x * e (j + 1) y)
include hyp hμ heC ha hK

/-- Uniform-in-`R` constants for `c_R`, `c_{Δ,R}`. -/
theorem uniform_cOff (hKR : IsKernelApprox W μ e KR) {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ R,
      (∀ k, Measurable (Function.uncurry fun x y =>
        cOff W μ (fun i => eC (i + 1)) (s R) (a R) x y k)) ∧
      (∀ k, Measurable fun x => cDiag W μ (fun i => eC (i + 1)) (s R) (a R) x k) ∧
      (∀ x y k, |cOff W μ (fun i => eC (i + 1)) (s R) (a R) x y k| ≤ M) ∧
      (∀ x k, |cDiag W μ (fun i => eC (i + 1)) (s R) (a R) x k| ≤ M) ∧
      (∀ x k, ∫ y, cOff W μ (fun i => eC (i + 1)) (s R) (a R) x y k
        ∂(μ : Measure (Torus d)) = 0) := by
  obtain ⟨C0, hC0, hc⟩ := cOff_props hyp hμ
  obtain ⟨B, hB⟩ := finKerD_uniform_bound hyp hμ heC ha hK hKR
  have hφ : ∀ i, ContDiff ℝ 1 ((fun i => eC (i + 1)) i ∘ liftT) := fun i => (heC (i + 1)).1
  have hφ0 : ∀ j, ∫ y, (fun i => eC (i + 1)) j y ∂(μ : Measure (Torus d)) = 0 := fun j => by
    rw [integral_congr_ae (heC (j + 1)).2.2]
    have := he.orthonormal (j + 1) 0
    simp only [he.zero, mul_one, Nat.add_one_ne_zero, ↓reduceIte] at this
    exact this
  refine ⟨C0 + max B 0, by positivity, fun R => ?_⟩
  exact hc hφ hφ0 (s R) (a R) (CK := max B 0) fun x y k => (hB R x y k).trans (le_max_left _ _)

/-- `A_R → 0` as a Bochner integral. -/
theorem tendsto_cOff_integral (hKR : IsKernelApprox W μ e KR) {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    Tendsto (fun R => ∫ x, ∫ y, ∑ k, cOff W μ (fun i => eC (i + 1)) (s R) (a R) x y k ^ 2
      ∂(μ : Measure (Torus d)) ∂(μ : Measure (Torus d))) atTop (𝓝 0) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨M, hM0, hU⟩ := uniform_cOff hyp hμ heC ha hK hKR he
  have hL := tendsto_cOff_sq hyp hμ heC ha hK hKR
  have heq : ∀ R, ∫ x, ∫ y, ∑ k, cOff W μ (fun i => eC (i + 1)) (s R) (a R) x y k ^ 2 ∂μm ∂μm =
      (∫⁻ X, ENNReal.ofReal (∑ k, cOff W μ (fun i => eC (i + 1)) (s R) (a R) (X 0) (X 1) k ^ 2)
        ∂Measure.pi (fun _ : Fin 2 => μm)).toReal := fun R => by
    obtain ⟨hcm, -, hcb, -, -⟩ := hU R
    have hm : Measurable fun p : Torus d × Torus d =>
        ∑ k, cOff W μ (fun i => eC (i + 1)) (s R) (a R) p.1 p.2 k ^ 2 :=
      Finset.measurable_sum _ fun k _ => (hcm k).pow_const 2
    have hint : Integrable (fun p : Torus d × Torus d =>
        ∑ k, cOff W μ (fun i => eC (i + 1)) (s R) (a R) p.1 p.2 k ^ 2) (μm.prod μm) :=
      integrable_finsetSum _ fun k _ => integrable_of_bdd ((hcm k).pow_const 2) (C := M ^ 2)
        fun p => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hcb _ _ k) 2
    rw [← integral_prod _ hint]
    have hmp := measurePreserving_finTwoArrow μm
    rw [← hmp.integral_comp' (fun p : Torus d × Torus d =>
        ∑ k, cOff W μ (fun i => eC (i + 1)) (s R) (a R) p.1 p.2 k ^ 2)]
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun X =>
        Finset.sum_nonneg fun k _ => sq_nonneg _) (hm.comp hmp.measurable).aestronglyMeasurable]
    rfl
  refine Tendsto.congr (fun R => (heq R).symm) ?_
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL
  rw [ENNReal.toReal_zero] at this
  exact this

/-- **(7.12)**, given the uniform `L^p` bound of the centered density. -/
theorem force_limit_of (hd : 1 ≤ d) (hKR : IsKernelApprox W μ e KR) {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hpart : ∃ C p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (rexp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C) :
    Tendsto (fun R => limsup (fun N => ∫⁻ X, ENNReal.ofReal
        (gradSqC (fun Y => Ucentered W μ N Y - UkernelF (KR R) N Y) X) ∂gibbs V W N) atTop)
      atTop (𝓝 0) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨C, p, hp1, hC⟩ := hpart
  set q := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  obtain ⟨M, hM0, hU⟩ := uniform_cOff hyp hμ heC ha hK hKR he
  obtain ⟨a₀, ha₀def⟩ : ∃ a₀ : ℝ, a₀ = 1 / (8 * d * (M ^ 2 + 1)) := ⟨_, rfl⟩
  have ha₀ : 0 < a₀ := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [ha₀def]; positivity
  obtain ⟨E, hE⟩ : ∃ E : ℝ≥0∞, E = ENNReal.ofReal (rexp (2 * a₀ * d * M ^ 2) *
    gaussSqConst.toReal) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0∞, D =
    (ENNReal.ofReal (((2 * q - 1) / a₀) ^ (2 * q - 1)) * E) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ : ∃ Cp : ℝ≥0∞, Cp = (ENNReal.ofReal C) ^ (1 / p) := ⟨_, rfl⟩
  have hDtop : D ≠ ⊤ := by
    rw [hD, hE]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hCptop : Cp ≠ ⊤ := by
    rw [hCp]; exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ≥0∞,
      h = fun t => Cp * ((ENNReal.ofReal t) ^ (1 / 2 : ℝ) * D) ^ (1 / q) := ⟨_, rfl⟩
  have hmono : ∀ t t', t ≤ t' → h t ≤ h t' := fun t t' htt => by
    rw [hh]
    beta_reduce
    gcongr
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, A = fun R => ∫ x, ∫ y,
      ∑ k, cOff W μ (fun i => eC (i + 1)) (s R) (a R) x y k ^ 2 ∂μm ∂μm := ⟨_, rfl⟩
  -- the bound for fixed `N = n+1` and `R`
  have hbound : ∀ R n : ℕ, ∫⁻ X, ENNReal.ofReal (gradSqC (fun Y => Ucentered W μ (n + 1) Y -
      UkernelF (KR R) (n + 1) Y) X) ∂gibbs V W (n + 1) ≤ h (A R + d * M ^ 2 / (n + 1)) := by
    intro R n
    obtain ⟨hcm, hΔm, hcb, hΔb, hcent⟩ := hU R
    have hφ : ∀ i, ContDiff ℝ 1 ((fun i => eC (i + 1)) i ∘ liftT) := fun i => (heC (i + 1)).1
    have hKRae := Ukernel_ae_finKer (fun j => (heC j).2.1) (s R) (a R) (hK R) (n + 1)
    have hgrad := weakGradC_diff_ae hyp hμ hφ (s R) (ha R) (by omega : 1 ≤ n + 1) hKRae
    obtain ⟨G, hG⟩ : ∃ G : (Fin (n + 1) → Torus d) → ℝ, G = fun X => ∑ i, ∑ k,
        ((((n + 1 : ℕ) : ℝ))⁻¹ * (∑ l ∈ Finset.univ.erase i,
          cOff W μm (fun i => eC (i + 1)) (s R) (a R) (X i) (X l) k +
          cDiag W μm (fun i => eC (i + 1)) (s R) (a R) (X i) k)) ^ 2 := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : (Fin (n + 1) → Torus d) → ℝ,
        w = fun X => rexp (-Ucentered W μm (n + 1) X) / centeredPartition W μm (n + 1) :=
      ⟨_, rfl⟩
    have hGint : Integrable G (Measure.pi fun _ : Fin (n + 1) => μm) := by
      rw [hG]; exact integrable_forceSum hcm hΔm hcb hΔb
    have hG0 : ∀ X, 0 ≤ G X := fun X => by
      rw [hG]; exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
    have hKpos := centeredPartition_pos hyp μm (n + 1)
    have hw0 : ∀ X, 0 ≤ w X := fun X => by rw [hw]; exact div_nonneg (exp_pos _).le hKpos.le
    have hwm : Measurable w := by
      rw [hw]; exact ((measurable_Ucentered hyp μm (n + 1)).neg.exp).div_const _
    rw [lintegral_gibbs_eq hyp hμ]
    have step1 : ∫⁻ X, ENNReal.ofReal (rexp (-Ucentered W μm (n + 1) X) /
        centeredPartition W μm (n + 1)) * ENNReal.ofReal (gradSqC (fun Y => Ucentered W μ (n + 1) Y -
          UkernelF (KR R) (n + 1) Y) X) ∂Measure.pi (fun _ : Fin (n + 1) => μm) =
        ∫⁻ X, ENNReal.ofReal (w X * G X) ∂Measure.pi (fun _ : Fin (n + 1) => μm) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hgrad] with X hX
      rw [← ENNReal.ofReal_mul (by rw [hw] at hw0; exact hw0 X), hw, hG]
      congr 2
      unfold gradSqC
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hX i k]
    rw [step1]
    refine (lintegral_mul_le_moments hw0 hG0 hwm.aemeasurable hGint.aemeasurable hpq ha₀).trans ?_
    -- the three factors
    obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μm (n + 1)
    have hwb : ∀ X, w X ≤ rexp BU / centeredPartition W μm (n + 1) := fun X => by
      rw [hw]
      refine div_le_div_of_nonneg_right (exp_le_exp.2 ?_) hKpos.le
      have := hBU X; rw [abs_le] at this; linarith
    have hwp : ∫⁻ X, ENNReal.ofReal (w X ^ p) ∂Measure.pi (fun _ : Fin (n + 1) => μm) ≤
        ENNReal.ofReal C := by
      have hint : Integrable (fun X => w X ^ p) (Measure.pi fun _ : Fin (n + 1) => μm) :=
        integrable_of_bdd (hwm.pow_const p)
          (C := (rexp BU / centeredPartition W μm (n + 1)) ^ p) fun X => by
            rw [abs_of_nonneg (rpow_nonneg (hw0 X) _)]
            exact rpow_le_rpow (hw0 X) (hwb X) hp0.le
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun X => rpow_nonneg (hw0 X) _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hC (n + 1) (by omega)
      rw [hw]; exact this
    have hGl : ∫⁻ X, ENNReal.ofReal (G X) ∂Measure.pi (fun _ : Fin (n + 1) => μm) ≤
        ENNReal.ofReal (A R + d * M ^ 2 / (n + 1)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hGint (Eventually.of_forall hG0), hG,
        integral_forceSum_sq hcm hΔm hcb hΔb (fun k => Eventually.of_forall fun x => hcent x k)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hA0 : 0 ≤ A R := by
        rw [hA]; exact integral_nonneg fun x => integral_nonneg fun y =>
          Finset.sum_nonneg fun k _ => sq_nonneg _
      have hB : ∫ x, ∑ k, cDiag W μm (fun i => eC (i + 1)) (s R) (a R) x k ^ 2 ∂μm ≤
          d * M ^ 2 := by
        have hpt : ∀ x, ∑ k, cDiag W μm (fun i => eC (i + 1)) (s R) (a R) x k ^ 2 ≤
            d * M ^ 2 := fun x => by
          calc ∑ k, cDiag W μm (fun i => eC (i + 1)) (s R) (a R) x k ^ 2 ≤
              ∑ _k : Fin d, M ^ 2 := Finset.sum_le_sum fun k _ => by
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hΔb x k) 2
            _ = d * M ^ 2 := by simp
        calc _ ≤ ∫ _x, (d * M ^ 2 : ℝ) ∂μm :=
              integral_mono_of_nonneg (Eventually.of_forall fun x =>
                Finset.sum_nonneg fun k _ => sq_nonneg _) (integrable_const _)
                (Eventually.of_forall hpt)
          _ = d * M ^ 2 := by simp
      have hn : (0 : ℝ) < n + 1 := by positivity
      have h1 : (n : ℝ) / (n + 1) ≤ 1 := by rw [div_le_one hn]; linarith
      have hAe : ∫ x, ∫ y, ∑ k, cOff W μm (fun i => eC (i + 1)) (s R) (a R) x y k ^ 2 ∂μm ∂μm =
          A R := by rw [hA]
      rw [hAe]
      push_cast
      calc (n : ℝ) / (n + 1) * A R +
            ((n : ℝ) + 1)⁻¹ * ∫ x, ∑ k, cDiag W μm (fun i => eC (i + 1)) (s R) (a R) x k ^ 2 ∂μm
          ≤ 1 * A R + ((n : ℝ) + 1)⁻¹ * (d * M ^ 2) := by gcongr
        _ = A R + d * M ^ 2 / (n + 1) := by rw [one_mul, div_eq_inv_mul]
    have hexp := exp_moment_forceSum hd (μ := μm) n hcm hcb hΔb (fun x k => hcent x k)
    rw [← ha₀def, ← hE] at hexp
    rw [hh, hCp, hD]
    beta_reduce
    gcongr
    rw [hG]; beta_reduce; exact hexp
  -- the limsup in `N`
  have hls : ∀ R : ℕ, limsup (fun N => ∫⁻ X, ENNReal.ofReal
      (gradSqC (fun Y => Ucentered W μ N Y - UkernelF (KR R) N Y) X) ∂gibbs V W N) atTop ≤
        h (A R + 1 / ((R : ℝ) + 1)) := by
    intro R
    refine limsup_le_of_le (by isBoundedDefault) ?_
    refine eventually_atTop.2 ⟨⌈(d : ℝ) * M ^ 2 * ((R : ℝ) + 1)⌉₊ + 1, fun N hN => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    refine (hbound R n).trans (hmono _ _ ?_)
    have hc : (d : ℝ) * M ^ 2 * ((R : ℝ) + 1) ≤ n + 1 := by
      have h1 := Nat.le_ceil ((d : ℝ) * M ^ 2 * ((R : ℝ) + 1))
      have h2 : ((⌈(d : ℝ) * M ^ 2 * ((R : ℝ) + 1)⌉₊ : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (by omega : ⌈(d : ℝ) * M ^ 2 * ((R : ℝ) + 1)⌉₊ ≤ n)
      linarith
    have : (d : ℝ) * M ^ 2 / (n + 1) ≤ 1 / ((R : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    linarith
  -- the limit in `R`
  have htA := tendsto_cOff_integral hyp hμ heC ha hK hKR he
  rw [← hA] at htA
  have ht : Tendsto (fun R : ℕ => A R + 1 / ((R : ℝ) + 1)) atTop (𝓝 0) := by
    simpa using htA.add tendsto_one_div_add_atTop_nhds_zero_nat
  have h0 : h 0 = 0 := by
    rw [hh]
    simp only [ENNReal.ofReal_zero]
    rw [ENNReal.zero_rpow_of_pos (by norm_num), zero_mul,
      ENNReal.zero_rpow_of_pos (by positivity), mul_zero]
  have hc : Tendsto h (𝓝 0) (𝓝 (h 0)) := by
    rw [hh]
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr hCptop)
    refine (ENNReal.continuous_rpow_const.tendsto _).comp ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hDtop)
    exact (ENNReal.continuous_rpow_const.tendsto _).comp (ENNReal.continuous_ofReal.tendsto 0)
  rw [h0] at hc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hc.comp ht)
    (fun _ => bot_le) hls

end

/-- (7.12), with the `C¹` representatives and the finite-rank data of `K_R` chosen. -/
theorem force_limit_of' (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {KR : ℕ → Torus d → Torus d → ℝ} (hKR : IsKernelApprox W μ e KR)
    (hpart : ∃ C p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (rexp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C) :
    Tendsto (fun R => limsup (fun N => ∫⁻ X, ENNReal.ofReal
        (gradSqC (fun Y => Ucentered W μ N Y - UkernelF (KR R) N Y) X) ∂gibbs V W N) atTop)
      atTop (𝓝 0) := by
  obtain ⟨eC, heC⟩ := exists_c1_reps hd hyp hr hμ he
  choose s a ha hK using hKR.1
  exact force_limit_of hyp hμ heC ha hK hd hKR he hpart

end SharpLSI
