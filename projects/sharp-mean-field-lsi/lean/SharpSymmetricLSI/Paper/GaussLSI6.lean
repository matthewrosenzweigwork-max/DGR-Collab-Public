import SharpSymmetricLSI.Paper.GaussLSI5
import SharpSymmetricLSI.Paper.EnergyParseval2
import SharpSymmetricLSI.Paper.AdmFinite
import SharpSymmetricLSI.Paper.AppAEvol2

/-!
# (8.13) (lane s42), step 4: `r_* ≤ λ_G`, and the assembled `gaussian_lsi`

For finitely supported `v` with `⟨v,Cv⟩ > 0`, the test densities `ρ_t = p(1+th)`
(Paper/GaussLSI4) are admissible for small `t ≠ 0`, `D(ρ_t) < ∞`, and the PL inequality
`2 r_* G(ρ_t) ≤ D(ρ_t)` (AppAEvol2 `rStar_mul_gap_le`) divided by `t²` passes to the limit:
`r_* ⟨v,Cv⟩ ≤ ∑ λ_{i+1} v_i²` (`G/t² → ½⟨v,Cv⟩`, `D/t² → ∫|∇v_fn|² dμ = ∑ λ_{i+1} v_i²`).
In `ℝ≥0∞` the limit also excludes `r_* = ∞`. Then `le_lamG_of_trunc` (Paper/LamSym3).
-/

noncomputable section
open MeasureTheory Filter Topology Finset

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `∇(∑ vᵢ eCᵢ₊₁) = ∑ vᵢ ∇eCᵢ₊₁`. -/
theorem cgrad_finsetSum {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
    (n : ℕ) (v : ℕ → ℝ) (x : Torus d) (k : Fin d) :
    cgrad (fun y => ∑ i ∈ range n, v i * eC (i + 1) y) x k =
      ∑ i ∈ range n, v i * cgrad (eC (i + 1)) x k := by
  unfold cgrad
  have e : (fun y => ∑ i ∈ range n, v i * eC (i + 1) y) ∘ liftT =
      fun z => ∑ i ∈ range n, v i * (eC (i + 1) ∘ liftT) z := rfl
  rw [e, fderiv_fun_sum fun i _ =>
    ((hφ (i + 1)).differentiable one_ne_zero (secT x)).const_mul (v i)]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_const_mul ((hφ (i + 1)).differentiable one_ne_zero (secT x))]
  rfl

/-- **`∫ |∇v_fn|² dμ = ∑_{i<n} λ_{i+1} vᵢ²`.** -/
theorem integral_cgrad_sq (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) {eC : ℕ → Torus d → ℝ}
    (heC : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT) ∧ eC j =ᵐ[haar d] e j) (n : ℕ) (v : ℕ → ℝ) :
    ∫ x, ∑ k, cgrad (fun y => ∑ i ∈ range n, v i * eC (i + 1) y) x k ^ 2
        ∂(μ : Measure (Torus d)) = ∑ i ∈ range n, lamShift lam i * v i ^ 2 := by
  set μm := (μ : Measure (Torus d))
  have hac : μm ≪ haar d := minimizer_ac hyp hμ
  have hwg : ∀ j, weakGrad (e j) =ᵐ[haar d] cgrad (eC j) := fun j =>
    weakGrad_ae_eq (appA_isWeakGrad_congr_ae (isWeakGrad_of_contDiff (heC j).1) (heC j).2)
  have hall : ∀ᵐ x ∂μm, ∀ j, weakGrad (e j) x = cgrad (eC j) x :=
    hac.ae_le (ae_all_iff.2 hwg)
  set a : ℕ → ℝ := fun j => if j = 0 then 0 else v (j - 1)
  set s := (range n).map (addRightEmbedding 1)
  have h := dirPair_eigsum hac he a s
  have hs : ∀ (F : ℕ → ℝ), ∑ j ∈ s, F j = ∑ i ∈ range n, F (i + 1) := fun F => by
    rw [Finset.sum_map]; rfl
  have ha : ∀ i, a (i + 1) = v i := fun i => by simp [a]
  simp only [hs, ha] at h
  show _ = ∑ i ∈ range n, lam (i + 1) * v i ^ 2
  rw [← h]
  unfold dirPair
  refine integral_congr_ae ?_
  filter_upwards [hall] with x hx
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cgrad_finsetSum (fun j => (heC j).1), sq]
  simp only [hx]

section main
variable (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
  {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
include hd hyp hr hμ he hC

/-- **(8.13) on finite vectors**: `r_* ≤ ∑ λ_{i+1} vᵢ² / ⟨v, C v⟩`. -/
theorem rStar_le_ratio (n : ℕ) (v : ℕ → ℝ)
    (hQ : 0 < ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j) :
    rStar V W ≤ ENNReal.ofReal (∑ i ∈ range n, lamShift lam i * v i ^ 2) /
      ENNReal.ofReal (∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j) := by
  set μm := (μ : Measure (Torus d))
  set Q := ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j
  set L := ∑ i ∈ range n, lamShift lam i * v i ^ 2
  obtain ⟨eC, heC⟩ := exists_c1_reps hd hyp hr hμ he
  obtain ⟨h, hc, hh0, hsum, hsv⟩ :=
    exists_test_pert hd hyp hr hμ he hC (fun j => ⟨(heC j).1, (heC j).2.2⟩) n v
  set g : Torus d → ℝ := fun x => ∑ i ∈ range n, v i * eC (i + 1) x
  have hg : ContDiff ℝ 1 (g ∘ liftT) := by
    have e : g ∘ liftT = fun z => ∑ i ∈ range n, v i * (eC (i + 1) ∘ liftT) z := rfl
    rw [e]
    exact ContDiff.sum fun i _ => contDiff_const.mul (heC (i + 1)).1
  obtain ⟨B, hB⟩ := exists_bound_of_continuous hc
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set p := elDens V W μm
  set G : ℝ → EReal := fun t => gap V W (densMeasure fun x => p x * (1 + t * h x))
  have hG := tendsto_gap_test hyp hμ hc hh0 hsv
  have hD := tendsto_diss_pert hyp hμ hc hg hB
  have hE : ∫ x, ∑ k, cgrad g x k ^ 2 ∂μm = L :=
    integral_cgrad_sq hyp hμ he (fun j => ⟨(heC j).1, (heC j).2.1⟩) n v
  rw [hE] at hD
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 ∧ |t| * (B + 2) ≤ 1 / 2 := by
    have : Tendsto (fun t : ℝ => |t| * (B + 2)) (𝓝 0) (𝓝 0) := by
      exact (continuous_abs.mul continuous_const : Continuous fun t : ℝ => |t| * (B + 2)).tendsto' 0 0
        (by simp)
    filter_upwards [nhdsWithin_le_nhds (this.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1 / 2))),
      self_mem_nhdsWithin] with t ht ht0
    exact ⟨ht0, ht⟩
  -- the PL inequality along `ρ_t`, divided by `t²`
  have hkey : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      rStar V W * ENNReal.ofReal (2 * ((G t).toReal / t ^ 2)) ≤
        ENNReal.ofReal (∫ x, dissInt W p h g t x ∂μm) := by
    filter_upwards [hsmall] with t ⟨ht0, ht⟩
    have ht' : |t| * B ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)).trans ht
    obtain ⟨h0, h1, -⟩ := pert_props hyp hμ hc.measurable hB hh0 ht'
    have hDeq := dissipation_pert hyp hμ hc hg hsum hB ht
    have hDne : dissipation V W (fun x => p x * (1 + t * h x)) ≠ ⊤ := by
      rw [hDeq]; exact ENNReal.ofReal_ne_top
    have hH1 : MemH1 (haar d) (fun x => Real.sqrt (p x * (1 + t * h x))) := by
      by_contra hn
      exact hDne (by unfold dissipation; rw [if_neg fun h => hn h.1])
    have hGt : G t ≠ ⊤ := (gap_lt_top_aux hyp h0 h1 hH1).1.ne
    have hPL := rStar_mul_gap_le (Eventually.of_forall h0) h1 hGt
    have hGe : (G t).toENNReal = ENNReal.ofReal (G t).toReal := by
      unfold EReal.toENNReal; rw [if_neg hGt]
    have ht2 : (0 : ℝ) < t ^ 2 := by positivity
    have e1 : ENNReal.ofReal (t ^ 2) * (rStar V W * ENNReal.ofReal (2 * ((G t).toReal / t ^ 2))) =
        2 * rStar V W * (G t).toENNReal := by
      rw [hGe, mul_left_comm, ← ENNReal.ofReal_mul ht2.le,
        show t ^ 2 * (2 * ((G t).toReal / t ^ 2)) = 2 * (G t).toReal by field_simp,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      ring
    have e2 : dissipation V W (fun x => p x * (1 + t * h x)) =
        ENNReal.ofReal (t ^ 2) * ENNReal.ofReal (∫ x, dissInt W p h g t x ∂μm) := by
      rw [hDeq, ENNReal.ofReal_mul ht2.le]
    have hne : ENNReal.ofReal (t ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr ht2).ne'
    refine (ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top).mp ?_
    rw [e1, ← e2]
    exact hPL
  -- limits
  have hQ0 : ENNReal.ofReal Q ≠ 0 := by simpa using hQ
  have hlimL : Tendsto (fun t => rStar V W * ENNReal.ofReal (2 * ((G t).toReal / t ^ 2)))
      (𝓝[≠] 0) (𝓝 (rStar V W * ENNReal.ofReal Q)) := by
    refine ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal ?_) (Or.inl hQ0)
    have := hG.const_mul 2
    rwa [show 2 * (Q / 2) = Q by ring] at this
  have hlimR : Tendsto (fun t => ENNReal.ofReal (∫ x, dissInt W p h g t x ∂μm)) (𝓝[≠] 0)
      (𝓝 (ENNReal.ofReal L)) :=
    ENNReal.tendsto_ofReal (hD.mono_left nhdsWithin_le_nhds)
  have hle := le_of_tendsto_of_tendsto hlimL hlimR hkey
  rwa [ENNReal.le_div_iff_mul_le (Or.inl hQ0) (Or.inl ENNReal.ofReal_ne_top)]

/-- **(8.13)**: `r_* ≤ λ_G`. -/
theorem rStar_le_lamG : rStar V W ≤ lamG (lamShift lam) C := by
  have h21 := prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS' := (hasSum_Tmat_sq hyp hμ he).summable
  have hCs : ∀ i j, C i j = C j i := fun i j => C_symm_of_secOp hT hS' hσ0 hσ hC i j
  have hnn := quadC_nonneg hT hS' hσ0 hσ hC
  have hup := quadC_le hT hS' hσ0 hσ hC
  have hcol : ∀ j, Summable fun k => C k j ^ 2 := fun j => (hC j).1
  have hlam0 : 0 < lamShift lam 0 := ((ref_spectrum hd hyp hr hμ).2 e lam he).1 1 le_rfl
  have hlam : ∀ i, 0 < lamShift lam i := fun i =>
    hlam0.trans_le (he.mono (by simp [lamShift] : 0 + 1 ≤ i + 1))
  exact le_lamG_of_trunc hσ0 hCs hnn hup hcol hlam fun n v hQ =>
    rStar_le_ratio hd hyp hr hμ he hC n v hQ

/-- **`gaussian_lsi` (R32) from Proposition 2.1's hypotheses**: (8.9), (8.10), (8.13). -/
theorem gaussian_lsi_of_prop21 {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) :
    0 < lamG (lamShift lam) C ∧ lamG (lamShift lam) C < ⊤ ∧
    (∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ →
      ent γ (fun z => f z ^ 2) ≤ 2 / lamG (lamShift lam) C * gaussForm (lamShift lam) γ f ∧
      var γ f ≤ gaussForm (lamShift lam) γ f / lamG (lamShift lam) C) ∧
    rStar V W ≤ lamG (lamShift lam) C := by
  obtain ⟨h1, h2, h3⟩ := gaussian_lsi_poincare_of_prop21 hd hyp hr hμ he hC hγ
  exact ⟨h1, h2, h3, rStar_le_lamG hd hyp hr hμ he hC⟩

end main

end SharpLSI
