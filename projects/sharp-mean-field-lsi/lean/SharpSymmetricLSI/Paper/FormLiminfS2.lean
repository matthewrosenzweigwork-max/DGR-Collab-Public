import SharpSymmetricLSI.Paper.FormLiminfS1
import SharpSymmetricLSI.Paper.GaussForm16

/-!
# (8.20), Gaussian side (lane s42): the `R → ∞` step, part 2 — row variables

For the kernel approximation `K_R`, the finite rows `∑_{q<n} kerMat(K_R)_{iq} z_q` approximate the
row variable `Y_i = (Tz)_i` in `L²(γ)` uniformly in `n` as `R → ∞` (`rowVar_approx`):
`E(∑_{q<n} w_q z_q)² = ⟨w, C w⟩ ≤ |w|²/σ` (`quadC_le`), and `∑_q w_q² ≤` the Hilbert–Schmidt
distance of Paper/FormLiminfS1.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- `∫ f² = (‖f‖₂)²` for `f ∈ L²`. -/
theorem integral_sq_eq_eLpNorm_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 ν) : ∫ x, f x ^ 2 ∂ν = (eLpNorm f 2 ν).toReal ^ 2 := by
  rw [← Lp.norm_toLp f hf, ← real_inner_self_eq_norm_sq, inner_toLp_gen]
  congr 1; funext x; ring

section approx
variable {μ : ProbabilityMeasure (Torus d)} (hyp : Hyp V W KV KW) (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  {KR : ℕ → Torus d → Torus d → ℝ} (hKR : IsKernelApprox W μ e KR)
include hyp hμ he hKR

set_option maxHeartbeats 1000000 in
/-- **The rows of `kerMat(K_R)` approximate the row variables uniformly in `n`.** -/
theorem rowVar_approx (h21 : Prop21Conclusion V W μ) {C : ℕ → ℕ → ℝ}
    (hC : IsInverseOfIPlus (Tmat W μ e) C) {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable (Tmat W μ e) γ i (Y i)) (i : ℕ) :
    Tendsto (fun R => limsup (fun n => ∫ z, (∑ q ∈ Finset.range n, kerMat (KR R) μ e i q * z q -
      Y i z) ^ 2 ∂γ) atTop) atTop (𝓝 0) := by
  have := hγ.1
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS' := (hasSum_Tmat_sq hyp hμ he).summable
  have hnn := quadC_nonneg hT hS' hσ0 hσ hC
  have hup := quadC_le hT hS' hσ0 hσ hC
  obtain ⟨hsum, hHS⟩ := kerMat_HS_tendsto hyp hμ he hKR
  set HS : ℕ → ℝ := fun R =>
    ∑' p : ℕ × ℕ, (kerMat (KR R) μ e p.1 p.2 - Tmat W μ e p.1 p.2) ^ 2
  set w : ℕ → ℕ → ℝ := fun R q => kerMat (KR R) μ e i q - Tmat W μ e i q
  -- the row is bounded by the Hilbert–Schmidt sum
  have hrow : ∀ R n, ∑ q ∈ range n, w R q ^ 2 ≤ HS R := fun R n => by
    set G : ℕ × ℕ → ℝ := fun p => (kerMat (KR R) μ e p.1 p.2 - Tmat W μ e p.1 p.2) ^ 2 with hG
    set ι : ℕ → ℕ × ℕ := fun q => (i, q) with hι
    have hinj : Function.Injective ι := fun a b h => (Prod.mk.inj h).2
    have hg0 : ∀ p, 0 ≤ G p := fun _ => sq_nonneg _
    have hGs : Summable G := hsum R
    have hrs : Summable (G ∘ ι) := hGs.comp_injective hinj
    have hw : ∀ q, w R q ^ 2 = (G ∘ ι) q := fun q => rfl
    have h1 : ∑ q ∈ range n, (G ∘ ι) q ≤ ∑' q, (G ∘ ι) q :=
      hrs.sum_le_tsum _ fun q _ => hg0 (ι q)
    have h2 : ∑' q, (G ∘ ι) q ≤ ∑' p, G p := tsum_comp_le_tsum_of_inj hGs hg0 hinj
    simp only [hw]
    exact h1.trans h2
  -- the row-variable error
  obtain ⟨hYm, hYt⟩ := hY i
  set b : ℕ → (ℕ → ℝ) → ℝ := fun n z => (∑ q ∈ range n, Tmat W μ e i q * z q) - Y i z
  have hbm : ∀ n, MemLp (b n) 2 γ := fun n => (memLp_linSum_gamma hγ (range n) _).sub hYm
  have hb : Tendsto (fun n => ∫ z, b n z ^ 2 ∂γ) atTop (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hYt
    have h2 := h1.pow 2
    simp only [Function.comp_def, ENNReal.toReal_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at h2
    exact h2.congr fun n => (integral_sq_eq_eLpNorm_sq (hbm n)).symm
  -- the bound for each `R, n`
  set f : ℕ → ℕ → ℝ := fun R n =>
    ∫ z, (∑ q ∈ range n, kerMat (KR R) μ e i q * z q - Y i z) ^ 2 ∂γ
  have hf0 : ∀ R n, 0 ≤ f R n := fun R n => integral_nonneg fun _ => sq_nonneg _
  have hfle : ∀ R n, f R n ≤ 2 * HS R / σ + 2 * ∫ z, b n z ^ 2 ∂γ := fun R n => by
    have hA := memLp_linSum_gamma hγ (range n) (w R)
    have hsplit : ∀ z, ∑ q ∈ range n, kerMat (KR R) μ e i q * z q - Y i z =
        ∑ q ∈ range n, w R q * z q + b n z := fun z => by
      simp only [w, b, sub_mul, Finset.sum_sub_distrib]; ring
    have hi1 : Integrable (fun z => (∑ q ∈ range n, w R q * z q + b n z) ^ 2) γ :=
      (hA.add (hbm n)).integrable_sq
    have hi2 : Integrable (fun z => 2 * (∑ q ∈ range n, w R q * z q) ^ 2 + 2 * b n z ^ 2) γ :=
      (hA.integrable_sq.const_mul 2).add ((hbm n).integrable_sq.const_mul 2)
    calc f R n = ∫ z, (∑ q ∈ range n, w R q * z q + b n z) ^ 2 ∂γ := by
          simp only [f]; congr 1; funext z; rw [hsplit]
      _ ≤ ∫ z, 2 * (∑ q ∈ range n, w R q * z q) ^ 2 + 2 * b n z ^ 2 ∂γ :=
          integral_mono hi1 hi2 fun z => by
            nlinarith [sq_nonneg (∑ q ∈ range n, w R q * z q - b n z)]
      _ = 2 * (∑ q ∈ range n, ∑ q' ∈ range n, w R q * C q q' * w R q') +
            2 * ∫ z, b n z ^ 2 ∂γ := by
          rw [integral_add (hA.integrable_sq.const_mul 2) ((hbm n).integrable_sq.const_mul 2),
            integral_const_mul, integral_const_mul,
            integral_linSum_sq_gamma hγ (range n) (w R) (hnn _ _)]
      _ ≤ 2 * HS R / σ + 2 * ∫ z, b n z ^ 2 ∂γ := by
          have h1 := hup (range n) (w R)
          have h2 : (∑ q ∈ range n, w R q ^ 2) / σ ≤ HS R / σ :=
            div_le_div_of_nonneg_right (hrow R n) hσ0.le
          have : 2 * (∑ q ∈ range n, ∑ q' ∈ range n, w R q * C q q' * w R q') ≤ 2 * HS R / σ := by
            rw [mul_div_assoc]; linarith
          linarith
  -- `limsup_n`
  have hlim : ∀ R, 0 ≤ limsup (f R) atTop ∧ limsup (f R) atTop ≤ 2 * HS R / σ := fun R => by
    have hg : Tendsto (fun n => 2 * HS R / σ + 2 * ∫ z, b n z ^ 2 ∂γ) atTop
        (𝓝 (2 * HS R / σ)) := by
      simpa using tendsto_const_nhds.add (hb.const_mul 2)
    have hbdd : IsBoundedUnder (· ≤ ·) atTop (f R) :=
      hg.isBoundedUnder_le.mono_le (Eventually.of_forall (hfle R))
    have hcob : IsCoboundedUnder (· ≤ ·) atTop (f R) :=
      isCoboundedUnder_le_of_le atTop (hf0 R)
    refine ⟨le_limsup_of_frequently_le (Frequently.of_forall (hf0 R)) hbdd, ?_⟩
    rw [← hg.limsup_eq]
    exact limsup_le_limsup (Eventually.of_forall (hfle R)) hcob hg.isBoundedUnder_le
  have hHS0 : Tendsto (fun R => 2 * HS R / σ) atTop (𝓝 0) := by
    simpa using (hHS.const_mul 2).div_const σ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hHS0
    (fun R => (hlim R).1) fun R => (hlim R).2

end approx

end SharpLSI
