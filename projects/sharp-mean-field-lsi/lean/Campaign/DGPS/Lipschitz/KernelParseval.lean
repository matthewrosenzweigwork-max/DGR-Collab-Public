import DGPS.Lipschitz.VolterraGradient
import DGPS.Lipschitz.WeightedSpectrum
import DGPS.Lipschitz.EigenfunctionC1
import DGPS.Lipschitz.Representatives
import DGPS.Lipschitz.SemigroupEigen

/-!
# Product form Parseval (LIP011, part I)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

/-- Spectral data on a weighted torus: an orthonormal eigenbasis of `L²(w m)` with continuous
representatives and the form expansion. -/
structure Spec (d : ℕ) where
  w : Torus d → ℝ
  c : ℝ
  C : ℝ
  meas : Measurable w
  pos : 0 < c
  bound : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C
  prob : ∫ x, w x ∂haar d = 1
  e : HilbertBasis ℕ ℝ (Hw d w)
  lam : ℕ → ℝ
  lam_nonneg : ∀ j, 0 ≤ lam j
  v : ℕ → Torus d → ℝ
  vc : ∀ i, Continuous (v i)
  ve : ∀ i, v i =ᵐ[haar d] ((e i : Hw d w) : Torus d → ℝ)
  form : ∀ (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
    HasSum (fun j => lam j * ⟪e j, f⟫_ℝ ^ 2) (weightedForm w Y Y)

/-- The measure `μ = w m`. -/
noncomputable abbrev Spec.mu (S : Spec d) : Measure (Torus d) := wMeasure d S.w

instance Spec.instFinite (S : Spec d) : IsFiniteMeasure S.mu :=
  WeightedGenerator.isFiniteMeasure_wMeasure S.bound

instance Spec.instOpenPos (S : Spec d) : S.mu.IsOpenPosMeasure :=
  (haar_ac_wMeasure S.pos S.bound).isOpenPosMeasure

theorem Spec.ae_haar (S : Spec d) {P : Torus d → Prop} (h : ∀ᵐ x ∂S.mu, P x) :
    ∀ᵐ x ∂haar d, P x := (haar_ac_wMeasure S.pos S.bound).ae_le h

theorem Spec.ae_mu (S : Spec d) {P : Torus d → Prop} (h : ∀ᵐ x ∂haar d, P x) :
    ∀ᵐ x ∂S.mu, P x := wMeasure_ac_haar.ae_le h

theorem Spec.integral_mu (S : Spec d) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Torus d → E) : ∫ x, φ x ∂S.mu = ∫ x, S.w x • φ x ∂haar d :=
  integral_wMeasure S.meas S.pos S.bound φ

theorem Spec.memLp_mu (S : Spec d) {f : Torus d → ℝ} (hf : Continuous f) :
    MemLp f 2 S.mu :=
  hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem Spec.hasSum_sq (S : Spec d) {g : Torus d → ℝ} (hg : MemLp g 2 S.mu) :
    HasSum (fun i => (∫ x, g x * S.v i x ∂S.mu) ^ 2) (∫ x, g x ^ 2 ∂S.mu) := by
  have h := S.e.hasSum_inner_mul_inner (hg.toLp g) (hg.toLp g)
  have hi : ∀ i, ⟪hg.toLp g, S.e i⟫_ℝ = ∫ x, g x * S.v i x ∂S.mu := fun i => by
    rw [real_inner_comm, inner_Hw_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp, S.ae_mu (S.ve i)] with x h1 h2
    rw [h1, ← h2, mul_comm]
  have h2 : ⟪hg.toLp g, hg.toLp g⟫_ℝ = ∫ x, g x ^ 2 ∂S.mu := by
    rw [inner_Hw_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with x h1
    rw [h1, sq]
  rw [h2] at h
  convert h using 2 with i
  rw [sq, hi i, real_inner_comm, hi i]

theorem Spec.coeff_eq (S : Spec d) {g : Torus d → ℝ} (hg : MemLp g 2 S.mu) (i : ℕ) :
    ⟪S.e i, hg.toLp g⟫_ℝ = ∫ x, g x * S.v i x ∂S.mu := by
  rw [inner_Hw_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp, S.ae_mu (S.ve i)] with x h1 h2
  rw [h1, ← h2, mul_comm]

/-- Weighted scalar Parseval: `Σ (1+λ_i) ⟨f,e_i⟩² = ‖f‖² + ‖∇f‖²` in `L²(μ)`. -/
theorem Spec.hasSum_weighted (S : Spec d) {f : Torus d → ℝ} (hf : MemLp f 2 S.mu)
    {Y : Torus d → Tangent d} (hY : IsWeakGradient f Y) :
    HasSum (fun i => (1 + S.lam i) * (∫ x, f x * S.v i x ∂S.mu) ^ 2)
      (∫ x, f x ^ 2 ∂S.mu + weightedForm S.w Y Y) := by
  have h1 := S.hasSum_sq hf
  have hY' : IsWeakGradient ((hf.toLp f : Hw d S.w) : Torus d → ℝ) Y :=
    hY.congr_ae (S.ae_haar hf.coeFn_toLp.symm) (Filter.EventuallyEq.refl _ _)
  have h2 := S.form (hf.toLp f) Y hY'
  have h3 : HasSum (fun i => (∫ x, f x * S.v i x ∂S.mu) ^ 2 +
      S.lam i * (∫ x, f x * S.v i x ∂S.mu) ^ 2) _ := h1.add (by
    simpa only [S.coeff_eq hf] using h2)
  simpa only [add_mul, one_mul] using h3

/-! ### Exchange of sum and integral for nonnegative terms -/

theorem hasSum_integral_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F : α → ℝ} (hint : ∀ i, Integrable (f i) μ) (h0 : ∀ i x, 0 ≤ f i x)
    (hs : ∀ x, HasSum (fun i => f i x) (F x)) (hF : Integrable F μ) :
    HasSum (fun i => ∫ x, f i x ∂μ) (∫ x, F x ∂μ) := by
  have hle : ∀ s : Finset ℕ, ∑ i ∈ s, ∫ x, f i x ∂μ ≤ ∫ x, F x ∂μ := by
    intro s
    rw [← integral_finsetSum _ (fun i _ => hint i)]
    refine integral_mono (integrable_finsetSum _ fun i _ => hint i) hF fun x => ?_
    exact sum_le_hasSum s (fun i _ => h0 i x) (hs x)
  have hsum : Summable (fun i => ∫ x, f i x ∂μ) :=
    summable_of_sum_le (fun i => integral_nonneg (h0 i)) hle
  have hn : Summable (fun i => ∫ x, ‖f i x‖ ∂μ) := by
    refine hsum.congr fun i => integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [Real.norm_eq_abs, abs_of_nonneg (h0 i x)]
  have := hasSum_integral_of_summable_integral_norm hint hn
  convert this using 1
  exact integral_congr_ae (Eventually.of_forall fun x => ((hs x).tsum_eq).symm)

/-! ### Kernel data -/

/-- A continuous kernel on `𝕋^d × 𝕋^d` with jointly measurable bounded slice weak gradients. -/
structure KData (d : ℕ) where
  K : Torus d → Torus d → ℝ
  G1 : Torus d → Torus d → Tangent d
  G2 : Torus d → Torus d → Tangent d
  Kc : Continuous (Function.uncurry K)
  G1m : Measurable (Function.uncurry G1)
  G2m : Measurable (Function.uncurry G2)
  B : ℝ
  G1b : ∀ x y, ‖G1 x y‖ ≤ B
  G2b : ∀ x y, ‖G2 x y‖ ≤ B
  g1 : ∀ y, IsWeakGradient (fun x => K x y) (fun x => G1 x y)
  g2 : ∀ x, IsWeakGradient (fun y => K x y) (fun y => G2 x y)

/-- The `i`-th coefficient function in `x`. -/
noncomputable def aK (S : Spec d) (K : Torus d → Torus d → ℝ) (i : ℕ) (y : Torus d) : ℝ :=
  ∫ x, K x y * S.v i x ∂S.mu

/-- The product coefficients `T_ij = ∫ K e_i ⊗ e_j dμ²`. -/
noncomputable def TK (S : Spec d) (K : Torus d → Torus d → ℝ) (i j : ℕ) : ℝ :=
  ∫ p, K p.1 p.2 * (S.v i p.1 * S.v j p.2) ∂(S.mu.prod S.mu)

/-- Swap the two variables. -/
def KData.swap (D : KData d) : KData d where
  K x y := D.K y x
  G1 x y := D.G2 y x
  G2 x y := D.G1 y x
  Kc := D.Kc.comp continuous_swap
  G1m := D.G2m.comp measurable_swap
  G2m := D.G1m.comp measurable_swap
  B := D.B
  G1b x y := D.G2b y x
  G2b x y := D.G1b y x
  g1 y := D.g2 y
  g2 x := D.g1 x

theorem Spec.integrable_of_bound (S : Spec d) {φ : Torus d → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ x, |φ x| ≤ M) : Integrable φ S.mu :=
  Integrable.of_bound hφ.aestronglyMeasurable M (Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hM x)

theorem Spec.weightedForm_eq (S : Spec d) (Y : Torus d → Tangent d) :
    weightedForm S.w Y Y = ∫ x, ‖Y x‖ ^ 2 ∂S.mu := by
  rw [weightedForm_self, S.integral_mu]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem KData.bound (D : KData d) : ∃ M, 0 ≤ M ∧ ∀ x y, |D.K x y| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn
    D.Kc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x y => ?_⟩
  have := hM (x, y) (mem_univ _)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem Spec.vbound (S : Spec d) (i : ℕ) : ∃ M, 0 ≤ M ∧ ∀ x, |S.v i x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn
    (S.vc i).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  have := hM x (mem_univ _)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem KData.slice_cont (D : KData d) (y : Torus d) : Continuous (fun x => D.K x y) :=
  D.Kc.comp (continuous_id.prodMk continuous_const)

theorem KData.integrable_K2 (S : Spec d) (D : KData d) :
    Integrable (fun p : Torus d × Torus d => D.K p.1 p.2 ^ 2) (S.mu.prod S.mu) :=
  (D.Kc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem KData.integrable_G1 (S : Spec d) (D : KData d) :
    Integrable (fun p : Torus d × Torus d => ‖D.G1 p.1 p.2‖ ^ 2) (S.mu.prod S.mu) :=
  Integrable.of_bound ((D.G1m.norm.pow_const 2).aestronglyMeasurable) (D.B ^ 2)
    (Eventually.of_forall fun p => by
      have h0 := norm_nonneg (D.G1 p.1 p.2)
      have h1 := D.G1b p.1 p.2
      simp only [norm_pow, norm_norm]
      exact pow_le_pow_left₀ h0 h1 2)

theorem aK_continuous (S : Spec d) (D : KData d) (i : ℕ) : Continuous (aK S D.K i) := by
  have hf : Continuous (Function.uncurry fun (y : Torus d) (x : Torus d) => D.K x y * S.v i x) :=
    (D.Kc.comp continuous_swap).mul ((S.vc i).comp continuous_snd)
  have := continuous_parametric_integral_of_continuous (μ := S.mu) hf isCompact_univ
  convert this using 1
  ext y
  simp [aK, Measure.restrict_univ]

theorem aK_bound (S : Spec d) (D : KData d) (i : ℕ) : ∃ M, 0 ≤ M ∧ ∀ y, |aK S D.K i y| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn
    (aK_continuous S D i).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  have := hM x (mem_univ _)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem TK_eq (S : Spec d) (D : KData d) (i j : ℕ) :
    TK S D.K i j = ∫ y, aK S D.K i y * S.v j y ∂S.mu := by
  have hint : Integrable (fun p : Torus d × Torus d => D.K p.1 p.2 * (S.v i p.1 * S.v j p.2))
      (S.mu.prod S.mu) :=
    (D.Kc.mul (((S.vc i).comp continuous_fst).mul ((S.vc j).comp continuous_snd))
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold TK
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show ∫ x, D.K x y * (S.v i x * S.v j y) ∂S.mu = aK S D.K i y * S.v j y
  rw [show aK S D.K i y = ∫ x, D.K x y * S.v i x ∂S.mu from rfl, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring

theorem TK_swap (S : Spec d) (D : KData d) (i j : ℕ) :
    TK S D.swap.K j i = TK S D.K i j := by
  unfold TK
  rw [← integral_prod_swap (μ := S.mu) (ν := S.mu)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [KData.swap, Prod.fst_swap, Prod.snd_swap]
  ring

theorem slice_sq (S : Spec d) (D : KData d) (y : Torus d) :
    HasSum (fun i => aK S D.K i y ^ 2) (∫ x, D.K x y ^ 2 ∂S.mu) :=
  S.hasSum_sq (S.memLp_mu (D.slice_cont y))

theorem slice_weighted (S : Spec d) (D : KData d) (y : Torus d) :
    HasSum (fun i => (1 + S.lam i) * aK S D.K i y ^ 2)
      (∫ x, (D.K x y ^ 2 + ‖D.G1 x y‖ ^ 2) ∂S.mu) := by
  have h := S.hasSum_weighted (S.memLp_mu (D.slice_cont y)) (D.g1 y)
  rw [S.weightedForm_eq] at h
  have hK : Integrable (fun x => D.K x y ^ 2) S.mu :=
    ((D.slice_cont y).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (fun x => ‖D.G1 x y‖ ^ 2) S.mu :=
    S.integrable_of_bound ((D.G1m.comp (measurable_id.prodMk measurable_const)).norm.pow_const 2)
      (M := D.B ^ 2) fun x => by
        have h0 := norm_nonneg (D.G1 x y)
        have h1 := D.G1b x y
        rw [abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ h0 h1 2
  rw [integral_add hK hG]
  exact h

theorem Spec.integrable_aK_sq (S : Spec d) (D : KData d) (i : ℕ) :
    Integrable (fun y => aK S D.K i y ^ 2) S.mu :=
  ((aK_continuous S D i).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem parseval_sq (S : Spec d) (D : KData d) :
    HasSum (fun i => ∫ y, aK S D.K i y ^ 2 ∂S.mu) (∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu) := by
  have hF : Integrable (fun y => ∫ x, D.K x y ^ 2 ∂S.mu) S.mu :=
    (D.integrable_K2 S).integral_prod_right
  have h := hasSum_integral_of_nonneg (μ := S.mu) (f := fun i y => aK S D.K i y ^ 2)
    (F := fun y => ∫ x, D.K x y ^ 2 ∂S.mu) (S.integrable_aK_sq D) (fun i y => sq_nonneg _)
    (slice_sq S D) hF
  rwa [← integral_prod_symm (fun p : Torus d × Torus d => D.K p.1 p.2 ^ 2)
    (D.integrable_K2 S)] at h

theorem parseval_weighted_x (S : Spec d) (D : KData d) :
    HasSum (fun i => (1 + S.lam i) * ∫ y, aK S D.K i y ^ 2 ∂S.mu)
      (∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu + ∫ p, ‖D.G1 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) := by
  have hI := (D.integrable_K2 S).add (D.integrable_G1 S)
  have hF : Integrable (fun y => ∫ x, (D.K x y ^ 2 + ‖D.G1 x y‖ ^ 2) ∂S.mu) S.mu :=
    hI.integral_prod_right
  have h := hasSum_integral_of_nonneg (μ := S.mu)
    (f := fun i y => (1 + S.lam i) * aK S D.K i y ^ 2)
    (F := fun y => ∫ x, (D.K x y ^ 2 + ‖D.G1 x y‖ ^ 2) ∂S.mu)
    (fun i => (S.integrable_aK_sq D i).const_mul _)
    (fun i y => mul_nonneg (by linarith [S.lam_nonneg i]) (sq_nonneg _))
    (slice_weighted S D) hF
  have h2 := integral_prod_symm (fun p : Torus d × Torus d => D.K p.1 p.2 ^ 2 + ‖D.G1 p.1 p.2‖ ^ 2) hI
  simp only at h2
  rw [← h2, integral_add (D.integrable_K2 S) (D.integrable_G1 S)] at h
  simpa only [integral_const_mul] using h

theorem hasSum_TK_sq (S : Spec d) (D : KData d) (i : ℕ) :
    HasSum (fun j => TK S D.K i j ^ 2) (∫ y, aK S D.K i y ^ 2 ∂S.mu) := by
  have h := S.hasSum_sq (S.memLp_mu (aK_continuous S D i))
  simpa only [TK_eq] using h

theorem hasSum_prod_of_iterated {f : ℕ × ℕ → ℝ} (h0 : ∀ p, 0 ≤ f p) {r : ℕ → ℝ} {A : ℝ}
    (hrow : ∀ i, HasSum (fun j => f (i, j)) (r i)) (hr : HasSum r A) : HasSum f A := by
  have hs : Summable f := by
    rw [summable_prod_of_nonneg h0]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    simpa only [fun i => (hrow i).tsum_eq] using hr.summable
  have h := hs.hasSum
  have : ∑' p, f p = A := by
    rw [hs.tsum_prod]
    simp only [fun i => (hrow i).tsum_eq]
    exact hr.tsum_eq
  rwa [this] at h

theorem hasSum_prod_weight_x (S : Spec d) (D : KData d) :
    HasSum (fun p : ℕ × ℕ => (1 + S.lam p.1) * TK S D.K p.1 p.2 ^ 2)
      (∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu + ∫ p, ‖D.G1 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) :=
  hasSum_prod_of_iterated (f := fun p : ℕ × ℕ => (1 + S.lam p.1) * TK S D.K p.1 p.2 ^ 2)
    (fun p => mul_nonneg (by linarith [S.lam_nonneg p.1]) (sq_nonneg _))
    (r := fun i => (1 + S.lam i) * ∫ y, aK S D.K i y ^ 2 ∂S.mu)
    (fun i => (hasSum_TK_sq S D i).mul_left (1 + S.lam i)) (parseval_weighted_x S D)

theorem hasSum_prod_sq (S : Spec d) (D : KData d) :
    HasSum (fun p : ℕ × ℕ => TK S D.K p.1 p.2 ^ 2) (∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu) :=
  hasSum_prod_of_iterated (f := fun p : ℕ × ℕ => TK S D.K p.1 p.2 ^ 2) (fun _ => sq_nonneg _)
    (r := fun i => ∫ y, aK S D.K i y ^ 2 ∂S.mu) (fun i => hasSum_TK_sq S D i) (parseval_sq S D)

/-- **Product-form Parseval** over `ℕ × ℕ` for a continuous kernel with bounded slice weak
gradients. -/
theorem product_parseval (S : Spec d) (D : KData d) :
    HasSum (fun p : ℕ × ℕ => (1 + S.lam p.1 + S.lam p.2) * TK S D.K p.1 p.2 ^ 2)
      (∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu + ∫ p, ‖D.G1 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu
        + ∫ p, ‖D.G2 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) := by
  have h1 := hasSum_prod_weight_x S D
  have h2 := hasSum_prod_weight_x S D.swap
  have h0 := hasSum_prod_sq S D
  have hA : ∫ p : Torus d × Torus d, D.swap.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu =
      ∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu :=
    integral_prod_swap (μ := S.mu) (ν := S.mu) (fun p : Torus d × Torus d => D.K p.1 p.2 ^ 2)
  have hN : ∫ p : Torus d × Torus d, ‖D.swap.G1 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu =
      ∫ p, ‖D.G2 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu :=
    integral_prod_swap (μ := S.mu) (ν := S.mu) (fun p : Torus d × Torus d => ‖D.G2 p.1 p.2‖ ^ 2)
  rw [hA, hN] at h2
  have h3 : HasSum (fun p : ℕ × ℕ => (1 + S.lam p.2) * TK S D.K p.1 p.2 ^ 2)
      (∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu + ∫ p, ‖D.G2 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) := by
    have := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr h2
    convert this using 2 with _p
    simp only [Function.comp, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [TK_swap]
  have h4 := (h1.add h3).sub h0
  convert h4 using 1
  · ext p; ring
  · ring

/-- Centered symmetric kernels have vanishing coefficients on the zero index. -/
theorem TK_zero_left (S : Spec d) (D : KData d) (h0 : ∀ x, S.v 0 x = 1)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (j : ℕ) : TK S D.K 0 j = 0 := by
  rw [TK_eq]
  have : ∀ y, aK S D.K 0 y = 0 := fun y => by
    simp only [aK, h0, mul_one]; exact hc y
  simp [this]

theorem TK_zero_right (S : Spec d) (D : KData d) (h0 : ∀ x, S.v 0 x = 1)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (hsym : ∀ x y, D.K x y = D.K y x) (i : ℕ) :
    TK S D.K i 0 = 0 := by
  have hs : D.swap.K = D.K := by funext x y; exact (hsym y x)
  have hd : ∀ y, ∫ x, D.swap.K x y ∂S.mu = 0 := fun y => by rw [hs]; exact hc y
  rw [← TK_swap S D]
  exact TK_zero_left S D.swap h0 hd i

/-- **Centered product Parseval**: sum over `i, j ≥ 1`. -/
theorem product_parseval_centered (S : Spec d) (D : KData d) (h0 : ∀ x, S.v 0 x = 1)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (hsym : ∀ x y, D.K x y = D.K y x) :
    HasSum (fun p : {p : ℕ × ℕ // 1 ≤ p.1 ∧ 1 ≤ p.2} =>
        (1 + S.lam p.1.1 + S.lam p.1.2) * TK S D.K p.1.1 p.1.2 ^ 2)
      (∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu + ∫ p, ‖D.G1 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu
        + ∫ p, ‖D.G2 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) := by
  have h := product_parseval S D
  rw [← hasSum_subtype_iff_of_support_subset (s := {p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2})] at h
  · exact h
  · intro p hp
    simp only [Function.mem_support, ne_eq] at hp
    by_contra hn
    apply hp
    have : p.1 = 0 ∨ p.2 = 0 := by
      simp only [Set.mem_ofPred_eq, not_and_or, not_le] at hn; omega
    rcases this with h1 | h1
    · rw [show TK S D.K p.1 p.2 = 0 from h1 ▸ TK_zero_left S D h0 hc _]; simp
    · rw [show TK S D.K p.1 p.2 = 0 from h1 ▸ TK_zero_right S D h0 hc hsym _]; simp

end DGPS.Lipschitz.KernelApproximation
