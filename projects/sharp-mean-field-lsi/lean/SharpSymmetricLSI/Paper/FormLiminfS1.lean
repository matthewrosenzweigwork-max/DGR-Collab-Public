import SharpSymmetricLSI.Paper.ULimit4
import SharpSymmetricLSI.Paper.EnergyParseval1
import SharpSymmetricLSI.Statements.R25_Lemma_A_2

/-!
# (8.20), Gaussian side (lane s42): kernel matrices and the `R → ∞` step, part 1

`kerMat K μ e p q = ∫∫ K(x,y) e_{p+1}(x) e_{q+1}(y) dμ dμ`; `Tmat W μ e = kerMat (K) μ e` for the
centered kernel `K`. The family `e_{p+1} ⊗ e_{q+1}` is orthonormal in `L²(μ⊗μ)`, so Bessel gives
`∑_{p,q} kerMat(K)_{pq}² ≤ ‖K‖²_{L²(μ⊗μ)}` (`kerMat_bessel`). For a kernel approximation `K_R`
((6.4), R25 `IsKernelApprox`), `∑_{p,q} (kerMat(K_R) - T)_{pq}² ≤ ‖K_R - K‖²_{L²} → 0`
(`kerMat_HS_tendsto`). For a finite-rank kernel, `kerMat` reads off the coefficients
(`kerMat_eq_zero_of_not_mem`).
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The matrix of a kernel in the reference basis (`p, q ≥ 1` in manuscript indexing). -/
noncomputable def kerMat (K : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (e : ℕ → Torus d → ℝ)
    (p q : ℕ) : ℝ :=
  ∫ x, ∫ y, K x y * e (p + 1) x * e (q + 1) y ∂μ ∂μ

theorem Tmat_eq_kerMat (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (e : ℕ → Torus d → ℝ) : Tmat W μ e = kerMat (centeredKernel W μ) μ e := rfl

theorem inner_toLp_gen {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) : ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, f x * g x ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  simp only [RCLike.inner_apply, conj_trivial, h1, h2]
  ring

theorem memLp_tensor {ν : Measure (Torus d)} [IsFiniteMeasure ν] {f g : Torus d → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    MemLp (fun z : Torus d × Torus d => f z.1 * g z.2) 2 (ν.prod ν) := by
  have hm : AEStronglyMeasurable (fun z : Torus d × Torus d => f z.1 * g z.2) (ν.prod ν) :=
    hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd
  rw [memLp_two_iff_integrable_sq hm]
  refine (hf.integrable_sq.mul_prod hg.integrable_sq).congr (Eventually.of_forall fun z => ?_)
  simp only
  ring

section basis
variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  (he : IsRefEigenbasis μ e lam)
include he

/-- `e_{p+1} ⊗ e_{q+1} ∈ L²(μ⊗μ)`. -/
def tens (p q : ℕ) : Lp ℝ 2 (μ.prod μ) :=
  (memLp_tensor (he.memLp (p + 1)) (he.memLp (q + 1))).toLp _

theorem orthonormal_tens : Orthonormal ℝ (fun pq : ℕ × ℕ => tens he pq.1 pq.2) := by
  rw [orthonormal_iff_ite]
  rintro ⟨p, q⟩ ⟨p', q'⟩
  simp only [tens]
  rw [inner_toLp_gen]
  have e1 : (fun z : Torus d × Torus d => e (p + 1) z.1 * e (q + 1) z.2 *
      (e (p' + 1) z.1 * e (q' + 1) z.2)) =
      fun z => (e (p + 1) z.1 * e (p' + 1) z.1) * (e (q + 1) z.2 * e (q' + 1) z.2) := by
    funext z; ring
  rw [e1, integral_prod_mul (fun x => e (p + 1) x * e (p' + 1) x)
    (fun y => e (q + 1) y * e (q' + 1) y), he.orthonormal, he.orthonormal]
  simp only [Nat.add_right_cancel_iff, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem kerMat_eq_inner {K : Torus d → Torus d → ℝ}
    (hK : MemLp (fun z : Torus d × Torus d => K z.1 z.2) 2 (μ.prod μ)) (p q : ℕ) :
    kerMat K μ e p q = ⟪tens he p q, hK.toLp _⟫ := by
  simp only [tens]
  rw [inner_toLp_gen]
  have hi : Integrable (fun z : Torus d × Torus d => e (p + 1) z.1 * e (q + 1) z.2 * K z.1 z.2)
      (μ.prod μ) := (memLp_tensor (he.memLp (p + 1)) (he.memLp (q + 1))).integrable_mul hK
  rw [integral_prod _ hi]
  unfold kerMat
  congr 1; funext x; congr 1; funext y; ring

/-- **Bessel**: `∑_{p,q} kerMat(K)_{pq}² ≤ ∫ K² d(μ⊗μ)`. -/
theorem kerMat_bessel {K : Torus d → Torus d → ℝ}
    (hK : MemLp (fun z : Torus d × Torus d => K z.1 z.2) 2 (μ.prod μ)) :
    Summable (fun pq : ℕ × ℕ => kerMat K μ e pq.1 pq.2 ^ 2) ∧
      ∑' pq : ℕ × ℕ, kerMat K μ e pq.1 pq.2 ^ 2 ≤ ∫ z, K z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  have ho := orthonormal_tens he
  have h1 := ho.inner_products_summable (hK.toLp _)
  have h2 := ho.tsum_inner_products_le (hK.toLp _)
  have e1 : ∀ pq : ℕ × ℕ, ‖⟪tens he pq.1 pq.2, hK.toLp _⟫‖ ^ 2 = kerMat K μ e pq.1 pq.2 ^ 2 :=
    fun pq => by rw [kerMat_eq_inner he hK, Real.norm_eq_abs, sq_abs]
  have e2 : ‖hK.toLp (fun z : Torus d × Torus d => K z.1 z.2)‖ ^ 2 =
      ∫ z, K z.1 z.2 ^ 2 ∂(μ.prod μ) := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp_gen]
    congr 1; funext z; ring
  simp only [e1] at h1 h2
  rw [e2] at h2
  exact ⟨h1, h2⟩

theorem kerMat_sub {K₁ K₂ : Torus d → Torus d → ℝ}
    (h₁ : MemLp (fun z : Torus d × Torus d => K₁ z.1 z.2) 2 (μ.prod μ))
    (h₂ : MemLp (fun z : Torus d × Torus d => K₂ z.1 z.2) 2 (μ.prod μ)) (p q : ℕ) :
    kerMat K₁ μ e p q - kerMat K₂ μ e p q = kerMat (fun x y => K₁ x y - K₂ x y) μ e p q := by
  rw [kerMat_eq_inner he h₁, kerMat_eq_inner he h₂, kerMat_eq_inner he (h₁.sub h₂),
    ← inner_sub_right]
  congr 1

/-- A finite-rank kernel `∑_{i,j∈s} a_{ij} e_{i+1}(x) e_{j+1}(y)` is in `L²(μ⊗μ)`. -/
theorem memLp_finRank {K : Torus d → Torus d → ℝ} {s : Finset ℕ} {a : ℕ → ℕ → ℝ}
    (hK : ∀ x y, K x y = ∑ i ∈ s, ∑ j ∈ s, a i j * e (i + 1) x * e (j + 1) y) :
    MemLp (fun z : Torus d × Torus d => K z.1 z.2) 2 (μ.prod μ) := by
  have e1 : (fun z : Torus d × Torus d => K z.1 z.2) =
      fun z => ∑ i ∈ s, ∑ j ∈ s, a i j * (e (i + 1) z.1 * e (j + 1) z.2) := by
    funext z; rw [hK]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1]
  exact memLp_finsetSum (ε' := ℝ) _ fun i _ => memLp_finsetSum (ε' := ℝ) _ fun j _ =>
    (memLp_tensor (he.memLp (i + 1)) (he.memLp (j + 1))).const_mul (a i j)

/-- **A finite-rank kernel's matrix is its coefficient matrix.** -/
theorem kerMat_eq_zero_of_not_mem {K : Torus d → Torus d → ℝ} {s : Finset ℕ} {a : ℕ → ℕ → ℝ}
    (hK : ∀ x y, K x y = ∑ i ∈ s, ∑ j ∈ s, a i j * e (i + 1) x * e (j + 1) y) (p q : ℕ) :
    kerMat K μ e p q = if p ∈ s ∧ q ∈ s then a p q else 0 := by
  have hm := memLp_finRank he hK
  rw [kerMat_eq_inner he hm]
  have hL : hm.toLp (fun z : Torus d × Torus d => K z.1 z.2) =
      ∑ i ∈ s, ∑ j ∈ s, a i j • tens he i j := by
    have e1 : (fun z : Torus d × Torus d => K z.1 z.2) =
        fun z => ∑ i ∈ s, ∑ j ∈ s, a i j * (e (i + 1) z.1 * e (j + 1) z.2) := by
      funext z; rw [hK]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hij : ∀ i j, MemLp (fun z : Torus d × Torus d => a i j * (e (i + 1) z.1 * e (j + 1) z.2))
        2 (μ.prod μ) := fun i j =>
      (memLp_tensor (he.memLp (i + 1)) (he.memLp (j + 1))).const_mul (a i j)
    refine Lp.ext ?_
    have hsum : ∀ (t : Finset ℕ) (F : ℕ → Lp ℝ 2 (μ.prod μ)),
        (⇑(∑ i ∈ t, F i) : Torus d × Torus d → ℝ) =ᵐ[μ.prod μ]
          fun z => ∑ i ∈ t, (F i : Torus d × Torus d → ℝ) z := fun t F => by
      classical
      induction t using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero _ _ _
      | insert b t hb ih =>
        simp only [Finset.sum_insert hb]
        filter_upwards [Lp.coeFn_add (F b) (∑ i ∈ t, F i), ih] with z h1 h2
        rw [h1, Pi.add_apply, h2]
    have hall : ∀ᵐ z ∂(μ.prod μ), ∀ i j, (tens he i j : Torus d × Torus d → ℝ) z =
        e (i + 1) z.1 * e (j + 1) z.2 := by
      rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
      exact MemLp.coeFn_toLp _
    have hsm : ∀ᵐ z ∂(μ.prod μ), ∀ i j, ((a i j • tens he i j : Lp ℝ 2 (μ.prod μ)) :
        Torus d × Torus d → ℝ) z = a i j * (tens he i j : Torus d × Torus d → ℝ) z := by
      rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
      filter_upwards [Lp.coeFn_smul (a i j) (tens he i j)] with z hz
      rw [hz]; rfl
    have hinner : ∀ᵐ z ∂(μ.prod μ), ∀ i, (⇑(∑ j ∈ s, a i j • tens he i j) :
        Torus d × Torus d → ℝ) z = ∑ j ∈ s, ((a i j • tens he i j : Lp ℝ 2 (μ.prod μ)) :
          Torus d × Torus d → ℝ) z := by
      rw [ae_all_iff]; intro i; exact hsum s _
    filter_upwards [hm.coeFn_toLp, hsum s (fun i => ∑ j ∈ s, a i j • tens he i j), hinner,
      hsm, hall] with z h1 h2 h3 h4 h5
    rw [h1, h2, hK]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h3 i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h4 i j, h5 i j]; ring
  rw [hL]
  have ho := orthonormal_tens he
  have hδ : ∀ i j, ⟪tens he p q, tens he i j⟫ = if p = i ∧ q = j then 1 else 0 := fun i j => by
    have := orthonormal_iff_ite.mp ho (p, q) (i, j)
    simpa [Prod.mk.injEq] using this
  simp only [inner_sum, inner_smul_right, hδ, mul_ite, mul_one, mul_zero]
  by_cases hp : p ∈ s <;> by_cases hq : q ∈ s
  · rw [if_pos ⟨hp, hq⟩, Finset.sum_eq_single p (fun i _ hi => Finset.sum_eq_zero fun j _ =>
      if_neg fun h => hi h.1.symm) (fun h => absurd hp h)]
    rw [Finset.sum_eq_single q (fun j _ hj => if_neg fun h => hj h.2.symm)
      (fun h => absurd hq h), if_pos ⟨rfl, rfl⟩]
  · rw [if_neg fun h => hq h.2]
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj =>
      if_neg fun (h : p = i ∧ q = j) => hq (h.2 ▸ hj)
  · rw [if_neg fun h => hp h.1]
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j _ =>
      if_neg fun (h : p = i ∧ q = j) => hp (h.1 ▸ hi)
  · rw [if_neg fun h => hp h.1]
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j _ =>
      if_neg fun (h : p = i ∧ q = j) => hp (h.1 ▸ hi)

end basis

section approx
variable {μ : ProbabilityMeasure (Torus d)} (hyp : Hyp V W KV KW) (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  {KR : ℕ → Torus d → Torus d → ℝ} (hKR : IsKernelApprox W μ e KR)
include hyp hμ he hKR

/-- **`∑_{p,q} (kerMat(K_R) - T)_{pq}²` is finite and tends to `0`.** -/
theorem kerMat_HS_tendsto :
    (∀ R, Summable fun p : ℕ × ℕ => (kerMat (KR R) μ e p.1 p.2 - Tmat W μ e p.1 p.2) ^ 2) ∧
    Tendsto (fun R => ∑' p : ℕ × ℕ, (kerMat (KR R) μ e p.1 p.2 - Tmat W μ e p.1 p.2) ^ 2)
      atTop (𝓝 0) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨hfin, -, hL2, -⟩ := hKR
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μm
  have hKm : MemLp (fun z : Torus d × Torus d => centeredKernel W μm z.1 z.2) 2 (μm.prod μm) :=
    MemLp.of_bound (measurable_centeredKernel hyp μm).aestronglyMeasurable B
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB _ _)
  have hRm : ∀ R, MemLp (fun z : Torus d × Torus d => KR R z.1 z.2) 2 (μm.prod μm) := fun R => by
    obtain ⟨s, a, -, hK⟩ := hfin R
    exact memLp_finRank he hK
  set D : ℕ → Torus d → Torus d → ℝ := fun R x y => KR R x y - centeredKernel W μm x y
  have hD : ∀ R p q, kerMat (KR R) μ e p q - Tmat W μ e p q = kerMat (D R) μm e p q :=
    fun R p q => kerMat_sub he (hRm R) hKm p q
  have hbes : ∀ R, Summable (fun pq : ℕ × ℕ => kerMat (D R) μm e pq.1 pq.2 ^ 2) ∧
      ∑' pq : ℕ × ℕ, kerMat (D R) μm e pq.1 pq.2 ^ 2 ≤ ∫ z, D R z.1 z.2 ^ 2 ∂(μm.prod μm) :=
    fun R => kerMat_bessel he ((hRm R).sub hKm)
  have key : ∀ R, ∑' p : ℕ × ℕ, (kerMat (KR R) μm e p.1 p.2 - Tmat W μm e p.1 p.2) ^ 2 =
      ∑' pq : ℕ × ℕ, kerMat (D R) μm e pq.1 pq.2 ^ 2 := fun R => tsum_congr fun p => by rw [hD]
  refine ⟨fun R => (hbes R).1.congr fun p => by rw [hD], ?_⟩
  refine Tendsto.congr (fun R => (key R).symm) ?_
  -- `‖K_R - K‖²_{L²(μ⊗μ)} → 0`
  have hmp := measurePreserving_piFinTwo (fun _ : Fin 2 => μm)
  have hle : ∀ R, ENNReal.ofReal (∫ z, D R z.1 z.2 ^ 2 ∂(μm.prod μm)) ≤
      ∫⁻ X, ENNReal.ofReal ((kerC (KR R) X - kerC (centeredKernel W μ) X) ^ 2 +
        gradSqC (fun Y => kerC (KR R) Y - kerC (centeredKernel W μ) Y) X)
        ∂Measure.pi (fun _ : Fin 2 => μm) := fun R => by
    have hDi : Integrable (fun z : Torus d × Torus d => D R z.1 z.2 ^ 2) (μm.prod μm) :=
      ((hRm R).sub hKm).integrable_sq
    rw [ofReal_integral_eq_lintegral_ofReal hDi (Eventually.of_forall fun _ => sq_nonneg _)]
    rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    refine lintegral_mono fun X => ENNReal.ofReal_le_ofReal ?_
    have hg : 0 ≤ gradSqC (fun Y => kerC (KR R) Y - kerC (centeredKernel W μ) Y) X :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    exact le_add_of_nonneg_right hg
  have hE : Tendsto (fun R => ENNReal.ofReal (∫ z, D R z.1 z.2 ^ 2 ∂(μm.prod μm))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL2 (fun _ => bot_le) hle
  have hE' : Tendsto (fun R => ∫ z, D R z.1 z.2 ^ 2 ∂(μm.prod μm)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
    simp only [Function.comp_def, ENNReal.toReal_zero] at this
    refine this.congr fun R => ?_
    rw [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE'
    (fun R => tsum_nonneg fun _ => sq_nonneg _) fun R => (hbes R).2

end approx

end SharpLSI
