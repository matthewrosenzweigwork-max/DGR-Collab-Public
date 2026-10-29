import SharpSymmetricLSI.Paper.R29Herm

/-!
# Parseval and energy tails for the reference occupation basis (Phase 3, lane D; R29)
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem occBasis_zero_of_lt {e : ℕ → Torus d → ℝ} {N : ℕ} {α : ℕ →₀ ℕ} (h : N < occSize α) :
    occBasis e α N = 0 := by
  funext X
  unfold occBasis
  rw [Finset.sum_eq_zero fun c hc => absurd (occSize_le_of_mem hc) (by omega), mul_zero]
  rfl

/-- `∫ (f - ∑ cₐ gₐ)² = ∫ f² - 2∑ cₐ⟨f,gₐ⟩ + ∑∑ cₐc_b⟨gₐ,g_b⟩`. -/
theorem integral_sub_sum_sq {Ω A : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (S : Finset A) {f : Ω → ℝ} {g : A → Ω → ℝ} (a : A → ℝ) (hf : MemLp f 2 P)
    (hg : ∀ α, MemLp (g α) 2 P) :
    ∫ x, (f x - ∑ α ∈ S, a α * g α x) ^ 2 ∂P = ∫ x, f x ^ 2 ∂P -
      2 * ∑ α ∈ S, a α * ∫ x, f x * g α x ∂P +
        ∑ α ∈ S, ∑ β ∈ S, a α * a β * ∫ x, g α x * g β x ∂P := by
  have hfg : ∀ α, Integrable (fun x => f x * g α x) P := fun α => hf.integrable_mul (hg α)
  have hgg : ∀ α β, Integrable (fun x => g α x * g β x) P := fun α β =>
    (hg α).integrable_mul (hg β)
  have hpt : ∀ x, (f x - ∑ α ∈ S, a α * g α x) ^ 2 = f x ^ 2 -
      2 * ∑ α ∈ S, a α * (f x * g α x) + ∑ α ∈ S, ∑ β ∈ S, a α * a β * (g α x * g β x) :=
    fun x => by
      have e1 : (∑ α ∈ S, a α * g α x) ^ 2 =
          ∑ α ∈ S, ∑ β ∈ S, a α * a β * (g α x * g β x) := by
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
      have e2 : 2 * f x * ∑ α ∈ S, a α * g α x = 2 * ∑ α ∈ S, a α * (f x * g α x) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun α _ => by ring
      rw [sub_sq, e1, e2]
  simp_rw [hpt]
  have i1 : Integrable (fun x => ∑ α ∈ S, a α * (f x * g α x)) P :=
    integrable_finsetSum _ fun α _ => (hfg α).const_mul _
  have i2 : Integrable (fun x => ∑ α ∈ S, ∑ β ∈ S, a α * a β * (g α x * g β x)) P :=
    integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => (hgg α β).const_mul _
  rw [integral_add (f := fun x => f x ^ 2 - 2 * ∑ α ∈ S, a α * (f x * g α x)) (hf.integrable_sq.sub
      (i1.const_mul _)) i2, integral_sub (f := fun x => f x ^ 2) hf.integrable_sq (i1.const_mul _),
    integral_const_mul, integral_finsetSum _ fun α _ => (hfg α).const_mul _,
    integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => (hgg α β).const_mul _]
  simp_rw [integral_finsetSum _ fun β _ => (hgg _ β).const_mul _, integral_const_mul]

section ref
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

/-- **Parseval** for symmetric `Ψ ∈ L²(μ^{⊗N})` and the reference occupation basis. -/
theorem hasSum_sq_occ_ref {N : ℕ} {Ψ : Config N d → ℝ}
    (hΨ : MemLp Ψ 2 (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))) (hsym : IsSymmetric Ψ) :
    HasSum (fun α => (∫ X, Ψ X * occBasis e α N X
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))) ^ 2)
      (∫ X, Ψ X ^ 2 ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))) := by
  set μm := (μ : Measure (Torus d))
  set P := Measure.pi fun _ : Fin N => μm
  set e' : ℕ → Torus d → ℝ := fun j => (he.memLp j).aestronglyMeasurable.mk (e j)
  have hem : ∀ j, Measurable (e' j) := fun j =>
    (he.memLp j).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : ∀ j, e j =ᵐ[μm] e' j := fun j => (he.memLp j).aestronglyMeasurable.ae_eq_mk
  have hL : ∀ j, MemLp (e' j) 2 μm := fun j => (he.memLp j).ae_eq (hae j)
  have horth : ∀ i j, ∫ x, e' i x * e' j x ∂μm = if i = j then 1 else 0 := fun i j => by
    rw [← he.orthonormal i j]
    refine integral_congr_ae ?_
    filter_upwards [hae i, hae j] with x h1 h2
    simp only [h1, h2]
  have hcomp : ∀ g : Torus d → ℝ, MemLp g 2 μm → (∀ j, ∫ x, g x * e' j x ∂μm = 0) →
      g =ᵐ[μm] 0 :=
    fun g hg h => he.complete g hg fun j => by
      rw [← h j]; exact integral_congr_ae ((hae j).mono fun x hx => by simp only [hx])
  have hX := ae_eq_e_mk (N := N) he
  have hcoef : ∀ α, ∫ X, Ψ X * occBasis e α N X ∂P = ∫ X, Ψ X * occBasis e' α N X ∂P := fun α => by
    refine integral_congr_ae (hX.mono fun X hX => ?_)
    simp only [occBasis]
    congr 2
    refine Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun i _ => ?_
    rw [hX i]
  simp_rw [hcoef]
  exact hasSum_sq_occ hem hL horth hcomp hΨ hsym

theorem occEnergy_nonneg (α : ℕ →₀ ℕ) : 0 ≤ occEnergy lam α := by
  obtain ⟨c, hc0, hc⟩ := exists_lam_lower hyp hμ he
  unfold occEnergy Finsupp.sum
  exact Finset.sum_nonneg fun n _ => mul_nonneg (hc0.le.trans (hc _ (by omega))) (Nat.cast_nonneg _)

/-- **Energy tail**: the projection onto `{Λ_α ≤ L}` misses at most `B/L` of `∫Ψ²`. -/
theorem integral_sub_proj_sq_le {N : ℕ} {Ψ : Config N d → ℝ}
    (hΨ : MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) Ψ) (hsym : IsSymmetric Ψ)
    {B : ℝ} (hB : ∫ X, gradSqC Ψ X ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤ B)
    {L : ℝ} (hL : 0 < L) (S : Finset (ℕ →₀ ℕ)) (hS : ∀ α, occEnergy lam α ≤ L → α ∈ S) :
    ∫ X, (Ψ X - ∑ α ∈ S, (∫ Y, Ψ Y * occBasis e α N Y
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))) * occBasis e α N X) ^ 2
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤ B / L := by
  set P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  set c : (ℕ →₀ ℕ) → ℝ := fun α => ∫ Y, Ψ Y * occBasis e α N Y ∂P
  have hΨL : MemLp Ψ 2 P := (measurableEmbedding_flat.memLp_map_measure_iff).mp hΨ.2.1
  have hBm : ∀ α, MemLp (occBasis e α N) 2 P := fun α => memLp_occBasis hyp hμ he α N
  set S' := S.filter fun α => occSize α ≤ N
  have hc0 : ∀ α, N < occSize α → c α = 0 := fun α h => by
    simp only [c, occBasis_zero_of_lt h, Pi.zero_apply, mul_zero, integral_zero]
  have hPS : (fun X => Ψ X - ∑ α ∈ S, c α * occBasis e α N X) =
      fun X => Ψ X - ∑ α ∈ S', c α * occBasis e α N X := by
    funext X
    congr 1
    refine (Finset.sum_subset (Finset.filter_subset _ S) fun α hα hα' => ?_).symm
    have : N < occSize α := by
      by_contra h; exact hα' (Finset.mem_filter.mpr ⟨hα, by omega⟩)
    rw [hc0 α this, zero_mul]
  have hPS2 : (fun X => (Ψ X - ∑ α ∈ S, c α * occBasis e α N X) ^ 2) =
      fun X => (Ψ X - ∑ α ∈ S', c α * occBasis e α N X) ^ 2 := by
    funext X; rw [congrFun hPS X]
  rw [hPS2]
  rw [integral_sub_sum_sq S' c hΨL hBm]
  have horthB : ∀ α ∈ S', ∀ β ∈ S', ∫ X, occBasis e α N X * occBasis e β N X ∂P =
      if α = β then 1 else 0 := fun α hα β hβ =>
    integral_occBasis_mul he.memLp he.orthonormal (Finset.mem_filter.mp hα).2
      (Finset.mem_filter.mp hβ).2
  have h3 : ∑ α ∈ S', ∑ β ∈ S', c α * c β * ∫ X, occBasis e α N X * occBasis e β N X ∂P =
      ∑ α ∈ S', c α ^ 2 := by
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Finset.sum_congr rfl fun β hβ => by rw [horthB α hα β hβ]]
    simp [Finset.sum_ite_eq, hα, sq]
  have h2 : ∑ α ∈ S', c α * ∫ X, Ψ X * occBasis e α N X ∂P = ∑ α ∈ S', c α ^ 2 :=
    Finset.sum_congr rfl fun α _ => by simp [c, sq]
  rw [h2, h3]
  -- Parseval and the energy bound for the tail
  have hpar := hasSum_sq_occ_ref hyp hμ he hΨL hsym
  have hsum := hpar.summable
  have hEn : ∀ T : Finset (ℕ →₀ ℕ), ∑ α ∈ T, occEnergy lam α * c α ^ 2 ≤ B := fun T => by
    have hsub : ∑ α ∈ T, occEnergy lam α * c α ^ 2 =
        ∑ α ∈ T.filter (fun α => occSize α ≤ N), occEnergy lam α * c α ^ 2 := by
      refine (Finset.sum_subset (Finset.filter_subset _ T) fun α hα hα' => ?_).symm
      have : N < occSize α := by
        by_contra h; exact hα' (Finset.mem_filter.mpr ⟨hα, by omega⟩)
      rw [hc0 α this]; ring
    rw [hsub]
    exact (bessel_occ_energy hyp hμ he hΨ _ fun α hα => (Finset.mem_filter.mp hα).2).trans hB
  have htail : ∀ α, (if α ∈ S' then 0 else c α ^ 2) ≤ occEnergy lam α * c α ^ 2 / L := fun α => by
    split_ifs with h
    · exact div_nonneg (mul_nonneg (occEnergy_nonneg hyp hμ he α) (sq_nonneg _)) hL.le
    · by_cases hN : occSize α ≤ N
      · have hΛ : L < occEnergy lam α := by
          by_contra h'; exact h (Finset.mem_filter.mpr ⟨hS α (by linarith), hN⟩)
        rw [le_div_iff₀ hL]
        nlinarith [sq_nonneg (c α)]
      · rw [hc0 α (by omega)]; simp
  have hsplit : ∫ X, Ψ X ^ 2 ∂P - ∑ α ∈ S', c α ^ 2 = ∑' α, (if α ∈ S' then 0 else c α ^ 2) := by
    rw [← hpar.tsum_eq]
    have : ∀ α, c α ^ 2 = (if α ∈ S' then c α ^ 2 else 0) + (if α ∈ S' then 0 else c α ^ 2) :=
      fun α => by split_ifs <;> simp
    rw [tsum_congr this, Summable.tsum_add (summable_of_ne_finset_zero (s := S')
      fun α hα => by simp [hα]) (hsum.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
        fun α => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl), tsum_eq_sum (s := S') fun α hα => by simp [hα]]
    simp only [Finset.sum_ite_mem, Finset.inter_self]
    ring
  have hEsum : Summable fun α => occEnergy lam α * c α ^ 2 :=
    summable_of_sum_le (fun α => mul_nonneg (occEnergy_nonneg hyp hμ he α) (sq_nonneg _)) hEn
  have hle : ∑' α, (if α ∈ S' then 0 else c α ^ 2) ≤ ∑' α, occEnergy lam α * c α ^ 2 / L :=
    Summable.tsum_le_tsum htail ((hsum.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
      fun α => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl)) (hEsum.div_const L)
  rw [tsum_div_const] at hle
  have hEt : ∑' α, occEnergy lam α * c α ^ 2 ≤ B :=
    Real.tsum_le_of_sum_le (fun α => mul_nonneg (occEnergy_nonneg hyp hμ he α) (sq_nonneg _)) hEn
  have : ∫ X, Ψ X ^ 2 ∂P - 2 * ∑ α ∈ S', c α ^ 2 + ∑ α ∈ S', c α ^ 2 =
      ∫ X, Ψ X ^ 2 ∂P - ∑ α ∈ S', c α ^ 2 := by ring
  rw [this, hsplit]
  exact hle.trans (div_le_div_of_nonneg_right hEt hL.le)

end ref

end SharpLSI
