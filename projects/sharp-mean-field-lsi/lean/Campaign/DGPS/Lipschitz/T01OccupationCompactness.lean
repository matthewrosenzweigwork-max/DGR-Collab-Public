import DGPS.Lipschitz.T01OccupationBridge
import DGPS.Analysis.RelativeFisher
import SharpSymmetricLSI.Paper.R29Main
import SharpSymmetricLSI.Paper.R37Particle
import FullLabeledLSI.Infra.SpectralEnergy

/-!
# Common spectral occupation coefficients without a semiconvex hypothesis

The occupation basis is the legacy multiplicity basis of the actual common reference
spectrum. Its Parseval identity uses only the reference eigenbasis. Energy bounds are
obtained by grouping the actual tensor coefficients, rather than changing the basis.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI

variable {d N : ℕ}

/-- Parseval for the actual common reference occupation basis, including a.e. symmetry. -/
theorem t01_hasSum_sq_reference_occupation (S : Spec d)
    (he : IsRefEigenbasis S.mu S.v S.lam) {f : Config N d → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : Fin N => S.mu))
    (hs : ∀ σ : Equiv.Perm (Fin N), (fun X => f (X ∘ σ)) =ᵐ[
      Measure.pi (fun _ : Fin N => S.mu)] f) :
    HasSum (fun α => (∫ X, f X * occBasis S.v α N X
      ∂Measure.pi (fun _ : Fin N => S.mu)) ^ 2)
      (∫ X, f X ^ 2 ∂Measure.pi (fun _ : Fin N => S.mu)) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hae := symmetrize_ae_eq hs
  have hp := hasSum_sq_occ (fun j => (S.vc j).measurable) he.memLp he.orthonormal
    he.complete (hf.ae_eq hae.symm) (isSymmetric_symmetrize f)
  have hcoef : ∀ α, (∫ X, symmetrize f X * occBasis S.v α N X
      ∂Measure.pi (fun _ : Fin N => S.mu)) =
      ∫ X, f X * occBasis S.v α N X ∂Measure.pi (fun _ : Fin N => S.mu) := by
    intro α
    exact integral_congr_ae (hae.mono fun X hX => congrArg (fun z => z * occBasis S.v α N X) hX)
  have hnorm : (∫ X, symmetrize f X ^ 2 ∂Measure.pi (fun _ : Fin N => S.mu)) =
      ∫ X, f X ^ 2 ∂Measure.pi (fun _ : Fin N => S.mu) :=
    integral_congr_ae (hae.mono fun X hX => congrArg (fun z : ℝ => z ^ 2) hX)
  simpa only [hcoef, hnorm] using hp

/-- Labelling energy is a purely combinatorial identity once the constant mode has
zero eigenvalue; it does not require a potential hypothesis. -/
theorem t01_sum_lam_labelling (lam : ℕ → ℝ) (hlam0 : lam 0 = 0)
    {α : ℕ →₀ ℕ} {c : Fin N → Fin (α.support.sup id + 2)}
    (hc : c ∈ occLabellings α N) : ∑ i, lam (c i : ℕ) = occEnergy lam α := by
  rw [← Finset.sum_fiberwise' Finset.univ c (fun ℓ => lam (ℓ : ℕ))]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, hlam0, mul_zero, zero_add, Fin.val_succ]
  have hcount : ∀ n : Fin (α.support.sup id + 1),
      ((Finset.univ.filter fun i => c i = n.succ).card : ℝ) = α n := by
    intro n
    rw [← mem_occLabellings.mp hc n]
    congr 2
  simp_rw [hcount]
  rw [Fin.sum_univ_eq_sum_range (fun n => (α n : ℝ) * lam (n + 1)), occEnergy, Finsupp.sum]
  symm
  rw [Finset.sum_subset (fun n hn => Finset.mem_range.mpr (support_lt α hn)) (fun n _ hn => by
    have : α n = 0 := by simpa using hn
    simp [this])]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Grouping all tensor labels of one type gives exactly the square of the normalized
occupation coefficient. This statement concerns the existing legacy basis itself. -/
theorem t01_occupation_coefficient_sq (S : Spec d)
    (he : IsRefEigenbasis S.mu S.v S.lam) {f : Config N d → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : Fin N => S.mu))
    (hs : IsSymmetric f) (α : ℕ →₀ ℕ) (hN : occSize α ≤ N) :
    (∫ X, f X * occBasis S.v α N X ∂Measure.pi (fun _ : Fin N => S.mu)) ^ 2 =
      ∑ c ∈ occLabellings α N,
        (∫ X, f X * tensorE S.v (fun i => (c i : ℕ)) X
          ∂Measure.pi (fun _ : Fin N => S.mu)) ^ 2 := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hint : ∀ c : Fin N → ℕ, Integrable (fun X => f X * tensorE S.v c X)
      (Measure.pi fun _ : Fin N => S.mu) := fun c =>
    hf.integrable_mul (memLp_prod_eval fun i => he.memLp (c i))
  have hcard := card_occLabellings α hN
  have hnd : 0 < N.descFactorial (occSize α) := Nat.descFactorial_pos.mpr hN
  have hc0 : (occLabellings α N).card ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hcard
    omega
  obtain ⟨c0, hc0⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc0)
  have htype := typeOf_val_of_mem hc0
  let a : ℝ := ∫ X, f X * tensorE S.v (fun i => (c0 i : ℕ)) X
    ∂Measure.pi (fun _ : Fin N => S.mu)
  have hcst : ∀ c ∈ occLabellings α N,
      (∫ X, f X * tensorE S.v (fun i => (c i : ℕ)) X
        ∂Measure.pi (fun _ : Fin N => S.mu)) ^ 2 = a ^ 2 := by
    intro c hc
    have htypes : typeOf (fun i => (c0 i : ℕ)) = typeOf (fun i => (c i : ℕ)) :=
      htype.trans (typeOf_val_of_mem hc).symm
    have hh := integral_tensor_eq_of_typeOf hs hint htypes
    exact congrArg (fun z : ℝ => z ^ 2) hh
  have hcoef := integral_occBasis_eq' hs hint (fun i => (c0 i : ℕ)) α htype
  have hscale : Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ)) ^ 2 *
      ((occLabellings α N).card : ℝ) ^ 2 = (occLabellings α N).card := by
    rw [Real.sq_sqrt (by positivity)]
    have hcardR : ((occLabellings α N).card : ℝ) * occFactorial α =
        N.descFactorial (occSize α) := by exact_mod_cast hcard
    have hndR : (0 : ℝ) < N.descFactorial (occSize α) := by exact_mod_cast hnd
    field_simp
    rw [← hcardR]
    ring
  rw [hcoef, mul_pow, mul_pow, hscale, Finset.sum_congr rfl hcst,
    Finset.sum_const, nsmul_eq_mul]

/-- The coefficient grouping identity respects the original a.e.-symmetric test. -/
theorem t01_occupation_coefficient_sq_ae (S : Spec d)
    (he : IsRefEigenbasis S.mu S.v S.lam) {f : Config N d → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : Fin N => S.mu))
    (hs : ∀ σ : Equiv.Perm (Fin N), (fun X => f (X ∘ σ)) =ᵐ[
      Measure.pi (fun _ : Fin N => S.mu)] f) (α : ℕ →₀ ℕ) (hN : occSize α ≤ N) :
    (∫ X, f X * occBasis S.v α N X ∂Measure.pi (fun _ : Fin N => S.mu)) ^ 2 =
      ∑ c ∈ occLabellings α N,
        (∫ X, f X * tensorE S.v (fun i => (c i : ℕ)) X
          ∂Measure.pi (fun _ : Fin N => S.mu)) ^ 2 := by
  have hae := symmetrize_ae_eq hs
  have hc : ∀ u : Config N d → ℝ,
      (∫ X, symmetrize f X * u X ∂Measure.pi (fun _ : Fin N => S.mu)) =
        ∫ X, f X * u X ∂Measure.pi (fun _ : Fin N => S.mu) := by
    intro u
    exact integral_congr_ae (hae.mono fun X hX => congrArg (fun z => z * u X) hX)
  simpa only [hc] using t01_occupation_coefficient_sq S he (hf.ae_eq hae.symm)
    (isSymmetric_symmetrize f) α hN

/-- The actual reference H1 energy controls the coefficients of this same occupation
basis. Tensor energy Bessel is applied on the unchanged Sobolev domain. -/
theorem t01_reference_occupation_energy_bound (S : Spec d)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hC1 : ∀ j, SharpLSI.FL.Gross.C1T (S.v j))
    (hlam0 : S.lam 0 = 0) {f : Config N d → ℝ}
    (hH : MemH1C (Measure.pi fun _ : Fin N => S.mu) f)
    (hs : ∀ σ : Equiv.Perm (Fin N), (fun X => f (X ∘ σ)) =ᵐ[
      Measure.pi (fun _ : Fin N => S.mu)] f) (T : Finset (ℕ →₀ ℕ)) :
    ∑ α ∈ T, occEnergy S.lam α *
      (∫ X, f X * occBasis S.v α N X ∂Measure.pi (fun _ : Fin N => S.mu)) ^ 2 ≤
        (SharpLSI.FL.refEnergy S.mu f).toReal := by
  classical
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  let P : BoundedPositiveReference d :=
    { density := S.w, measurable_density := S.meas, lower := S.c, upper := S.C,
      lower_pos := S.pos, lower_le := S.bound.mono fun _ hx => hx.1,
      le_upper := S.bound.mono fun _ hx => hx.2, mass_one := S.prob }
  have htensor := SharpLSI.FL.Spectral.bessel_energy_of_H1 P.measure_le_smul_haar
    P.haar_le_smul_measure he hC1 (fun _ => EventuallyEq.refl _ _) hlam0 hH
  have hf : MemLp f 2 (Measure.pi fun _ : Fin N => S.mu) :=
    (measurableEmbedding_flat.memLp_map_measure_iff).mp hH.2.1
  let F : (ℕ →₀ ℕ) → Finset (Fin N → ℕ) := fun α =>
    (occLabellings α N).image (fun c i => (c i : ℕ))
  have htype : ∀ α c, c ∈ F α → typeOf c = α := by
    intro α c hc
    obtain ⟨lab, hlab, heq⟩ := Finset.mem_image.mp hc
    rw [← heq]
    exact typeOf_val_of_mem hlab
  let T' := T.filter fun α => occSize α ≤ N
  have hz : ∑ α ∈ T, occEnergy S.lam α *
      (∫ X, f X * occBasis S.v α N X ∂Measure.pi (fun _ : Fin N => S.mu)) ^ 2 =
      ∑ α ∈ T', occEnergy S.lam α *
      (∫ X, f X * occBasis S.v α N X ∂Measure.pi (fun _ : Fin N => S.mu)) ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun α hα hα' => ?_
    have hlt : N < occSize α := by
      by_contra h
      exact hα' (Finset.mem_filter.mpr ⟨hα, by omega⟩)
    simp only [occBasis_zero_of_lt hlt, Pi.zero_apply, mul_zero, integral_zero,
      zero_pow (by norm_num : 2 ≠ 0)]
  rw [hz]
  have hgroup : ∀ α ∈ T', occEnergy S.lam α *
      (∫ X, f X * occBasis S.v α N X ∂Measure.pi (fun _ : Fin N => S.mu)) ^ 2 =
      ∑ c ∈ F α, SharpLSI.FL.Spectral.Lam S.lam c *
        SharpLSI.FL.Spectral.coeff S.mu S.v c f ^ 2 := by
    intro α hα
    rw [t01_occupation_coefficient_sq_ae S he hf hs α (Finset.mem_filter.mp hα).2,
      Finset.mul_sum]
    dsimp only [F]
    rw [Finset.sum_image (by
      intro c hc c' hc' hcc
      funext i
      exact Fin.ext (congrFun hcc i))]
    apply Finset.sum_congr rfl
    intro c hc
    rw [← t01_sum_lam_labelling S.lam hlam0 hc]
    rfl
  rw [Finset.sum_congr rfl hgroup]
  have hdis : ∀ α ∈ T', ∀ β ∈ T', α ≠ β → Disjoint (F α) (F β) := by
    intro α hα β hβ hne
    apply Finset.disjoint_left.mpr
    intro c hc hd
    exact hne ((htype α c hc).symm.trans (htype β c hd))
  rw [← Finset.sum_biUnion hdis]
  exact (htensor.1.sum_le_tsum _ (fun c _ => mul_nonneg
    (SharpLSI.FL.Spectral.Lam_nonneg S.lam_nonneg c) (sq_nonneg _))).trans htensor.2

/-- Projection onto an actual occupation-energy sublevel misses at most `B/L` of the
square mass. The original a.e.-symmetric reference H1 test is retained. -/
theorem t01_reference_occupation_projection_tail (S : Spec d)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hC1 : ∀ j, SharpLSI.FL.Gross.C1T (S.v j))
    (hlam0 : S.lam 0 = 0) {Ψ : Config N d → ℝ}
    (hH : MemH1C (Measure.pi fun _ : Fin N => S.mu) Ψ)
    (hs : ∀ σ : Equiv.Perm (Fin N), (fun X => Ψ (X ∘ σ)) =ᵐ[
      Measure.pi (fun _ : Fin N => S.mu)] Ψ)
    {B : ℝ} (hB : (SharpLSI.FL.refEnergy S.mu Ψ).toReal ≤ B)
    {L : ℝ} (hL : 0 < L) (T : Finset (ℕ →₀ ℕ))
    (hT : ∀ α, occEnergy S.lam α ≤ L → α ∈ T) :
    ∫ X, (Ψ X - ∑ α ∈ T, (∫ Y, Ψ Y * occBasis S.v α N Y
      ∂Measure.pi (fun _ : Fin N => S.mu)) * occBasis S.v α N X) ^ 2
      ∂Measure.pi (fun _ : Fin N => S.mu) ≤ B / L := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  set P := Measure.pi fun _ : Fin N => S.mu
  set c : (ℕ →₀ ℕ) → ℝ := fun α => ∫ Y, Ψ Y * occBasis S.v α N Y ∂P
  have hΨL : MemLp Ψ 2 P := (measurableEmbedding_flat.memLp_map_measure_iff).mp hH.2.1
  have hBm : ∀ α, MemLp (occBasis S.v α N) 2 P := fun α => by
    unfold occBasis
    exact (memLp_finsetSum _ fun c _ => memLp_prod_eval fun i => he.memLp _).const_mul _
  set T' := T.filter fun α => occSize α ≤ N
  have hc0 : ∀ α, N < occSize α → c α = 0 := fun α h => by
    simp only [c, occBasis_zero_of_lt h, Pi.zero_apply, mul_zero, integral_zero]
  have hPS : (fun X => Ψ X - ∑ α ∈ T, c α * occBasis S.v α N X) =
      fun X => Ψ X - ∑ α ∈ T', c α * occBasis S.v α N X := by
    funext X
    congr 1
    refine (Finset.sum_subset (Finset.filter_subset _ T) fun α hα hα' => ?_).symm
    have : N < occSize α := by
      by_contra h; exact hα' (Finset.mem_filter.mpr ⟨hα, by omega⟩)
    rw [hc0 α this, zero_mul]
  have hPS2 : (fun X => (Ψ X - ∑ α ∈ T, c α * occBasis S.v α N X) ^ 2) =
      fun X => (Ψ X - ∑ α ∈ T', c α * occBasis S.v α N X) ^ 2 := by
    funext X; rw [congrFun hPS X]
  rw [hPS2]
  rw [integral_sub_sum_sq T' c hΨL hBm]
  have horthB : ∀ α ∈ T', ∀ β ∈ T', ∫ X, occBasis S.v α N X * occBasis S.v β N X ∂P =
      if α = β then 1 else 0 := fun α hα β hβ =>
    integral_occBasis_mul he.memLp he.orthonormal (Finset.mem_filter.mp hα).2
      (Finset.mem_filter.mp hβ).2
  have h3 : ∑ α ∈ T', ∑ β ∈ T', c α * c β * ∫ X, occBasis S.v α N X * occBasis S.v β N X ∂P =
      ∑ α ∈ T', c α ^ 2 := by
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Finset.sum_congr rfl fun β hβ => by rw [horthB α hα β hβ]]
    simp [Finset.sum_ite_eq, hα, sq]
  have h2 : ∑ α ∈ T', c α * ∫ X, Ψ X * occBasis S.v α N X ∂P = ∑ α ∈ T', c α ^ 2 :=
    Finset.sum_congr rfl fun α _ => by simp [c, sq]
  rw [h2, h3]
  -- Parseval and the energy bound for the tail
  have hpar := t01_hasSum_sq_reference_occupation S he hΨL hs
  have hsum := hpar.summable
  have hΛ : ∀ α, 0 ≤ occEnergy S.lam α := fun α =>
    Finset.sum_nonneg fun j _ => mul_nonneg (S.lam_nonneg _) (Nat.cast_nonneg _)
  have hEn : ∀ T0 : Finset (ℕ →₀ ℕ), ∑ α ∈ T0, occEnergy S.lam α * c α ^ 2 ≤ B :=
    fun T0 => (t01_reference_occupation_energy_bound S he hC1 hlam0 hH hs T0).trans hB
  have htail : ∀ α, (if α ∈ T' then 0 else c α ^ 2) ≤ occEnergy S.lam α * c α ^ 2 / L := fun α => by
    split_ifs with h
    · exact div_nonneg (mul_nonneg (hΛ α) (sq_nonneg _)) hL.le
    · by_cases hN : occSize α ≤ N
      · have hΛ : L < occEnergy S.lam α := by
          by_contra h'; exact h (Finset.mem_filter.mpr ⟨hT α (by linarith), hN⟩)
        rw [le_div_iff₀ hL]
        nlinarith [sq_nonneg (c α)]
      · rw [hc0 α (by omega)]; simp
  have hsplit : ∫ X, Ψ X ^ 2 ∂P - ∑ α ∈ T', c α ^ 2 = ∑' α, (if α ∈ T' then 0 else c α ^ 2) := by
    rw [← hpar.tsum_eq]
    have : ∀ α, c α ^ 2 = (if α ∈ T' then c α ^ 2 else 0) + (if α ∈ T' then 0 else c α ^ 2) :=
      fun α => by split_ifs <;> simp
    rw [tsum_congr this, Summable.tsum_add (summable_of_ne_finset_zero (s := T')
      fun α hα => by simp [hα]) (hsum.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
        fun α => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl), tsum_eq_sum (s := T') fun α hα => by simp [hα]]
    simp only [Finset.sum_ite_mem, Finset.inter_self]
    ring
  have hEsum : Summable fun α => occEnergy S.lam α * c α ^ 2 :=
    summable_of_sum_le (fun α => mul_nonneg (hΛ α) (sq_nonneg _)) hEn
  have hle : ∑' α, (if α ∈ T' then 0 else c α ^ 2) ≤ ∑' α, occEnergy S.lam α * c α ^ 2 / L :=
    Summable.tsum_le_tsum htail ((hsum.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
      fun α => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl)) (hEsum.div_const L)
  rw [tsum_div_const] at hle
  have hEt : ∑' α, occEnergy S.lam α * c α ^ 2 ≤ B :=
    Real.tsum_le_of_sum_le (fun α => mul_nonneg (hΛ α) (sq_nonneg _)) hEn
  have : ∫ X, Ψ X ^ 2 ∂P - 2 * ∑ α ∈ T', c α ^ 2 + ∑ α ∈ T', c α ^ 2 =
      ∫ X, Ψ X ^ 2 ∂P - ∑ α ∈ T', c α ^ 2 := by ring
  rw [this, hsplit]
  exact hle.trans (div_le_div_of_nonneg_right hEt hL.le)


/-- Positive physical modes with divergent ordered eigenvalues have finite occupation
energy sublevels. The zero coordinate is excluded by the legacy occupation indexing. -/
theorem t01_finite_occupation_energy_sublevel (S : Spec d) (hmono : Monotone S.lam)
    (hlam1 : 0 < S.lam 1) (htend : Tendsto S.lam atTop atTop) (L : ℝ) :
    {α : ℕ →₀ ℕ | occEnergy S.lam α ≤ L}.Finite := by
  obtain ⟨n0, hn0⟩ := (tendsto_atTop.mp htend (L + 1)).exists_forall_of_atTop
  let M := ⌈L / S.lam 1⌉₊
  refine ((Finset.range n0).finsupp fun _ => Finset.range (M + 1)).finite_toSet.subset ?_
  intro α hα
  have hterm : ∀ n ∈ α.support, S.lam (n + 1) * α n ≤ L := by
    intro n hn
    exact (Finset.single_le_sum (f := fun n => S.lam (n + 1) * (α n : ℝ))
      (fun m _ => mul_nonneg (S.lam_nonneg _) (Nat.cast_nonneg _)) hn).trans hα
  rw [Finset.mem_coe, Finset.mem_finsupp_iff]
  refine ⟨fun n hn => Finset.mem_range.mpr ?_, fun n _ => Finset.mem_range.mpr ?_⟩
  · by_contra h
    have h1 := hterm n hn
    have h2 := hn0 (n + 1) (by omega)
    have h3 : (1 : ℝ) ≤ α n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hn)
    have h4 : 0 < S.lam (n + 1) := hlam1.trans_le (hmono (by omega))
    nlinarith
  · by_cases hn : n ∈ α.support
    · have h1 := hterm n hn
      have h2 : S.lam 1 * α n ≤ L :=
        (mul_le_mul_of_nonneg_right (hmono (by omega)) (Nat.cast_nonneg _)).trans h1
      have h3 : (α n : ℝ) ≤ L / S.lam 1 := by
        rw [le_div_iff₀ hlam1]
        linarith
      have h4 : α n ≤ M := by exact_mod_cast h3.trans (Nat.le_ceil _)
      omega
    · rw [Finsupp.notMem_support_iff.mp hn]
      omega

/-- Strong compactness of the actual common-reference occupation coefficients and
Hermite synthesis of their limit. The only uniform bounds are mass and genuine H1 energy. -/
theorem t01_reference_occupation_compactness (S : Spec d)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hC1 : ∀ j, SharpLSI.FL.Gross.C1T (S.v j))
    (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1) (hmono : Monotone S.lam)
    (htend : Tendsto S.lam atTop atTop) (Ns : ℕ → ℕ)
    (Ψ : (n : ℕ) → Config (Ns n) d → ℝ)
    (hH : ∀ n, MemH1C (Measure.pi fun _ : Fin (Ns n) => S.mu) (Ψ n))
    (hs : ∀ n, ∀ σ : Equiv.Perm (Fin (Ns n)),
      (fun X => Ψ n (X ∘ σ)) =ᵐ[Measure.pi (fun _ : Fin (Ns n) => S.mu)] Ψ n)
    (B : ℝ)
    (hM : ∀ n, ∫ X, Ψ n X ^ 2 ∂Measure.pi (fun _ : Fin (Ns n) => S.mu) ≤ B)
    (hE : ∀ n, (SharpLSI.FL.refEnergy S.mu (Ψ n)).toReal ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ψinf : (ℕ → ℝ) → ℝ, MemLp Ψinf 2 gammaRef ∧
      Tendsto (fun k => ∑' α : ℕ →₀ ℕ, ENNReal.ofReal
        (((∫ X, Ψ (φ k) X * occBasis S.v α (Ns (φ k)) X
          ∂Measure.pi (fun _ : Fin (Ns (φ k)) => S.mu)) -
          ∫ z, Ψinf z * hermiteBasis α z ∂gammaRef) ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ X, Ψ (φ k) X ^ 2
        ∂Measure.pi (fun _ : Fin (Ns (φ k)) => S.mu)) atTop
        (𝓝 (∫ z, Ψinf z ^ 2 ∂gammaRef)) ∧
      (∀ α, Tendsto (fun k => ∫ X, Ψ (φ k) X * occBasis S.v α (Ns (φ k)) X
        ∂Measure.pi (fun _ : Fin (Ns (φ k)) => S.mu)) atTop
        (𝓝 (∫ z, Ψinf z * hermiteBasis α z ∂gammaRef))) ∧
      (∀ T : Finset (ℕ →₀ ℕ), ∑ α ∈ T, occEnergy S.lam α *
        (∫ z, Ψinf z * hermiteBasis α z ∂gammaRef) ^ 2 ≤ B) ∧
      HasSum (fun α => (∫ z, Ψinf z * hermiteBasis α z ∂gammaRef) ^ 2)
        (∫ z, Ψinf z ^ 2 ∂gammaRef) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hL : ∀ n, MemLp (Ψ n) 2 (Measure.pi fun _ : Fin (Ns n) => S.mu) := fun n =>
    (measurableEmbedding_flat.memLp_map_measure_iff).mp (hH n).2.1
  let x : ℕ → (ℕ →₀ ℕ) → ℝ := fun n α => ∫ X, Ψ n X * occBasis S.v α (Ns n) X
    ∂Measure.pi (fun _ : Fin (Ns n) => S.mu)
  have hp : ∀ n, HasSum (fun α => x n α ^ 2)
      (∫ X, Ψ n X ^ 2 ∂Measure.pi (fun _ : Fin (Ns n) => S.mu)) := fun n =>
    t01_hasSum_sq_reference_occupation S he (hL n) (hs n)
  have hB0 : 0 ≤ B := (integral_nonneg fun X => sq_nonneg (Ψ 0 X)).trans (hM 0)
  have hΛ : ∀ α, 0 ≤ occEnergy S.lam α := fun α =>
    Finset.sum_nonneg fun j _ => mul_nonneg (S.lam_nonneg _) (Nat.cast_nonneg _)
  have hx1 : ∀ n T, ∑ α ∈ T, x n α ^ 2 ≤ B := fun n T =>
    (sum_le_hasSum T (fun α _ => sq_nonneg _) (hp n)).trans (hM n)
  have hx2 : ∀ n T, ∑ α ∈ T, occEnergy S.lam α * x n α ^ 2 ≤ B := fun n T =>
    (t01_reference_occupation_energy_bound S he hC1 hlam0 (hH n) (hs n) T).trans (hE n)
  obtain ⟨φ, hφ, x0, hx01, hx02, hpt, hl2⟩ := exists_l2_subseq hΛ
    (t01_finite_occupation_energy_sublevel S hmono hlam1 htend) hB0 hx1 hx2
  obtain ⟨Ψinf, hΨinf, hcoef, hpar⟩ := exists_hermite_synthesis hx01
  refine ⟨φ, hφ, Ψinf, hΨinf, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hcoef] using hl2
  · rw [← hpar.tsum_eq]
    exact (tendsto_tsum_sq_of_l2 (fun n => (hp (φ n)).summable) hpar.summable hl2).congr
      (fun n => (hp (φ n)).tsum_eq)
  · intro α
    simpa only [hcoef] using hpt α
  · intro T
    simpa only [hcoef] using hx02 T
  · simpa only [hcoef] using hpar

end DGPS.Lipschitz
