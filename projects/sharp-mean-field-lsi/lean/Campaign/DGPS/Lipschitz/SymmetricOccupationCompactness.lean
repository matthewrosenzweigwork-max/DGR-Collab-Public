import DGPS.Lipschitz.SymmetricOccupation

/-!
# Common occupation coefficient compactness (LIP058)

On top of `DGPS.Lipschitz.occupation_basis_and_spectral_tail` (LIP057) we prove:

* the sublevels `{α : Λ_α ≤ L}` of the occupation eigenvalue `Λ_α = ∑_j λ_j α_j` are finite
  (`sublevel_finite_LIP058`), because `λ_1 > 0` bounds the occupation count and
  `λ_j → ∞` bounds the available labels;
* an abstract compactness lemma (`seqcompact_LIP058`): a sequence of real arrays on a countable
  set with uniformly bounded mass and uniformly bounded "energy" with respect to a weight with
  finite sublevels has a subsequence converging in `ℓ²` (coordinatewise extraction by Tychonoff
  and sequential compactness, upgraded by the uniform tail estimate);
* `DGPS.Lipschitz.common_occupation_coefficient_compactness`: the occupation coefficient
  arrays of a sequence of symmetric `Ψ_n ∈ H¹(𝕋^{d N_n})` with bounded masses and reference
  energies, extended by zero to the occupations that do not occur for `N_n` particles, form a
  sequence in the common space `ℓ²` of all finite occupation vectors, and a subsequence
  converges strongly there.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace Real

namespace DGPS.Lipschitz.SymmetricOccupationCompactness


theorem sublevel_finite_LIP058 (lam : ℕ → ℝ) (h0 : lam 0 = 0) (h01 : lam 0 < lam 1)
    (hmono : Monotone lam) (htend : Tendsto lam atTop atTop) (L : ℝ) :
    {a : {a : ℕ →₀ ℕ // a 0 = 0} | (a.1.sum fun j m => lam j * m) ≤ L}.Finite := by
  classical
  have hm : 0 < lam 1 := by rw [h0] at h01; exact h01
  have hnn : ∀ j, 0 ≤ lam j := fun j => by simpa [h0] using hmono (Nat.zero_le j)
  obtain ⟨J, hJ⟩ := (htend.eventually_gt_atTop L).exists_forall_of_atTop
  set K : ℕ := ⌊L / lam 1⌋₊ with hK
  let T : Finset (ℕ →₀ ℕ) :=
    (Finset.range (K + 1)).biUnion fun n => Finset.finsuppAntidiag (Finset.range J) n
  refine (T.finite_toSet.preimage Subtype.val_injective.injOn).subset ?_
  intro a ha
  simp only [Set.mem_ofPred_eq] at ha
  have hterm : ∀ j ∈ a.1.support, 1 ≤ a.1 j := fun j hj =>
    Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hj)
  have hj0 : ∀ j ∈ a.1.support, 1 ≤ j := fun j hj =>
    Nat.one_le_iff_ne_zero.2 (fun h => by
      have := hterm j hj; subst h; rw [a.2] at this; omega)
  have hsub : a.1.support ⊆ Finset.range J := by
    intro j hj
    rw [Finset.mem_range]
    by_contra hcon
    replace hcon := not_lt.1 hcon
    have h1 : lam j ≤ a.1.sum fun j m => lam j * m := by
      unfold Finsupp.sum
      calc lam j ≤ lam j * (a.1 j : ℝ) := by
            have : (1 : ℝ) ≤ a.1 j := by exact_mod_cast hterm j hj
            nlinarith [hnn j]
        _ ≤ _ := Finset.single_le_sum (f := fun j => lam j * (a.1 j : ℝ))
            (fun i _ => mul_nonneg (hnn i) (Nat.cast_nonneg _)) hj
    have := hJ j hcon
    linarith
  have hcnt : (a.1.sum fun _ m => m) ≤ K := by
    rw [hK]
    apply Nat.le_floor
    rw [le_div_iff₀ hm]
    have : lam 1 * ((a.1.sum fun _ m => m : ℕ) : ℝ) ≤ a.1.sum fun j m => lam j * m := by
      unfold Finsupp.sum
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have := hmono (hj0 j hj)
      have h2 : (0 : ℝ) ≤ a.1 j := Nat.cast_nonneg _
      nlinarith
    linarith
  simp only [Set.mem_preimage, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, T]
  refine ⟨a.1.sum fun _ m => m, ?_, ?_⟩
  · simpa [Finset.mem_range, Nat.lt_succ_iff] using hcnt
  · rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, hsub⟩
    exact (Finsupp.sum_of_support_subset a.1 hsub (fun _ m => m) (by simp)).symm


theorem seqcompact_LIP058 {ι : Type} [Countable ι] (Λ : ι → ℝ)
    (hfin : ∀ L : ℝ, {i | Λ i ≤ L}.Finite)
    (x : ℕ → ι → ℝ) (M E : ℝ) (hE : 0 ≤ E)
    (hM : ∀ n (F : Finset ι), ∑ i ∈ F, x n i ^ 2 ≤ M)
    (hT : ∀ n (L : ℝ), 0 < L → ∀ F : Finset ι, ∑ i ∈ F with L < Λ i, x n i ^ 2 ≤ E / L) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ι → ℝ, (∀ F : Finset ι, ∑ i ∈ F, y i ^ 2 ≤ M) ∧
      ∀ δ > 0, ∃ K, ∀ k ≥ K, ∀ F : Finset ι, ∑ i ∈ F, (x (φ k) i - y i) ^ 2 ≤ δ := by
  classical
  have hM0 : 0 ≤ M := by simpa using hM 0 ∅
  have hbd : ∀ n i, x n i ∈ Set.Icc (-Real.sqrt M) (Real.sqrt M) := by
    intro n i
    have h := hM n {i}
    simp only [Finset.sum_singleton] at h
    exact abs_le.1 (Real.abs_le_sqrt h)
  have hK : IsCompact (Set.univ.pi fun _ : ι => Set.Icc (-Real.sqrt M) (Real.sqrt M)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨y, -, φ, hφ, hlim⟩ := hK.tendsto_subseq
    (x := x) (fun n => Set.mem_univ_pi.2 (hbd n))
  have hpt : ∀ i, Tendsto (fun k => x (φ k) i) atTop (𝓝 (y i)) :=
    fun i => tendsto_pi_nhds.1 hlim i
  have hyM : ∀ F : Finset ι, ∑ i ∈ F, y i ^ 2 ≤ M := by
    intro F
    have ht : Tendsto (fun k => ∑ i ∈ F, x (φ k) i ^ 2) atTop (𝓝 (∑ i ∈ F, y i ^ 2)) :=
      tendsto_finsetSum _ fun i _ => (hpt i).pow 2
    exact le_of_tendsto ht (Eventually.of_forall fun k => hM _ F)
  have hyT : ∀ (L : ℝ), 0 < L → ∀ F : Finset ι, ∑ i ∈ F with L < Λ i, y i ^ 2 ≤ E / L := by
    intro L hL F
    have ht : Tendsto (fun k => ∑ i ∈ F with L < Λ i, x (φ k) i ^ 2) atTop
        (𝓝 (∑ i ∈ F with L < Λ i, y i ^ 2)) :=
      tendsto_finsetSum _ fun i _ => (hpt i).pow 2
    exact le_of_tendsto ht (Eventually.of_forall fun k => hT _ L hL F)
  refine ⟨φ, hφ, y, hyM, ?_⟩
  intro δ hδ
  set L : ℝ := 8 * E / δ + 1 with hLdef
  have hL : 0 < L := by positivity
  have hEL : 4 * (E / L) ≤ δ / 2 := by
    have : 8 * E ≤ δ * L := by
      rw [hLdef, mul_add, mul_div_cancel₀ _ hδ.ne']; linarith
    rw [← mul_div_assoc, div_le_iff₀ hL]
    linarith
  set S := (hfin L).toFinset with hS
  have hconv : Tendsto (fun k => ∑ i ∈ S, (x (φ k) i - y i) ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun k => ∑ i ∈ S, (x (φ k) i - y i) ^ 2) atTop (𝓝 (∑ i ∈ S, (y i - y i) ^ 2)) :=
      tendsto_finsetSum _ fun i _ => ((hpt i).sub tendsto_const_nhds).pow 2
    simpa using this
  obtain ⟨K, hK⟩ := (hconv.eventually (gt_mem_nhds (show (0:ℝ) < δ / 2 by positivity))).exists_forall_of_atTop
  refine ⟨K, fun k hk F => ?_⟩
  have h1 := hK k hk
  rw [← Finset.sum_filter_add_sum_filter_not F (fun i => L < Λ i)]
  have hA : ∑ i ∈ F with L < Λ i, (x (φ k) i - y i) ^ 2 ≤
      2 * (E / L) + 2 * (E / L) := by
    calc ∑ i ∈ F with L < Λ i, (x (φ k) i - y i) ^ 2
        ≤ ∑ i ∈ F with L < Λ i, (2 * x (φ k) i ^ 2 + 2 * y i ^ 2) :=
          Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (x (φ k) i + y i)]
      _ = 2 * ∑ i ∈ F with L < Λ i, x (φ k) i ^ 2 + 2 * ∑ i ∈ F with L < Λ i, y i ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by
          have := hT (φ k) L hL F
          have := hyT L hL F
          linarith
  have hB : ∑ i ∈ F with ¬ L < Λ i, (x (φ k) i - y i) ^ 2 ≤ ∑ i ∈ S, (x (φ k) i - y i) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => sq_nonneg _
    intro i hi
    simp only [Finset.mem_filter] at hi
    simp only [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact not_lt.1 hi.2
  linarith

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent
open DGPS.Lipschitz.SymmetricOccupation

/-- Extension by zero of an occupation array for `N` particles to the common index set of all
finite occupation vectors. -/
noncomputable def extendLIP058 {N : ℕ} (cf : Occ N → ℝ) (a : {a : ℕ →₀ ℕ // a 0 = 0}) : ℝ :=
  if h : (a.1.sum fun _ m => m) ≤ N then cf ⟨a.1, a.2, h⟩ else 0

theorem extend_apply_LIP058 {N : ℕ} (cf : Occ N → ℝ) (a : Occ N) :
    extendLIP058 cf ⟨a.1, a.2.1⟩ = cf a := by
  simp only [extendLIP058]
  simp [a.2.2]
  rfl

theorem extend_eq_zero_LIP058 {N : ℕ} (cf : Occ N → ℝ) {a : {a : ℕ →₀ ℕ // a 0 = 0}}
    (h : N < a.1.sum fun _ m => m) : extendLIP058 cf a = 0 := by
  simp [extendLIP058, not_le.2 h]

theorem hasSum_extend_LIP058 {N : ℕ} (cf : Occ N → ℝ) (wt : {a : ℕ →₀ ℕ // a 0 = 0} → ℝ)
    {s : ℝ} (h : HasSum (fun a : Occ N => wt ⟨a.1, a.2.1⟩ * cf a ^ 2) s) :
    HasSum (fun i => wt i * extendLIP058 cf i ^ 2) s := by
  have hinj : Function.Injective (fun a : Occ N => (⟨a.1, a.2.1⟩ : {a : ℕ →₀ ℕ // a 0 = 0})) :=
    fun a b hab => Subtype.ext (a1 := a) (a2 := b) (by
      have := congrArg Subtype.val hab
      simpa using this)
  refine (hinj.hasSum_iff (f := fun i => wt i * extendLIP058 cf i ^ 2) ?_).1 ?_
  · intro i hi
    have hlt : N < i.1.sum fun _ m => m := by
      by_contra hcon
      exact hi ⟨⟨i.1, i.2, not_lt.1 hcon⟩, rfl⟩
    simp [extend_eq_zero_LIP058 cf hlt]
  · simpa [Function.comp_def, extend_apply_LIP058] using h

end DGPS.Lipschitz.SymmetricOccupationCompactness

namespace DGPS.Lipschitz

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent
open DGPS.Lipschitz.SymmetricOccupation DGPS.Lipschitz.SymmetricOccupationCompactness

/-- LIP058.  **Common occupation coefficient compactness.**  With the data of
`occupation_basis_and_spectral_tail` (eigenvalues `lam`, complete orthonormal basis `ε` of
`L²(μ)`, `μ = w m`), every sublevel `{α : Λ_α ≤ L}` of `Λ_α = ∑_j lam j α_j` in the set of finite
occupation vectors `{a : ℕ →₀ ℕ // a 0 = 0}` is finite, and: for every sequence of particle
numbers `N_n` and of `μ^{N_n}`-a.e. symmetric `Ψ_n ∈ H¹(𝕋^{d N_n})` with
`‖Ψ_n‖² ≤ M` and `∫ ∑_i |∇_i Ψ_n|² dμ^{N_n} ≤ E`, the coefficient arrays
`x_n = (∫ Ψ_n E_{α,N_n} dμ^{N_n})_α`, extended by zero to the occupation vectors with more than
`N_n` particles, are elements of the common space `ℓ²` of all finite occupation vectors, and a
subsequence converges strongly in `ℓ²`. -/
theorem common_occupation_coefficient_compactness {d : ℕ} {w : Torus d → ℝ} {c C : ℝ}
    (hd : 0 < d) (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hint : ∫ x, w x ∂haar d = 1) :
    ∃ _ : IsProbabilityMeasure (wMeasure d w),
    ∃ (e : HilbertBasis ℕ ℝ (Hw d w)) (lam : ℕ → ℝ) (ε : ℕ → Torus d → ℝ),
      (lam 0 = 0 ∧ lam 0 < lam 1 ∧ Monotone lam ∧ Tendsto lam atTop atTop ∧
        ∀ j : ℕ, 1 ≤ j → 4 * π ^ 2 * c / (25 * C) * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j) ∧
      (∀ j, ε j =ᵐ[wMeasure d w] ((e j : Hw d w) : Torus d → ℝ)) ∧
      CompleteONB (wMeasure d w) ε ∧
      (∀ L : ℝ, {a : {a : ℕ →₀ ℕ // a 0 = 0} | (a.1.sum fun j m => lam j * m) ≤ L}.Finite) ∧
      ∀ (Nseq : ℕ → ℕ+) (Ψ : ∀ n, ParticleSpace d (Nseq n) → ℝ)
        (g : ∀ n, ParticleSpace d (Nseq n) → Fin (Nseq n) → Tangent d) (M E : ℝ),
        (∀ n, IsParticleHaarWeakGradient (Nseq n) (Ψ n) (g n)) →
        (∀ n, ∀ σ : Equiv.Perm (Fin (Nseq n : ℕ)),
          (fun ω => Ψ n (ω ∘ σ)) =ᵐ[Qm (wMeasure d w) (Nseq n : ℕ)] Ψ n) →
        (∀ n, ∫ ω, Ψ n ω ^ 2 ∂Qm (wMeasure d w) (Nseq n : ℕ) ≤ M) →
        (∀ n, ∫ ω, particleTangentNormSq (g n ω) ∂Qm (wMeasure d w) (Nseq n : ℕ) ≤ E) →
        ∃ x : ℕ → lp (fun _ : {a : ℕ →₀ ℕ // a 0 = 0} => ℝ) 2,
          (∀ n (a : Occ (Nseq n : ℕ)) (r : ℕ) (lab : Fin r → ℕ), (∀ l, lab l ≠ 0) →
            (∀ j, j ≠ 0 → Fintype.card {l : Fin r // lab l = j} = a.1 j) →
            x n ⟨a.1, a.2.1⟩ =
              ∫ ω, Ψ n ω * Eocc ε (Nseq n : ℕ) lab ω ∂Qm (wMeasure d w) (Nseq n : ℕ)) ∧
          (∀ n (a : {a : ℕ →₀ ℕ // a 0 = 0}), (Nseq n : ℕ) < (a.1.sum fun _ m => m) →
            x n a = 0) ∧
          ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x' : lp (fun _ : {a : ℕ →₀ ℕ // a 0 = 0} => ℝ) 2,
            Tendsto (fun k => x (φ k)) atTop (𝓝 x') := by
  classical
  obtain ⟨hP, e, lam, ε, ⟨hl0, hl01, hmono, htend, hgrow⟩, hεae, honb, hN⟩ :=
    occupation_basis_and_spectral_tail hd hw hc hwb hint
  refine ⟨hP, e, lam, ε, ⟨hl0, hl01, hmono, htend, hgrow⟩, hεae, honb,
    sublevel_finite_LIP058 lam hl0 hl01 hmono htend, ?_⟩
  intro Nseq Ψ g M E hg hsym hM hE
  have hex : ∀ n, ∃ cf : Occ (Nseq n : ℕ) → ℝ,
      (∀ (a : Occ (Nseq n : ℕ)) (r : ℕ) (lab : Fin r → ℕ), (∀ l, lab l ≠ 0) →
        (∀ j, j ≠ 0 → Fintype.card {l : Fin r // lab l = j} = a.1 j) →
        cf a = ∫ ω, Ψ n ω * Eocc ε (Nseq n : ℕ) lab ω ∂Qm (wMeasure d w) (Nseq n : ℕ)) ∧
      HasSum (fun a => cf a ^ 2) (∫ ω, Ψ n ω ^ 2 ∂Qm (wMeasure d w) (Nseq n : ℕ)) ∧
      HasSum (fun a => occLam lam a * cf a ^ 2)
        (∫ ω, particleTangentNormSq (g n ω) ∂Qm (wMeasure d w) (Nseq n : ℕ)) := by
    intro n
    obtain ⟨b, -, hb⟩ := hN (Nseq n)
    obtain ⟨cf, h1, h2, h3, -⟩ := hb (Ψ n) (g n) (hg n) (hsym n)
    exact ⟨cf, h1, h2, h3⟩
  choose cf hcf hmass henergy using hex
  -- the weight `Λ` on all finite occupation vectors
  let Λ : {a : ℕ →₀ ℕ // a 0 = 0} → ℝ := fun a => a.1.sum fun j m => lam j * m
  have hnn : ∀ j, 0 ≤ lam j := fun j => by simpa [hl0] using hmono (Nat.zero_le j)
  have hΛ0 : ∀ a, 0 ≤ Λ a := fun a =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hnn j) (Nat.cast_nonneg _)
  let X : ℕ → {a : ℕ →₀ ℕ // a 0 = 0} → ℝ := fun n => extendLIP058 (cf n)
  have hX1 : ∀ n, HasSum (fun i => X n i ^ 2) (∫ ω, Ψ n ω ^ 2 ∂Qm (wMeasure d w) (Nseq n : ℕ)) := by
    intro n
    have := hasSum_extend_LIP058 (cf n) (fun _ => 1) (by simpa using hmass n)
    simpa using this
  have hX2 : ∀ n, HasSum (fun i => Λ i * X n i ^ 2)
      (∫ ω, particleTangentNormSq (g n ω) ∂Qm (wMeasure d w) (Nseq n : ℕ)) := by
    intro n
    exact hasSum_extend_LIP058 (cf n) Λ (henergy n)
  have hEn : ∀ n, 0 ≤ ∫ ω, particleTangentNormSq (g n ω) ∂Qm (wMeasure d w) (Nseq n : ℕ) :=
    fun n => by
      simpa using sum_le_hasSum (∅ : Finset {a : ℕ →₀ ℕ // a 0 = 0})
        (fun i _ => mul_nonneg (hΛ0 i) (sq_nonneg _)) (hX2 n)
  have hE0 : 0 ≤ E := (hEn 0).trans (hE 0)
  have hfinsum : ∀ n (F : Finset {a : ℕ →₀ ℕ // a 0 = 0}), ∑ i ∈ F, X n i ^ 2 ≤ M := fun n F =>
    (sum_le_hasSum F (fun i _ => sq_nonneg _) (hX1 n)).trans (hM n)
  have htail : ∀ n (L : ℝ), 0 < L → ∀ F : Finset {a : ℕ →₀ ℕ // a 0 = 0},
      ∑ i ∈ F with L < Λ i, X n i ^ 2 ≤ E / L := by
    intro n L hL F
    rw [le_div_iff₀ hL, Finset.sum_mul]
    calc ∑ i ∈ F with L < Λ i, X n i ^ 2 * L ≤ ∑ i ∈ F with L < Λ i, Λ i * X n i ^ 2 :=
          Finset.sum_le_sum fun i hi => by
            have := (Finset.mem_filter.1 hi).2
            nlinarith [sq_nonneg (X n i)]
      _ ≤ ∑ i ∈ F, Λ i * X n i ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun i _ _ => mul_nonneg (hΛ0 i) (sq_nonneg _)
      _ ≤ _ := (sum_le_hasSum F (fun i _ => mul_nonneg (hΛ0 i) (sq_nonneg _)) (hX2 n)).trans
            (hE n)
  have hfin := sublevel_finite_LIP058 lam hl0 hl01 hmono htend
  obtain ⟨φ, hφ, y, hyM, hconv⟩ := seqcompact_LIP058 Λ hfin X M E hE0 hfinsum htail
  -- membership in `ℓ²`
  have hmem : ∀ f : {a : ℕ →₀ ℕ // a 0 = 0} → ℝ, ∀ B : ℝ, (∀ F : Finset _, ∑ i ∈ F, f i ^ 2 ≤ B) →
      Memℓp f 2 := by
    intro f B hB
    refine memℓp_gen' (C := B) fun F => ?_
    simpa [Real.norm_eq_abs, sq_abs] using hB F
  let x : ℕ → lp (fun _ : {a : ℕ →₀ ℕ // a 0 = 0} => ℝ) 2 := fun n =>
    ⟨X n, hmem (X n) M (hfinsum n)⟩
  let x' : lp (fun _ : {a : ℕ →₀ ℕ // a 0 = 0} => ℝ) 2 := ⟨y, hmem y M hyM⟩
  refine ⟨x, ?_, ?_, φ, hφ, x', ?_⟩
  · intro n a r lab hlab hcnt
    exact (extend_apply_LIP058 (cf n) a).trans (hcf n a r lab hlab hcnt)
  · intro n a ha
    exact extend_eq_zero_LIP058 (cf n) ha
  · rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
    intro η hη
    obtain ⟨K, hK⟩ := hconv ((η / 2) ^ 2) (by positivity)
    refine ⟨K, fun k hk => ?_⟩
    have hz : Memℓp (⇑(x (φ k) - x')) 2 := lp.memℓp _
    have hsq : ‖x (φ k) - x'‖ ^ 2 ≤ (η / 2) ^ 2 := by
      have hs : Summable fun i => (x (φ k) - x') i ^ 2 := by
        have := (memℓp_gen_iff (by simp)).1 hz
        simpa [Real.norm_eq_abs, sq_abs] using this
      have h1 : ‖x (φ k) - x'‖ ^ 2 = ∑' i, (x (φ k) - x') i ^ 2 := by
        have := lp.norm_rpow_eq_tsum (p := 2) (by simp) (x (φ k) - x')
        simpa [Real.norm_eq_abs, sq_abs] using this
      rw [h1]
      refine hs.tsum_le_of_sum_le fun F => ?_
      calc ∑ i ∈ F, (x (φ k) - x') i ^ 2 = ∑ i ∈ F, (X (φ k) i - y i) ^ 2 :=
            Finset.sum_congr rfl fun i _ => rfl
        _ ≤ (η / 2) ^ 2 := hK k hk F
    have : ‖x (φ k) - x'‖ ≤ η / 2 := le_of_sq_le_sq hsq (by positivity)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    linarith

end DGPS.Lipschitz
