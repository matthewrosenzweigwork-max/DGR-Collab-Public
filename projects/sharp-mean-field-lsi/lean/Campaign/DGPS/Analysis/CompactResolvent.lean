import DGPS.Analysis.WeightedForms

/-!
# Compact resolvent and semigroup construction (FOU009)

An abstract spectral layer for a closed form given as a Hilbert space `V` of finite form norm,
together with a compact, injective, densely ranged, contractive embedding `J : V → H`, followed by
the concrete adapter to the weighted form `E_w` on `L²(w m)`.
-/

namespace DGPS.Analysis.CompactResolvent

open scoped InnerProductSpace ENNReal
open Module.End Filter Topology MeasureTheory

section Eigen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_eigenbasis (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hs : (T : H →ₗ[ℝ] H).IsSymmetric) (hinj : Function.Injective T) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ H) (μ : ι → ℝ),
      (∀ j, T (b j) = μ j • b j) ∧ (∀ j, μ j ≠ 0) ∧ ∀ ε > 0, {j | ε ≤ |μ j|}.Finite := by
  classical
  have key : ∀ μ : ℝ, ∃ (n : ℕ) (v : Fin n → H), Orthonormal ℝ v ∧ (∀ i, T (v i) = μ • v i) ∧
      (μ ≠ 0 → Submodule.span ℝ (Set.range v) = eigenspace (T : Module.End ℝ H) μ) ∧
      (μ = 0 → n = 0) := by
    intro μ
    by_cases hμ : μ = 0
    · exact ⟨0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0,
        fun h => absurd hμ h, fun _ => rfl⟩
    · have := ContinuousLinearMap.finite_dimensional_eigenspace hc μ hμ
      let B := stdOrthonormalBasis ℝ (eigenspace (T : Module.End ℝ H) μ)
      refine ⟨_, fun i => (B i : H), ?_, ?_, ?_, fun h => absurd h hμ⟩
      · exact B.orthonormal.comp_linearIsometry (Submodule.subtypeₗᵢ _)
      · intro i
        exact mem_eigenspace_iff.mp (B i).2
      · intro _
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact (B i).2
        · intro x hx
          have h1 : (⟨x, hx⟩ : eigenspace (T : Module.End ℝ H) μ) ∈
              Submodule.span ℝ (Set.range B) := by
            have := B.toBasis.span_eq
            rw [OrthonormalBasis.coe_toBasis] at this
            rw [this]; trivial
          have h2 := Submodule.mem_map_of_mem (f := (eigenspace (T : Module.End ℝ H) μ).subtype) h1
          rw [← Submodule.span_image] at h2
          rw [← Set.range_comp] at h2
          exact h2
  choose n v hon heig hspan hn0 using key
  have hons : Orthonormal ℝ (fun a : (Σ μ : ℝ, Fin (n μ)) => v a.1 a.2) := by
    constructor
    · rintro ⟨μ, i⟩; exact (hon μ).1 i
    · rintro ⟨μ, i⟩ ⟨ν, k⟩ hne
      by_cases hμν : μ = ν
      · subst hμν
        have : i ≠ k := fun h => hne (by subst h; rfl)
        exact (hon μ).2 this
      · have h := hs (v μ i) (v ν k)
        simp only [ContinuousLinearMap.coe_coe, heig, real_inner_smul_left, real_inner_smul_right] at h
        have h' : (μ - ν) * ⟪v μ i, v ν k⟫_ℝ = 0 := by linarith
        rcases mul_eq_zero.mp h' with h0 | h0
        · exact absurd (sub_eq_zero.mp h0) hμν
        · exact h0
  have hcomp : (Submodule.span ℝ (Set.range (fun a : (Σ μ : ℝ, Fin (n μ)) => v a.1 a.2)))ᗮ = ⊥ := by
    have hle : (⨆ μ, eigenspace (T : Module.End ℝ H) μ) ≤
        Submodule.span ℝ (Set.range (fun a : (Σ μ : ℝ, Fin (n μ)) => v a.1 a.2)) := by
      refine iSup_le fun μ => ?_
      by_cases hμ : μ = 0
      · subst hμ
        have : eigenspace (T : Module.End ℝ H) 0 = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rw [mem_eigenspace_iff] at hx
          have : T x = T 0 := by simpa using hx
          have := hinj this
          simp [this]
        rw [this]; exact bot_le
      · rw [← hspan μ hμ]
        apply Submodule.span_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨⟨μ, i⟩, rfl⟩
    have := Submodule.orthogonal_le hle
    rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs] at this
    exact le_antisymm this bot_le
  refine ⟨Σ μ : ℝ, Fin (n μ), HilbertBasis.mkOfOrthogonalEqBot hons hcomp, fun a => a.1, ?_, ?_, ?_⟩
  · rintro ⟨μ, i⟩
    simp [heig]
  · rintro ⟨μ, i⟩ hμ
    simp only at hμ
    subst hμ
    have h0 := hn0 0 rfl
    have h2 := i.2
    omega
  · intro ε hε
    by_contra hinf
    have hS : Set.Infinite {j : (Σ μ : ℝ, Fin (n μ)) | ε ≤ |j.1|} := hinf
    let f := hS.natEmbedding
    let x : ℕ → H := fun m => v (f m).1.1 (f m).1.2
    have hxn : ∀ m, ‖x m‖ = 1 := fun m => hons.1 _
    have hmem : ∀ m, T (x m) ∈ closure (T '' Metric.closedBall 0 1) := fun m =>
      subset_closure ⟨x m, by simp [hxn m], rfl⟩
    obtain ⟨a, -, φ, hφ, hlim⟩ := (hc.isCompact_closure_image_closedBall 1).tendsto_subseq hmem
    have hcauchy := hlim.cauchySeq
    rw [Metric.cauchySeq_iff'] at hcauchy
    obtain ⟨N, hN⟩ := hcauchy ε hε
    have h1 := hN (N + 1) (by omega)
    have hne : (f (φ (N + 1))) ≠ f (φ N) := by
      intro h
      have := f.injective h
      have := hφ.injective this
      omega
    have hne' : (f (φ (N + 1))).1 ≠ (f (φ N)).1 := fun h => hne (Subtype.ext h)
    have horth := hons.2 hne'
    have hμ1 := (f (φ (N + 1))).2
    have hμ2 := (f (φ N)).2
    simp only [Set.mem_ofPred_eq] at hμ1 hμ2
    rw [dist_eq_norm] at h1
    have hTx : ∀ m, T (x m) = (f m).1.1 • x m := fun m => heig _ _
    simp only [Function.comp, hTx] at h1
    have hsq : ‖(f (φ (N + 1))).1.1 • x (φ (N + 1)) - (f (φ N)).1.1 • x (φ N)‖ ^ 2 =
        (f (φ (N + 1))).1.1 ^ 2 + (f (φ N)).1.1 ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
      have : ⟪x (φ (N + 1)), x (φ N)⟫_ℝ = 0 := horth
      rw [this, hxn, hxn]
      simp [sq_abs]
    have hε2 : ε ^ 2 ≤ (f (φ (N + 1))).1.1 ^ 2 := by
      rw [← sq_abs ((f (φ (N + 1))).1.1)]; exact pow_le_pow_left₀ hε.le hμ1 2
    have hε3 : ε ^ 2 ≤ (f (φ N)).1.1 ^ 2 := by
      rw [← sq_abs ((f (φ N)).1.1)]; exact pow_le_pow_left₀ hε.le hμ2 2
    have : ε ^ 2 < ‖(f (φ (N + 1))).1.1 • x (φ (N + 1)) - (f (φ N)).1.1 • x (φ N)‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_pos_of_pos hε]
    have := lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
    linarith

end Eigen
section Mult

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {ι : Type*} (b : HilbertBasis ι ℝ H)

theorem coeff_sq_summable (f : H) : Summable fun j => ⟪b j, f⟫_ℝ ^ 2 := by
  have := b.summable_inner_mul_inner f f
  refine this.congr fun j => ?_
  rw [real_inner_comm f (b j)]; ring

theorem tsum_coeff_sq (f : H) : ∑' j, ⟪b j, f⟫_ℝ ^ 2 = ‖f‖ ^ 2 := by
  have := b.tsum_inner_mul_inner f f
  rw [real_inner_self_eq_norm_sq] at this
  rw [← this]
  refine tsum_congr fun j => ?_
  rw [real_inner_comm f (b j)]; ring

theorem hasSum_coeff_mul (f g : H) : HasSum (fun j => ⟪b j, f⟫_ℝ * ⟪b j, g⟫_ℝ) ⟪f, g⟫_ℝ := by
  have := b.hasSum_inner_mul_inner f g
  convert this using 2 with j
  rw [real_inner_comm f (b j)]

theorem memℓp_two_of_sq_summable (c : ι → ℝ) (h : Summable fun j => c j ^ 2) : Memℓp c 2 := by
  apply memℓp_gen
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- The vector with prescribed square-summable coefficients. -/
noncomputable def ofSq (c : ι → ℝ) (h : Summable fun j => c j ^ 2) : H :=
  b.repr.symm ⟨c, memℓp_two_of_sq_summable c h⟩

theorem coeff_ofSq (c : ι → ℝ) (h : Summable fun j => c j ^ 2) (k : ι) :
    ⟪b k, ofSq b c h⟫_ℝ = c k := by
  rw [← b.repr_apply_apply]; simp [ofSq]

theorem ext_coeff {f g : H} (h : ∀ k, ⟪b k, f⟫_ℝ = ⟪b k, g⟫_ℝ) : f = g := by
  apply b.repr.injective
  apply lp.ext
  funext k
  simpa [b.repr_apply_apply] using h k

theorem norm_sq_ofSq (c : ι → ℝ) (h : Summable fun j => c j ^ 2) :
    ‖ofSq b c h‖ ^ 2 = ∑' j, c j ^ 2 := by
  rw [← tsum_coeff_sq b]
  exact tsum_congr fun j => by rw [coeff_ofSq]

theorem sq_mul_le (m : ι → ℝ) (M : ℝ) (hM : ∀ j, |m j| ≤ M) (j : ι) (x : ℝ) :
    (m j * x) ^ 2 ≤ M ^ 2 * x ^ 2 := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (sq_le_sq.mpr (by
    rw [abs_of_nonneg ((abs_nonneg _).trans (hM j))]; exact hM j)) (sq_nonneg _)

theorem sq_summable_mul (m : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) (f : H) :
    Summable fun j => (m j * ⟪b j, f⟫_ℝ) ^ 2 := by
  obtain ⟨M, hM⟩ := hm
  exact ((coeff_sq_summable b f).mul_left (M ^ 2)).of_nonneg_of_le (fun j => sq_nonneg _)
    (fun j => sq_mul_le m M hM j _)

/-- The diagonal ("multiplier") linear map `b j ↦ m j • b j`, for a bounded sequence `m`. -/
noncomputable def mulLin (m : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) : H →ₗ[ℝ] H where
  toFun f := ofSq b (fun j => m j * ⟪b j, f⟫_ℝ) (sq_summable_mul b m hm f)
  map_add' f g := by
    apply ext_coeff b; intro k
    simp only [coeff_ofSq, inner_add_right]; ring
  map_smul' r f := by
    apply ext_coeff b; intro k
    simp only [coeff_ofSq, inner_smul_right, RingHom.id_apply]; ring

/-- The diagonal ("multiplier") operator `b j ↦ m j • b j`, for a bounded sequence `m`. -/
noncomputable def mulOp (m : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) : H →L[ℝ] H :=
  LinearMap.mkContinuousOfExistsBound (mulLin b m hm) (by
    obtain ⟨M, hM⟩ := hm
    refine ⟨|M|, fun f => ?_⟩
    have h1 : ‖mulLin b m ⟨M, hM⟩ f‖ ^ 2 ≤ (|M| * ‖f‖) ^ 2 := by
      show ‖ofSq b (fun j => m j * ⟪b j, f⟫_ℝ) (sq_summable_mul b m ⟨M, hM⟩ f)‖ ^ 2 ≤ _
      rw [norm_sq_ofSq, mul_pow, sq_abs, ← tsum_coeff_sq b f, ← tsum_mul_left]
      exact (sq_summable_mul b m ⟨M, hM⟩ f).tsum_le_tsum
        (fun j => sq_mul_le m M hM j _) ((coeff_sq_summable b f).mul_left _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1)

theorem coeff_mulOp (m : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) (f : H) (k : ι) :
    ⟪b k, mulOp b m hm f⟫_ℝ = m k * ⟪b k, f⟫_ℝ := by
  exact coeff_ofSq b _ (sq_summable_mul b m hm f) k

theorem coeff_basis [DecidableEq ι] (j k : ι) : ⟪b j, b k⟫_ℝ = if j = k then 1 else 0 := by
  have := (orthonormal_iff_ite.mp b.orthonormal) j k
  simpa using this

theorem mulOp_basis (m : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) (k : ι) :
    mulOp b m hm (b k) = m k • b k := by
  classical
  apply ext_coeff b; intro j
  rw [coeff_mulOp, inner_smul_right, coeff_basis]
  by_cases h : j = k <;> simp [h]

theorem hasSum_inner_mulOp (m : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) (f g : H) :
    HasSum (fun j => m j * ⟪b j, f⟫_ℝ * ⟪b j, g⟫_ℝ) ⟪mulOp b m hm f, g⟫_ℝ := by
  have := hasSum_coeff_mul b (mulOp b m hm f) g
  simpa only [coeff_mulOp] using this

theorem inner_mulOp_comm (m : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) (f g : H) :
    ⟪mulOp b m hm f, g⟫_ℝ = ⟪f, mulOp b m hm g⟫_ℝ := by
  refine (hasSum_inner_mulOp b m hm f g).unique ?_
  have := hasSum_coeff_mul b f (mulOp b m hm g)
  simp only [coeff_mulOp] at this
  convert this using 2 with j
  ring

theorem mulOp_isSymmetric (m : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) :
    ((mulOp b m hm : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric := fun f g =>
  inner_mulOp_comm b m hm f g

theorem inner_mulOp_self_nonneg (m : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) (hpos : ∀ j, 0 ≤ m j)
    (f : H) : 0 ≤ ⟪mulOp b m hm f, f⟫_ℝ := by
  refine (hasSum_inner_mulOp b m hm f f).nonneg fun j => ?_
  have := mul_nonneg (hpos j) (mul_self_nonneg ⟪b j, f⟫_ℝ)
  linarith [this, show m j * ⟪b j, f⟫_ℝ * ⟪b j, f⟫_ℝ = m j * (⟪b j, f⟫_ℝ * ⟪b j, f⟫_ℝ) by ring]

theorem mulOp_mulOp (m m' : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) (hm' : ∃ M, ∀ j, |m' j| ≤ M)
    (hmm : ∃ M, ∀ j, |m j * m' j| ≤ M) (f : H) :
    mulOp b m hm (mulOp b m' hm' f) = mulOp b (fun j => m j * m' j) hmm f := by
  apply ext_coeff b; intro k
  simp only [coeff_mulOp]; ring

theorem mulOp_one (hm : ∃ M, ∀ j : ι, |(fun _ => (1 : ℝ)) j| ≤ M) (f : H) :
    mulOp b (fun _ => 1) hm f = f := by
  apply ext_coeff b; intro k
  simp [coeff_mulOp]

theorem mulOp_congr (m m' : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) (hm' : ∃ M, ∀ j, |m' j| ≤ M)
    (h : ∀ j, m j = m' j) (f : H) : mulOp b m hm f = mulOp b m' hm' f := by
  apply ext_coeff b; intro k
  simp [coeff_mulOp, h]

theorem norm_mulOp_le (m : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ j, |m j| ≤ M) (f : H) : ‖mulOp b m hm f‖ ≤ M * ‖f‖ := by
  have h1 : ‖mulOp b m hm f‖ ^ 2 ≤ (M * ‖f‖) ^ 2 := by
    rw [← tsum_coeff_sq b (mulOp b m hm f), mul_pow, ← tsum_coeff_sq b f, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) (coeff_sq_summable b _)
      ((coeff_sq_summable b f).mul_left _)
    rw [coeff_mulOp]
    exact sq_mul_le m M hM j _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

theorem mulOp_injective (m : ι → ℝ) (hm : ∃ M, ∀ j, |m j| ≤ M) (h0 : ∀ j, m j ≠ 0) :
    Function.Injective (mulOp b m hm) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply ext_coeff b; intro k
  have := congrArg (fun g => ⟪b k, g⟫_ℝ) hf
  simp only [coeff_mulOp, inner_zero_right, mul_eq_zero] at this
  simpa [(h0 k)] using this

/-- Coefficientwise convergence with a summable dominating bound gives convergence in `H`. -/
theorem tendsto_of_coeff {α : Type*} {F : Filter α} {f : α → H} {g : H}
    (hcoef : ∀ k, Tendsto (fun a => ⟪b k, f a⟫_ℝ) F (𝓝 ⟪b k, g⟫_ℝ))
    (bound : ι → ℝ) (hb : Summable bound)
    (hdom : ∀ᶠ a in F, ∀ k, (⟪b k, f a⟫_ℝ - ⟪b k, g⟫_ℝ) ^ 2 ≤ bound k) :
    Tendsto f F (𝓝 g) := by
  have h1 : Tendsto (fun a => ∑' k, (⟪b k, f a⟫_ℝ - ⟪b k, g⟫_ℝ) ^ 2) F (𝓝 (∑' k : ι, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := bound) hb (fun k => ?_) ?_
    · have := ((hcoef k).sub_const ⟪b k, g⟫_ℝ).pow 2
      simpa using this
    · filter_upwards [hdom] with a ha k
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact ha k
  simp only [tsum_zero] at h1
  have h2 : ∀ a, ∑' k, (⟪b k, f a⟫_ℝ - ⟪b k, g⟫_ℝ) ^ 2 = ‖f a - g‖ ^ 2 := by
    intro a
    rw [← tsum_coeff_sq b (f a - g)]
    exact tsum_congr fun k => by rw [inner_sub_right]
  simp only [h2] at h1
  have h3 : Tendsto (fun a => ‖f a - g‖) F (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this
    refine this.congr fun a => ?_
    simp [Real.sqrt_sq (norm_nonneg _)]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr h3

end Mult

section Form

section FormE

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Hypotheses on the form embedding `J : V → H`: here `V` is the form space (with the form norm
`‖x‖² = ‖J x‖² + E(x,x)`), contractively, injectively, densely and compactly embedded in `H`. -/
structure IsForm (J : V →L[ℝ] H) : Prop where
  norm_le : ∀ v, ‖J v‖ ≤ ‖v‖
  inj : Function.Injective J
  dense : DenseRange J
  compact : IsCompactOperator J

/-- The closed nonnegative form attached to the embedding: `E x y = ⟪x,y⟫_V - ⟪J x, J y⟫_H`. -/
def formE (J : V →L[ℝ] H) (x y : V) : ℝ := ⟪x, y⟫_ℝ - ⟪J x, J y⟫_ℝ

theorem formE_comm (J : V →L[ℝ] H) (x y : V) : formE J x y = formE J y x := by
  simp [formE, real_inner_comm]

theorem formE_add_right (J : V →L[ℝ] H) (x y z : V) :
    formE J x (y + z) = formE J x y + formE J x z := by
  simp only [formE, inner_add_right, map_add]; ring

theorem formE_smul_right (J : V →L[ℝ] H) (x y : V) (r : ℝ) :
    formE J x (r • y) = r * formE J x y := by
  simp only [formE, inner_smul_right, map_smul]; ring

theorem formE_add_left (J : V →L[ℝ] H) (x y z : V) :
    formE J (x + y) z = formE J x z + formE J y z := by
  simp only [formE, inner_add_left, map_add]; ring

theorem formE_nonneg {J : V →L[ℝ] H} (hJ : IsForm J) (x : V) : 0 ≤ formE J x x := by
  have := hJ.norm_le x
  simp only [formE, real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg (J x)]

end FormE

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The adjoint of the form embedding. -/
noncomputable abbrev adj (J : V →L[ℝ] H) : H →L[ℝ] V := ContinuousLinearMap.adjoint J

theorem adj_inner_left (J : V →L[ℝ] H) (y : H) (x : V) : ⟪adj J y, x⟫_ℝ = ⟪y, J x⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left J x y

theorem adj_inner_right (J : V →L[ℝ] H) (y : H) (x : V) : ⟪x, adj J y⟫_ℝ = ⟪J x, y⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_right J x y

section
open IsForm

variable {J : V →L[ℝ] H} (hJ : IsForm J)

include hJ in
theorem IsForm.eq_zero_of_adj_eq_zero {g : H} (h : adj J g = 0) : g = 0 := by
  have h1 : ∀ v, ⟪g, J v⟫_ℝ = 0 := fun v => by
    rw [← adj_inner_left, h, inner_zero_left]
  have h2 : ∀ y : H, ⟪g, y⟫_ℝ = 0 :=
    fun y => hJ.dense.induction_on y (isClosed_eq (continuous_const.inner continuous_id)
      continuous_const) h1
  simpa using h2 g

include hJ in
theorem IsForm.adj_injective : Function.Injective (adj J) := by
  rw [injective_iff_map_eq_zero]
  exact fun g hg => hJ.eq_zero_of_adj_eq_zero hg

theorem IsForm.isSymmetric_T : ((J.comp (adj J) : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  calc ⟪J (adj J x), y⟫_ℝ = ⟪adj J x, adj J y⟫_ℝ := (adj_inner_right J y (adj J x)).symm
    _ = ⟪adj J y, adj J x⟫_ℝ := real_inner_comm _ _
    _ = ⟪J (adj J y), x⟫_ℝ := adj_inner_right J x (adj J y)
    _ = ⟪x, J (adj J y)⟫_ℝ := real_inner_comm _ _

include hJ in
theorem IsForm.injective_T : Function.Injective (J.comp (adj J) : H →L[ℝ] H) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  have h1 : ‖adj J g‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, adj_inner_left]
    simpa using congrArg (fun z => ⟪g, z⟫_ℝ) hg
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h1
  exact hJ.eq_zero_of_adj_eq_zero (norm_eq_zero.mp this)

include hJ in
theorem IsForm.isCompactOperator_T : IsCompactOperator (J.comp (adj J) : H →L[ℝ] H) :=
  hJ.compact.comp_clm (adj J)

end

/-- The spectral data of `T = J J†`: a Hilbert basis of eigenvectors with eigenvalues `mu j ≠ 0`
whose superlevel sets away from zero are finite. -/
structure Spec (J : V →L[ℝ] H) where
  ι : Type
  b : HilbertBasis ι ℝ H
  mu : ι → ℝ
  eig : ∀ j, J (adj J (b j)) = mu j • b j
  ne : ∀ j, mu j ≠ 0
  fin : ∀ ε > 0, {j | ε ≤ |mu j|}.Finite

theorem IsForm.nonempty_spec {J : V →L[ℝ] H} (hJ : IsForm J) : Nonempty (Spec J) := by
  obtain ⟨ι, b, mu, h1, h2, h3⟩ := exists_eigenbasis (J.comp (adj J)) hJ.isCompactOperator_T
    (IsForm.isSymmetric_T (J := J)) hJ.injective_T
  exact ⟨⟨ι, b, mu, h1, h2, h3⟩⟩

section
open Spec

variable {J : V →L[ℝ] H} (S : Spec J)

/-- The form eigenvalue `λ j = μ j⁻¹ - 1`. -/
noncomputable def Spec.lam (j : S.ι) : ℝ := (S.mu j)⁻¹ - 1

theorem Spec.mu_eq (j : S.ι) : S.mu j = ‖adj J (S.b j)‖ ^ 2 := by
  have h1 : ⟪J (adj J (S.b j)), S.b j⟫_ℝ = ‖adj J (S.b j)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]; exact (adj_inner_right J (S.b j) (adj J (S.b j))).symm
  rw [S.eig j, real_inner_smul_left, real_inner_self_eq_norm_sq, (S.b.orthonormal.1 j)] at h1
  simpa using h1

theorem Spec.mu_pos (j : S.ι) : 0 < S.mu j :=
  lt_of_le_of_ne (by rw [S.mu_eq j]; positivity) (S.ne j).symm

theorem Spec.mu_le_one {J : V →L[ℝ] H} (S : Spec J) (hJ : IsForm J) (j : S.ι) : S.mu j ≤ 1 := by
  have h0 : 0 ≤ ‖adj J (S.b j)‖ := norm_nonneg _
  have h2 : ‖adj J (S.b j)‖ ^ 2 ≤ ‖adj J (S.b j)‖ * 1 := by
    calc ‖adj J (S.b j)‖ ^ 2 = ⟪J (adj J (S.b j)), S.b j⟫_ℝ := by
          rw [← real_inner_self_eq_norm_sq]; exact (adj_inner_right J (S.b j) (adj J (S.b j)))
      _ ≤ ‖J (adj J (S.b j))‖ * ‖S.b j‖ := real_inner_le_norm _ _
      _ ≤ ‖adj J (S.b j)‖ * 1 := by
          gcongr
          · exact hJ.norm_le _
          · exact (S.b.orthonormal.1 j).le
  have h1 : ‖adj J (S.b j)‖ ≤ 1 := by
    by_contra hlt
    push Not at hlt
    nlinarith
  rw [S.mu_eq j]
  exact pow_le_one₀ h0 h1

theorem Spec.lam_nonneg (hJ : IsForm J) (j : S.ι) : 0 ≤ S.lam j := by
  unfold lam
  have := (one_le_inv₀ (S.mu_pos j)).mpr (S.mu_le_one hJ j)
  linarith

theorem Spec.mu_inv (j : S.ι) : (S.mu j)⁻¹ = 1 + S.lam j := by
  unfold lam; ring

/-- The rescaled images `μ_j^{-1/2} J† b_j` of the eigenbasis. -/
noncomputable def Spec.wvec (j : S.ι) : V := (Real.sqrt (S.mu j))⁻¹ • adj J (S.b j)

theorem Spec.adj_eq_smul_wvec (j : S.ι) : adj J (S.b j) = Real.sqrt (S.mu j) • S.wvec j := by
  have : Real.sqrt (S.mu j) ≠ 0 := (Real.sqrt_pos.mpr (S.mu_pos j)).ne'
  rw [wvec, smul_smul, mul_inv_cancel₀ this, one_smul]

theorem Spec.inner_adj_basis [DecidableEq S.ι] (j k : S.ι) :
    ⟪adj J (S.b j), adj J (S.b k)⟫_ℝ = if j = k then S.mu j else 0 := by
  rw [adj_inner_right J (S.b k) (adj J (S.b j)), S.eig j, real_inner_smul_left, coeff_basis]
  by_cases h : j = k <;> simp [h]

theorem Spec.wvec_orthonormal : Orthonormal ℝ S.wvec := by
  classical
  rw [orthonormal_iff_ite]
  intro j k
  have hj : 0 < Real.sqrt (S.mu j) := Real.sqrt_pos.mpr (S.mu_pos j)
  have hk : 0 < Real.sqrt (S.mu k) := Real.sqrt_pos.mpr (S.mu_pos k)
  simp only [wvec, real_inner_smul_left, real_inner_smul_right, inner_adj_basis]
  by_cases h : j = k
  · subst h
    simp only [ite_true]
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt (S.mu_pos j).le]
    field_simp [(S.mu_pos j).ne']
  · simp [h]

theorem Spec.wvec_complete (hJ : IsForm J) :
    (Submodule.span ℝ (Set.range S.wvec))ᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_orthogonal] at hx
  have h1 : ∀ j, ⟪S.b j, J x⟫_ℝ = 0 := by
    intro j
    have := hx (S.wvec j) (Submodule.subset_span ⟨j, rfl⟩)
    rw [wvec, real_inner_smul_left, adj_inner_left] at this
    have hs : (Real.sqrt (S.mu j))⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr (S.mu_pos j)).ne'
    exact (mul_eq_zero.mp this).resolve_left hs
  have h2 : J x = 0 := ext_coeff S.b (fun k => by simpa using h1 k)
  have : x = 0 := hJ.inj (by simpa using h2)
  simp [this]

/-- The Hilbert basis of the form space `V` obtained from the eigenbasis. -/
noncomputable def Spec.bV (hJ : IsForm J) : HilbertBasis S.ι ℝ V :=
  HilbertBasis.mkOfOrthogonalEqBot S.wvec_orthonormal (S.wvec_complete hJ)

theorem Spec.bV_apply (hJ : IsForm J) (j : S.ι) : S.bV hJ j = S.wvec j := by
  have := HilbertBasis.coe_mkOfOrthogonalEqBot S.wvec_orthonormal (S.wvec_complete hJ)
  exact congrFun this j

theorem Spec.bV_coeff (hJ : IsForm J) (x : V) (j : S.ι) :
    ⟪S.bV hJ j, x⟫_ℝ = (Real.sqrt (S.mu j))⁻¹ * ⟪S.b j, J x⟫_ℝ := by
  rw [bV_apply, wvec, real_inner_smul_left, adj_inner_left]

theorem Spec.hasSum_inner_V (hJ : IsForm J) (x y : V) :
    HasSum (fun j => (S.mu j)⁻¹ * (⟪S.b j, J x⟫_ℝ * ⟪S.b j, J y⟫_ℝ)) ⟪x, y⟫_ℝ := by
  have := hasSum_coeff_mul (S.bV hJ) x y
  convert this using 2 with j
  rw [bV_coeff, bV_coeff]
  have : (S.mu j)⁻¹ = (Real.sqrt (S.mu j))⁻¹ * (Real.sqrt (S.mu j))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (S.mu_pos j).le]
  rw [this]; ring

theorem Spec.hasSum_formE (hJ : IsForm J) (x y : V) :
    HasSum (fun j => S.lam j * (⟪S.b j, J x⟫_ℝ * ⟪S.b j, J y⟫_ℝ)) (formE J x y) := by
  have := (S.hasSum_inner_V hJ x y).sub (hasSum_coeff_mul S.b (J x) (J y))
  convert this using 2 with j
  · unfold lam; ring
  · rfl

theorem Spec.summable_of_mem_range (hJ : IsForm J) (x : V) :
    Summable fun j => (S.mu j)⁻¹ * ⟪S.b j, J x⟫_ℝ ^ 2 := by
  refine (S.hasSum_inner_V hJ x x).summable.congr fun j => ?_
  ring

theorem Spec.exists_of_summable (hJ : IsForm J) (f : H)
    (hf : Summable fun j => (S.mu j)⁻¹ * ⟪S.b j, f⟫_ℝ ^ 2) : ∃ x, J x = f := by
  have hsq : ∀ j, ((Real.sqrt (S.mu j))⁻¹ * ⟪S.b j, f⟫_ℝ) ^ 2 = (S.mu j)⁻¹ * ⟪S.b j, f⟫_ℝ ^ 2 := by
    intro j
    rw [mul_pow, inv_pow, Real.sq_sqrt (S.mu_pos j).le]
  have hc : Summable fun j => ((Real.sqrt (S.mu j))⁻¹ * ⟪S.b j, f⟫_ℝ) ^ 2 := by
    simpa only [hsq] using hf
  refine ⟨ofSq (S.bV hJ) _ hc, ext_coeff S.b fun k => ?_⟩
  rw [← adj_inner_left, adj_eq_smul_wvec, real_inner_smul_left, ← bV_apply S hJ,
    coeff_ofSq]
  have : Real.sqrt (S.mu k) ≠ 0 := (Real.sqrt_pos.mpr (S.mu_pos k)).ne'
  field_simp

end

end Form

section Resolvent

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {J : V →L[ℝ] H} (S : Spec J)

section
open Spec

/-- The resolvent multiplier `(1 + h λ_j)⁻¹`. -/
noncomputable def Spec.resM (h : ℝ) (j : S.ι) : ℝ := (1 + h * S.lam j)⁻¹

theorem Spec.resM_pos (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) (j : S.ι) : 0 < S.resM h j := by
  have := S.lam_nonneg hJ j
  unfold resM; positivity

theorem Spec.resM_le_one (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) (j : S.ι) : S.resM h j ≤ 1 := by
  have := S.lam_nonneg hJ j
  unfold resM
  exact inv_le_one_of_one_le₀ (by nlinarith)

theorem Spec.resM_mul (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) (j : S.ι) :
    S.resM h j * (1 + h * S.lam j) = 1 := by
  have := S.lam_nonneg hJ j
  unfold resM
  exact inv_mul_cancel₀ (by positivity)

theorem Spec.resM_bdd (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) : ∃ M, ∀ j, |S.resM h j| ≤ M :=
  ⟨1, fun j => by rw [abs_of_pos (S.resM_pos hJ hh j)]; exact S.resM_le_one hJ hh j⟩

/-- The resolvent `R_h = (1 + h A)⁻¹`, as a diagonal operator in the eigenbasis. -/
noncomputable def Spec.resolvent (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) : H →L[ℝ] H :=
  mulOp S.b (S.resM h) (S.resM_bdd hJ hh)

theorem Spec.coeff_resolvent (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) (f : H) (k : S.ι) :
    ⟪S.b k, S.resolvent hJ hh f⟫_ℝ = S.resM h k * ⟪S.b k, f⟫_ℝ :=
  coeff_mulOp _ _ _ _ _

theorem Spec.resolvent_basis (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) (k : S.ι) :
    S.resolvent hJ hh (S.b k) = S.resM h k • S.b k :=
  mulOp_basis _ _ _ _

theorem Spec.resolvent_isSymmetric (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) :
    ((S.resolvent hJ hh : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric :=
  mulOp_isSymmetric _ _ _

theorem Spec.resolvent_pos (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) (f : H) :
    0 ≤ ⟪S.resolvent hJ hh f, f⟫_ℝ :=
  inner_mulOp_self_nonneg _ _ _ (fun j => (S.resM_pos hJ hh j).le) f

theorem Spec.resolvent_injective (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) :
    Function.Injective (S.resolvent hJ hh) :=
  mulOp_injective _ _ _ (fun j => (S.resM_pos hJ hh j).ne')

theorem Spec.norm_resolvent_le (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) (f : H) :
    ‖S.resolvent hJ hh f‖ ≤ ‖f‖ := by
  have := norm_mulOp_le S.b (S.resM h) (S.resM_bdd hJ hh) 1 zero_le_one
    (fun j => by rw [abs_of_pos (S.resM_pos hJ hh j)]; exact S.resM_le_one hJ hh j) f
  simpa [resolvent] using this

theorem Spec.resolvent_zero (hJ : IsForm J) (f : H) :
    S.resolvent hJ (le_refl (0 : ℝ)) f = f := by
  apply ext_coeff S.b; intro k
  rw [coeff_resolvent]
  simp [resM]

/-- The `T = J J†` operator is the diagonal operator with eigenvalues `μ_j`. -/
theorem Spec.T_eq_mulOp (hJ : IsForm J) (f : H) :
    J (adj J f) = mulOp S.b S.mu ⟨1, fun j => by
      rw [abs_of_pos (S.mu_pos j)]; exact S.mu_le_one hJ j⟩ f := by
  apply ext_coeff S.b; intro k
  rw [coeff_mulOp]
  have := (IsForm.isSymmetric_T (J := J)) (S.b k) f
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply] at this
  rw [← this, S.eig k, real_inner_smul_left, real_inner_comm]

end

end Resolvent

section Minimizer

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {J : V →L[ℝ] H} (S : Spec J)

section
open Spec

theorem Spec.one_add_lam_le (hJ : IsForm J) {h : ℝ} (hh : 0 < h) (j : S.ι) :
    (1 + S.lam j) * S.resM h j ≤ 1 + h⁻¹ := by
  have hl := S.lam_nonneg hJ j
  have hm := S.resM_pos hJ hh.le j
  have hm1 := S.resM_le_one hJ hh.le j
  have hmul := S.resM_mul hJ hh.le j
  have : 1 + S.lam j ≤ (1 + h⁻¹) * (1 + h * S.lam j) := by
    have : h⁻¹ * (h * S.lam j) = S.lam j := by field_simp
    nlinarith [inv_nonneg.mpr hh.le, mul_nonneg (inv_nonneg.mpr hh.le) hl]
  calc (1 + S.lam j) * S.resM h j ≤ (1 + h⁻¹) * (1 + h * S.lam j) * S.resM h j :=
        mul_le_mul_of_nonneg_right this hm.le
    _ = 1 + h⁻¹ := by rw [mul_assoc, mul_comm (1 + h * S.lam j), hmul, mul_one]

theorem Spec.exists_lift (hJ : IsForm J) {h : ℝ} (hh : 0 < h) (f : H) :
    ∃ x, J x = S.resolvent hJ hh.le f := by
  apply S.exists_of_summable hJ
  have hb := (coeff_sq_summable S.b f).mul_left (1 + h⁻¹)
  refine hb.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
  · have := S.mu_pos j
    positivity
  · rw [coeff_resolvent, S.mu_inv]
    have h1 := S.one_add_lam_le hJ hh j
    have hm1 := S.resM_le_one hJ hh.le j
    have hm := S.resM_pos hJ hh.le j
    have : (1 + S.lam j) * (S.resM h j * ⟪S.b j, f⟫_ℝ) ^ 2 =
        ((1 + S.lam j) * S.resM h j) * S.resM h j * ⟪S.b j, f⟫_ℝ ^ 2 := by ring
    rw [this]
    have h2 : ((1 + S.lam j) * S.resM h j) * S.resM h j ≤ (1 + h⁻¹) * 1 :=
      mul_le_mul h1 hm1 hm.le (by positivity)
    nlinarith [sq_nonneg ⟪S.b j, f⟫_ℝ]

/-- The Euler equation for the minimizer `x` with `J x = R_h f`. -/
theorem Spec.euler (hJ : IsForm J) {h : ℝ} (hh : 0 < h) (f : H) (x : V)
    (hx : J x = S.resolvent hJ hh.le f) (y : V) :
    ⟪J x - f, J y⟫_ℝ + h * formE J x y = 0 := by
  have h1 : HasSum (fun j => (⟪S.b j, J x⟫_ℝ - ⟪S.b j, f⟫_ℝ) * ⟪S.b j, J y⟫_ℝ)
      ⟪J x - f, J y⟫_ℝ := by
    have := hasSum_coeff_mul S.b (J x - f) (J y)
    simpa only [inner_sub_right] using this
  have h2 := (S.hasSum_formE hJ x y).mul_left h
  have h3 := h1.add h2
  refine h3.unique ?_
  have : (fun j => (⟪S.b j, J x⟫_ℝ - ⟪S.b j, f⟫_ℝ) * ⟪S.b j, J y⟫_ℝ +
      h * (S.lam j * (⟪S.b j, J x⟫_ℝ * ⟪S.b j, J y⟫_ℝ))) = fun _ => (0 : ℝ) := by
    funext j
    have hc : ⟪S.b j, J x⟫_ℝ = S.resM h j * ⟪S.b j, f⟫_ℝ := by rw [hx, coeff_resolvent]
    have hmul := S.resM_mul hJ hh.le j
    rw [hc]
    calc _ = (S.resM h j * (1 + h * S.lam j) - 1) * (⟪S.b j, f⟫_ℝ * ⟪S.b j, J y⟫_ℝ) := by ring
      _ = 0 := by rw [hmul]; ring
  rw [this]
  exact hasSum_zero

/-- The objective `‖J x - f‖² + h E(x,x)`. -/
noncomputable def Spec.obj (J : V →L[ℝ] H) (h : ℝ) (f : H) (x : V) : ℝ :=
  ‖J x - f‖ ^ 2 + h * formE J x x

theorem Spec.obj_sub_eq (hJ : IsForm J) {h : ℝ} (hh : 0 < h) (f : H) (x : V)
    (hx : J x = S.resolvent hJ hh.le f) (y : V) :
    obj J h f y = obj J h f x + (‖J (y - x)‖ ^ 2 + h * formE J (y - x) (y - x)) := by
  have he := S.euler hJ hh f x hx (y - x)
  have hy : y = x + (y - x) := by abel
  set z := y - x with hz
  have e1 : ‖J y - f‖ ^ 2 = ‖J z‖ ^ 2 + 2 * ⟪J x - f, J z⟫_ℝ + ‖J x - f‖ ^ 2 := by
    have : J y - f = J z + (J x - f) := by rw [hy]; simp [hz]
    rw [this, norm_add_sq_real, real_inner_comm]
  have e2 : formE J y y = formE J x x + 2 * formE J x z + formE J z z := by
    rw [hy]
    simp only [formE_add_right, formE_add_left, formE_comm J z x]
    ring
  unfold obj
  rw [e1, e2]
  nlinarith [he]

theorem Spec.obj_min (hJ : IsForm J) {h : ℝ} (hh : 0 < h) (f : H) (x : V)
    (hx : J x = S.resolvent hJ hh.le f) (y : V) : obj J h f x ≤ obj J h f y := by
  rw [S.obj_sub_eq hJ hh f x hx y]
  have := formE_nonneg hJ (y - x)
  nlinarith [sq_nonneg ‖J (y - x)‖]

theorem Spec.eq_of_obj_le (hJ : IsForm J) {h : ℝ} (hh : 0 < h) (f : H) (x : V)
    (hx : J x = S.resolvent hJ hh.le f) (y : V) (hy : obj J h f y ≤ obj J h f x) : y = x := by
  have := S.obj_sub_eq hJ hh f x hx y
  have h2 := formE_nonneg hJ (y - x)
  have h3 : ‖J (y - x)‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖J (y - x)‖]
  have h4 : J (y - x) = 0 := by simpa using h3
  have : y - x = 0 := hJ.inj (by simpa using h4)
  exact sub_eq_zero.mp this

include S in
/-- Unique minimizer of `‖J x - f‖² + h E(x,x)`, with `J x = R_h f`. -/
theorem Spec.existsUnique_minimizer (hJ : IsForm J) {h : ℝ} (hh : 0 < h) (f : H) :
    ∃! x : V, (∀ y, obj J h f x ≤ obj J h f y) := by
  obtain ⟨x, hx⟩ := S.exists_lift hJ hh f
  refine ⟨x, S.obj_min hJ hh f x hx, fun y hy => ?_⟩
  exact S.eq_of_obj_le hJ hh f x hx y (hy x)

theorem Spec.minimizer_iff (hJ : IsForm J) {h : ℝ} (hh : 0 < h) (f : H) (x : V) :
    (∀ y, obj J h f x ≤ obj J h f y) ↔ J x = S.resolvent hJ hh.le f := by
  obtain ⟨x0, hx0⟩ := S.exists_lift hJ hh f
  constructor
  · intro hmin
    have := S.eq_of_obj_le hJ hh f x0 hx0 x (hmin x0)
    rw [this, hx0]
  · intro hx
    exact S.obj_min hJ hh f x hx

/-- Compactness of the resolvent: `R_h = T ∘ N` with `T = J J†` compact and `N` bounded. -/
theorem Spec.resolvent_compact (hJ : IsForm J) {h : ℝ} (hh : 0 < h) :
    IsCompactOperator (S.resolvent hJ hh.le) := by
  have hN : ∃ M, ∀ j, |(1 + S.lam j) * S.resM h j| ≤ M := by
    refine ⟨1 + h⁻¹, fun j => ?_⟩
    rw [abs_of_nonneg (mul_nonneg (by linarith [S.lam_nonneg hJ j]) (S.resM_pos hJ hh.le j).le)]
    exact S.one_add_lam_le hJ hh j
  let N : H →L[ℝ] H := mulOp S.b (fun j => (1 + S.lam j) * S.resM h j) hN
  have hT : IsCompactOperator (J.comp (adj J) : H →L[ℝ] H) := hJ.isCompactOperator_T
  have : (J.comp (adj J)).comp N = S.resolvent hJ hh.le := by
    ext1 f
    apply ext_coeff S.b; intro k
    show ⟪S.b k, J (adj J (N f))⟫_ℝ = _
    rw [S.T_eq_mulOp hJ, coeff_mulOp, coeff_resolvent]
    show S.mu k * ⟪S.b k, mulOp S.b _ hN f⟫_ℝ = _
    have h1 : (1 + S.lam k) * S.mu k = 1 := by
      rw [← S.mu_inv]; exact inv_mul_cancel₀ (S.mu_pos k).ne'
    rw [coeff_mulOp, ← mul_assoc, ← mul_assoc, mul_comm (S.mu k), h1, one_mul]
  rw [← this]
  exact hT.comp_clm N

end

end Minimizer

section Generator

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {J : V →L[ℝ] H} (S : Spec J)

section
open Spec

/-- The domain of the generator: `Σ λ_j² ⟨e_j, f⟩² < ∞`. -/
def Spec.genDom : Submodule ℝ H where
  carrier := {f | Summable fun j => (S.lam j * ⟪S.b j, f⟫_ℝ) ^ 2}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    have hf' : Summable fun j => (S.lam j * ⟪S.b j, f⟫_ℝ) ^ 2 := hf
    have hg' : Summable fun j => (S.lam j * ⟪S.b j, g⟫_ℝ) ^ 2 := hg
    show Summable fun j => (S.lam j * ⟪S.b j, f + g⟫_ℝ) ^ 2
    refine ((hf'.mul_left 2).add (hg'.mul_left 2)).of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => ?_)
    simp only [inner_add_right]
    nlinarith [sq_nonneg (S.lam j * ⟪S.b j, f⟫_ℝ - S.lam j * ⟪S.b j, g⟫_ℝ)]
  smul_mem' := by
    intro r f hf
    have hf' : Summable fun j => (S.lam j * ⟪S.b j, f⟫_ℝ) ^ 2 := hf
    show Summable fun j => (S.lam j * ⟪S.b j, r • f⟫_ℝ) ^ 2
    refine (hf'.mul_left (r ^ 2)).congr fun j => ?_
    simp only [inner_smul_right]; ring

theorem Spec.mem_genDom {f : H} : f ∈ S.genDom ↔ Summable fun j => (S.lam j * ⟪S.b j, f⟫_ℝ) ^ 2 :=
  Iff.rfl

/-- The generator as a vector on its domain. -/
noncomputable def Spec.genFun (f : S.genDom) : H := ofSq S.b (fun j => S.lam j * ⟪S.b j, (f : H)⟫_ℝ) f.2

theorem Spec.coeff_genFun (f : S.genDom) (k : S.ι) :
    ⟪S.b k, S.genFun f⟫_ℝ = S.lam k * ⟪S.b k, (f : H)⟫_ℝ :=
  coeff_ofSq S.b _ _ k

/-- The form generator `A f = Σ λ_j ⟨e_j, f⟩ e_j` on its natural domain. -/
noncomputable def Spec.gen : H →ₗ.[ℝ] H where
  domain := S.genDom
  toFun :=
    { toFun := S.genFun
      map_add' := fun f g => by
        apply ext_coeff S.b; intro k
        rw [inner_add_right, coeff_genFun, coeff_genFun, coeff_genFun]
        simp only [Submodule.coe_add, inner_add_right]; ring
      map_smul' := fun r f => by
        apply ext_coeff S.b; intro k
        rw [inner_smul_right, coeff_genFun, coeff_genFun]
        simp only [Submodule.coe_smul, inner_smul_right, RingHom.id_apply]; ring }

theorem Spec.coeff_gen (f : S.gen.domain) (k : S.ι) :
    ⟪S.b k, S.gen f⟫_ℝ = S.lam k * ⟪S.b k, (f : H)⟫_ℝ :=
  S.coeff_genFun f k

theorem Spec.gen_domain : S.gen.domain = S.genDom := rfl

end

end Generator

section Generator2

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {J : V →L[ℝ] H} (S : Spec J)

section
open Spec

theorem Spec.b_mem_genDom (j : S.ι) : S.b j ∈ S.genDom := by
  classical
  rw [mem_genDom]
  have : (fun k => (S.lam k * ⟪S.b k, S.b j⟫_ℝ) ^ 2) = fun k => if k = j then S.lam j ^ 2 else 0 := by
    funext k
    rw [coeff_basis]
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  rw [this]
  exact (hasSum_ite_eq j (S.lam j ^ 2)).summable

theorem Spec.gen_basis (j : S.ι) : S.gen (⟨S.b j, S.b_mem_genDom j⟩ : S.gen.domain) = S.lam j • S.b j := by
  classical
  apply ext_coeff S.b; intro k
  rw [coeff_gen, inner_smul_right, coeff_basis]
  by_cases h : k = j
  · subst h; simp
  · simp [h]

theorem Spec.hasSum_gen_inner (f g : S.gen.domain) :
    HasSum (fun j => S.lam j * (⟪S.b j, (f : H)⟫_ℝ * ⟪S.b j, (g : H)⟫_ℝ)) ⟪S.gen f, (g : H)⟫_ℝ := by
  have := hasSum_coeff_mul S.b (S.gen f) (g : H)
  simp only [coeff_gen] at this
  convert this using 2 with j
  ring

theorem Spec.gen_symm (f g : S.gen.domain) : ⟪S.gen f, (g : H)⟫_ℝ = ⟪(f : H), S.gen g⟫_ℝ := by
  refine (S.hasSum_gen_inner f g).unique ?_
  have := hasSum_coeff_mul S.b (f : H) (S.gen g)
  simp only [coeff_gen] at this
  convert this using 2 with j
  ring

theorem Spec.gen_nonneg (hJ : IsForm J) (f : S.gen.domain) : 0 ≤ ⟪S.gen f, (f : H)⟫_ℝ := by
  refine (S.hasSum_gen_inner f f).nonneg fun j => ?_
  exact mul_nonneg (S.lam_nonneg hJ j) (mul_self_nonneg _)

theorem Spec.dense_genDom : Dense (S.gen.domain : Set H) := by
  have h1 : Dense ((Submodule.span ℝ (Set.range S.b) : Submodule ℝ H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact S.b.dense_span
  refine h1.mono ?_
  have : Submodule.span ℝ (Set.range S.b) ≤ S.genDom := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact S.b_mem_genDom j
  exact this

/-- The generator is self-adjoint. -/
theorem Spec.gen_selfAdjoint : IsSelfAdjoint S.gen := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hd := S.dense_genDom
  have hfa : LinearPMap.IsFormalAdjoint S.gen S.gen := fun x y => S.gen_symm x y
  apply le_antisymm
  · -- `A† ≤ A`
    have key : ∀ y : (LinearPMap.adjoint S.gen).domain, ∃ h : (y : H) ∈ S.genDom, S.gen ⟨y, h⟩ = LinearPMap.adjoint S.gen y := by
      intro y
      set w := LinearPMap.adjoint S.gen y with hw
      have hform := LinearPMap.adjoint_isFormalAdjoint hd y
      have hc : ∀ k, ⟪S.b k, w⟫_ℝ = S.lam k * ⟪S.b k, (y : H)⟫_ℝ := by
        intro k
        have := hform (⟨S.b k, S.b_mem_genDom k⟩ : S.gen.domain)
        have h2 : ⟪w, S.b k⟫_ℝ = ⟪(y : H), S.lam k • S.b k⟫_ℝ := by
          rw [← S.gen_basis k]; exact this
        rw [inner_smul_right] at h2
        rw [real_inner_comm, h2, real_inner_comm]
      have hs : Summable fun j => (S.lam j * ⟪S.b j, (y : H)⟫_ℝ) ^ 2 := by
        simpa only [← hc] using coeff_sq_summable S.b w
      refine ⟨hs, ?_⟩
      apply ext_coeff S.b; intro k
      rw [coeff_gen, hc]
    refine ⟨?_, ?_⟩
    · intro y hy
      obtain ⟨h, _⟩ := key ⟨y, hy⟩
      exact h
    · intro x y hxy
      obtain ⟨h, h2⟩ := key x
      have hy : (⟨(x : H), h⟩ : S.gen.domain) = y := Subtype.ext hxy
      rw [← h2]; exact congrArg S.gen hy
  · exact hfa.le_adjoint hd

end

end Generator2

section Generator3

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {J : V →L[ℝ] H} (S : Spec J)

section
open Spec

theorem Spec.mem_genDom_of_form (f : H) (x : V) (hx : J x = f) (g : H)
    (hg : ∀ y, formE J x y = ⟪g, J y⟫_ℝ) :
    ∃ h : f ∈ S.genDom, S.gen ⟨f, h⟩ = g := by
  have hc : ∀ k, ⟪S.b k, g⟫_ℝ = S.lam k * ⟪S.b k, f⟫_ℝ := by
    intro k
    have h1 := hg (adj J (S.b k))
    have hJy : J (adj J (S.b k)) = S.mu k • S.b k := S.eig k
    have e1 : formE J x (adj J (S.b k)) = (1 - S.mu k) * ⟪f, S.b k⟫_ℝ := by
      unfold formE
      rw [adj_inner_right, hJy, hx, real_inner_smul_right]; ring
    rw [e1, hJy, real_inner_smul_right] at h1
    have hmu := S.mu_pos k
    have : ⟪g, S.b k⟫_ℝ = S.lam k * ⟪f, S.b k⟫_ℝ := by
      unfold lam
      field_simp
      linarith
    rw [real_inner_comm, this, real_inner_comm]
  have hs : Summable fun j => (S.lam j * ⟪S.b j, f⟫_ℝ) ^ 2 := by
    simpa only [← hc] using coeff_sq_summable S.b g
  refine ⟨hs, ?_⟩
  apply ext_coeff S.b; intro k
  rw [coeff_gen, hc]

theorem Spec.exists_form_of_mem_gen_domain (hJ : IsForm J) (f : S.gen.domain) :
    ∃ x, J x = (f : H) ∧ ∀ y, formE J x y = ⟪S.gen f, J y⟫_ℝ := by
  have hf : Summable fun j => (S.lam j * ⟪S.b j, (f : H)⟫_ℝ) ^ 2 := f.2
  have hsum : Summable fun j => (S.mu j)⁻¹ * ⟪S.b j, (f : H)⟫_ℝ ^ 2 := by
    refine ((coeff_sq_summable S.b (f : H)).add hf).mul_left 2 |>.of_nonneg_of_le
      (fun j => ?_) (fun j => ?_)
    · have := S.mu_pos j
      positivity
    · rw [S.mu_inv]
      have hl := S.lam_nonneg hJ j
      nlinarith [sq_nonneg (S.lam j * ⟪S.b j, (f : H)⟫_ℝ - ⟪S.b j, (f : H)⟫_ℝ),
        sq_nonneg ⟪S.b j, (f : H)⟫_ℝ]
  obtain ⟨x, hx⟩ := S.exists_of_summable hJ (f : H) hsum
  refine ⟨x, hx, fun y => ?_⟩
  refine (S.hasSum_formE hJ x y).unique ?_
  have := hasSum_coeff_mul S.b (S.gen f) (J y)
  simp only [coeff_gen] at this
  convert this using 2 with j
  rw [hx]; ring

end

end Generator3

section Semigroup

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {J : V →L[ℝ] H} (S : Spec J)

section
open Spec

/-- The semigroup multiplier `exp (-t λ_j)`. -/
noncomputable def Spec.semiM (t : ℝ) (j : S.ι) : ℝ := Real.exp (-(t * S.lam j))

theorem Spec.semiM_pos (t : ℝ) (j : S.ι) : 0 < S.semiM t j := Real.exp_pos _

theorem Spec.semiM_le_one (hJ : IsForm J) {t : ℝ} (ht : 0 ≤ t) (j : S.ι) : S.semiM t j ≤ 1 := by
  unfold semiM
  rw [Real.exp_le_one_iff]
  have := mul_nonneg ht (S.lam_nonneg hJ j)
  linarith

theorem Spec.semiM_bdd (hJ : IsForm J) {t : ℝ} (ht : 0 ≤ t) : ∃ M, ∀ j, |S.semiM t j| ≤ M :=
  ⟨1, fun j => by rw [abs_of_pos (S.semiM_pos t j)]; exact S.semiM_le_one hJ ht j⟩

/-- The heat semigroup `S_t = exp (-t A)`, diagonal in the eigenbasis. -/
noncomputable def Spec.semigroup (hJ : IsForm J) (t : NNReal) : H →L[ℝ] H :=
  mulOp S.b (S.semiM t) (S.semiM_bdd hJ t.2)

theorem Spec.coeff_semigroup (hJ : IsForm J) (t : NNReal) (f : H) (k : S.ι) :
    ⟪S.b k, S.semigroup hJ t f⟫_ℝ = Real.exp (-(t * S.lam k)) * ⟪S.b k, f⟫_ℝ :=
  coeff_mulOp _ _ _ _ _

theorem Spec.semigroup_basis (hJ : IsForm J) (t : NNReal) (k : S.ι) :
    S.semigroup hJ t (S.b k) = Real.exp (-(t * S.lam k)) • S.b k :=
  mulOp_basis _ _ _ _

theorem Spec.semigroup_zero (hJ : IsForm J) (f : H) : S.semigroup hJ 0 f = f := by
  apply ext_coeff S.b; intro k
  rw [coeff_semigroup]; simp

theorem Spec.semigroup_add (hJ : IsForm J) (s t : NNReal) (f : H) :
    S.semigroup hJ (s + t) f = S.semigroup hJ s (S.semigroup hJ t f) := by
  apply ext_coeff S.b; intro k
  rw [coeff_semigroup, coeff_semigroup, coeff_semigroup, NNReal.coe_add, add_mul, neg_add,
    Real.exp_add]
  ring

theorem Spec.semigroup_isSymmetric (hJ : IsForm J) (t : NNReal) :
    ((S.semigroup hJ t : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric :=
  mulOp_isSymmetric _ _ _

theorem Spec.semigroup_pos (hJ : IsForm J) (t : NNReal) (f : H) :
    0 ≤ ⟪S.semigroup hJ t f, f⟫_ℝ :=
  inner_mulOp_self_nonneg _ _ _ (fun j => (S.semiM_pos t j).le) f

theorem Spec.norm_semigroup_le (hJ : IsForm J) (t : NNReal) (f : H) :
    ‖S.semigroup hJ t f‖ ≤ ‖f‖ := by
  have := norm_mulOp_le S.b (S.semiM t) (S.semiM_bdd hJ t.2) 1 zero_le_one
    (fun j => by rw [abs_of_pos (S.semiM_pos t j)]; exact S.semiM_le_one hJ t.2 j) f
  simpa [semigroup] using this

theorem Spec.semigroup_injective (hJ : IsForm J) (t : NNReal) : Function.Injective (S.semigroup hJ t) :=
  mulOp_injective _ _ _ (fun j => (S.semiM_pos t j).ne')

/-- The spectral formula `S_t f = Σ exp (-t λ_j) ⟨e_j, f⟩ e_j`. -/
theorem Spec.hasSum_semigroup (hJ : IsForm J) (t : NNReal) (f : H) :
    HasSum (fun j => (Real.exp (-(t * S.lam j)) * ⟪S.b j, f⟫_ℝ) • S.b j) (S.semigroup hJ t f) := by
  have := S.b.hasSum_repr (S.semigroup hJ t f)
  convert this using 3 with j
  rw [HilbertBasis.repr_apply_apply, coeff_semigroup]

end

end Semigroup
section SemigroupLimits

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {J : V →L[ℝ] H} (S : Spec J)

section
open Spec

/-- Strong continuity of the semigroup on `[0, ∞)`. -/
theorem Spec.semigroup_continuous (hJ : IsForm J) (f : H) :
    Continuous fun t : NNReal => S.semigroup hJ t f := by
  rw [continuous_iff_continuousAt]
  intro s
  refine tendsto_of_coeff S.b (fun k => ?_) (fun k => ⟪S.b k, f⟫_ℝ ^ 2)
    (coeff_sq_summable S.b f) (Filter.Eventually.of_forall fun t k => ?_)
  · simp only [coeff_semigroup]
    have : Continuous fun t : NNReal => Real.exp (-(t * S.lam k)) * ⟪S.b k, f⟫_ℝ := by fun_prop
    exact this.continuousAt
  · simp only [coeff_semigroup, ← sub_mul]
    rw [mul_pow]
    refine mul_le_of_le_one_left (sq_nonneg _) ?_
    have h1 : 0 < Real.exp (-((t : ℝ) * S.lam k)) := Real.exp_pos _
    have h2 : Real.exp (-((t : ℝ) * S.lam k)) ≤ 1 := S.semiM_le_one hJ t.2 k
    have h3 : 0 < Real.exp (-((s : ℝ) * S.lam k)) := Real.exp_pos _
    have h4 : Real.exp (-((s : ℝ) * S.lam k)) ≤ 1 := S.semiM_le_one hJ s.2 k
    rw [sq_le_one_iff_abs_le_one, abs_le]
    constructor <;> linarith

theorem Spec.tendsto_slope_exp (l : ℝ) :
    Filter.Tendsto (fun t : NNReal => ((t : ℝ))⁻¹ * (Real.exp (-(t * l)) - 1))
      (𝓝[≠] (0 : NNReal)) (𝓝 (-l)) := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (-(t * l))) (-l) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const l).neg.exp
    simpa using this
  have h1 := hd.tendsto_slope_zero_right
  have h2 : Filter.Tendsto (fun t : NNReal => (t : ℝ)) (𝓝[≠] (0 : NNReal)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
    · refine eventually_nhdsWithin_of_forall fun t ht => ?_
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  refine (h1.comp h2).congr fun t => ?_
  simp

theorem Spec.exp_sub_one_bounds {l : ℝ} (hl : 0 ≤ l) {t : ℝ} (ht : 0 < t) :
    -l ≤ t⁻¹ * (Real.exp (-(t * l)) - 1) ∧ t⁻¹ * (Real.exp (-(t * l)) - 1) ≤ 0 := by
  have h1 := Real.add_one_le_exp (-(t * l))
  have h2 : Real.exp (-(t * l)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  constructor
  · rw [← mul_le_mul_iff_of_pos_left ht, ← mul_assoc, mul_inv_cancel₀ ht.ne']
    nlinarith
  · exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) (by linarith)

/-- The generator is the strong right derivative at `0` of the semigroup on its domain. -/
theorem Spec.semigroup_hasDerivWithin_zero (hJ : IsForm J) (f : S.gen.domain) :
    Filter.Tendsto (fun t : NNReal => (t : ℝ)⁻¹ • (S.semigroup hJ t (f : H) - (f : H)))
      (𝓝[≠] (0 : NNReal)) (𝓝 (-S.gen f)) := by
  refine tendsto_of_coeff S.b (fun k => ?_) (fun k => (S.lam k * ⟪S.b k, (f : H)⟫_ℝ) ^ 2)
    (f.2 : Summable fun j => (S.lam j * ⟪S.b j, (f : H)⟫_ℝ) ^ 2) ?_
  · simp only [inner_smul_right, inner_sub_right, coeff_semigroup, inner_neg_right, coeff_gen]
    have := (tendsto_slope_exp (S.lam k)).mul_const ⟪S.b k, (f : H)⟫_ℝ
    rw [neg_mul] at this
    refine this.congr fun t => ?_
    ring
  · refine eventually_nhdsWithin_of_forall fun t ht k => ?_
    have htp : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
    simp only [inner_smul_right, inner_sub_right, coeff_semigroup, inner_neg_right, coeff_gen]
    obtain ⟨hb1, hb2⟩ := exp_sub_one_bounds (S.lam_nonneg hJ k) htp
    have e : ((t : ℝ)⁻¹ * (Real.exp (-((t : ℝ) * S.lam k)) * ⟪S.b k, (f : H)⟫_ℝ - ⟪S.b k, (f : H)⟫_ℝ)
        - -(S.lam k * ⟪S.b k, (f : H)⟫_ℝ))
        = ((t : ℝ)⁻¹ * (Real.exp (-((t : ℝ) * S.lam k)) - 1) + S.lam k) * ⟪S.b k, (f : H)⟫_ℝ := by ring
    rw [e, mul_pow, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [hb1, hb2]

end

end SemigroupLimits

section ProductFormula

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {J : V →L[ℝ] H} (S : Spec J)

section
open Spec

theorem Spec.coeff_resolvent_pow (hJ : IsForm J) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) (f : H) (k : S.ι) :
    ⟪S.b k, ((S.resolvent hJ hh) ^ n) f⟫_ℝ = S.resM h k ^ n * ⟪S.b k, f⟫_ℝ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    show ⟪S.b k, S.resolvent hJ hh (((S.resolvent hJ hh) ^ n) f)⟫_ℝ = _
    rw [coeff_resolvent, ih]
    ring

/-- The resolvent product formula `R_{t/n}^n f → S_t f`. -/
theorem Spec.tendsto_resolvent_pow (hJ : IsForm J) (t : NNReal) (f : H) :
    Tendsto (fun n : ℕ => ((S.resolvent hJ (h := (t : ℝ) / n)
      (div_nonneg t.2 (Nat.cast_nonneg n))) ^ n) f) atTop (𝓝 (S.semigroup hJ t f)) := by
  refine tendsto_of_coeff S.b (fun k => ?_) (fun k => ⟪S.b k, f⟫_ℝ ^ 2)
    (coeff_sq_summable S.b f) (Eventually.of_forall fun n k => ?_)
  · simp only [coeff_resolvent_pow, coeff_semigroup]
    refine Tendsto.mul_const _ ?_
    have h1 := Real.tendsto_one_add_div_pow_exp ((t : ℝ) * S.lam k)
    have h2 := (h1.inv₀ (Real.exp_pos _).ne')
    rw [← Real.exp_neg] at h2
    refine h2.congr fun n => ?_
    unfold resM
    rw [inv_pow]
    congr 3
    ring
  · rw [coeff_resolvent_pow, coeff_semigroup]
    have hm := S.resM_pos hJ (div_nonneg t.2 (Nat.cast_nonneg n)) k
    have hm1 := S.resM_le_one hJ (div_nonneg t.2 (Nat.cast_nonneg n)) k
    have hp : 0 < S.resM ((t : ℝ) / n) k ^ n := pow_pos hm n
    have hp1 : S.resM ((t : ℝ) / n) k ^ n ≤ 1 := pow_le_one₀ hm.le hm1
    have he := Real.exp_pos (-((t : ℝ) * S.lam k))
    have he1 : Real.exp (-((t : ℝ) * S.lam k)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have h0 := S.lam_nonneg hJ k
        have h2 : 0 ≤ (t : ℝ) * S.lam k := mul_nonneg t.2 h0
        linarith)
    rw [← sub_mul, mul_pow]
    calc _ ≤ 1 * ⟪S.b k, f⟫_ℝ ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
      _ = _ := one_mul _

end

end ProductFormula

section EnergyQuotient

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {J : V →L[ℝ] H} (S : Spec J)

section
open Spec

/-- The energy quotient `t⁻¹ (‖f‖² - ⟪S_t f, f⟫)`. -/
noncomputable def Spec.quot (hJ : IsForm J) (t : NNReal) (f : H) : ℝ :=
  (t : ℝ)⁻¹ * (‖f‖ ^ 2 - ⟪S.semigroup hJ t f, f⟫_ℝ)

theorem Spec.hasSum_quot (hJ : IsForm J) (t : NNReal) (f : H) :
    HasSum (fun j => (t : ℝ)⁻¹ * (1 - Real.exp (-(t * S.lam j))) * ⟪S.b j, f⟫_ℝ ^ 2)
      (S.quot hJ t f) := by
  have h1 := (hasSum_coeff_mul S.b f f).sub (hasSum_coeff_mul S.b (S.semigroup hJ t f) f)
  have h2 := h1.mul_left ((t : ℝ)⁻¹)
  unfold quot
  rw [← real_inner_self_eq_norm_sq]
  convert h2 using 1
  funext j
  rw [coeff_semigroup]
  ring

theorem Spec.quot_coeff_bounds (hJ : IsForm J) {t : ℝ} (ht : 0 < t) (j : S.ι) :
    0 ≤ t⁻¹ * (1 - Real.exp (-(t * S.lam j))) ∧
      t⁻¹ * (1 - Real.exp (-(t * S.lam j))) ≤ S.lam j := by
  obtain ⟨hb1, hb2⟩ := exp_sub_one_bounds (S.lam_nonneg hJ j) ht
  constructor <;> nlinarith

theorem Spec.tendsto_quot_of_mem_range (hJ : IsForm J) (x : V) :
    Tendsto (fun t : NNReal => S.quot hJ t (J x)) (𝓝[≠] (0 : NNReal))
      (𝓝 (formE J x x)) := by
  have hs := (S.hasSum_formE hJ x x)
  have hlim := tendsto_tsum_of_dominated_convergence
    (𝓕 := 𝓝[≠] (0 : NNReal))
    (f := fun (t : NNReal) (j : S.ι) =>
      (t : ℝ)⁻¹ * (1 - Real.exp (-(t * S.lam j))) * ⟪S.b j, J x⟫_ℝ ^ 2)
    (g := fun j => S.lam j * ⟪S.b j, J x⟫_ℝ ^ 2)
    (bound := fun j => S.lam j * (⟪S.b j, J x⟫_ℝ * ⟪S.b j, J x⟫_ℝ)) hs.summable
    (fun j => ?_) ?_
  · have e1 : ∀ t : NNReal, S.quot hJ t (J x) =
        ∑' j, (t : ℝ)⁻¹ * (1 - Real.exp (-(t * S.lam j))) * ⟪S.b j, J x⟫_ℝ ^ 2 :=
      fun t => ((S.hasSum_quot hJ t (J x)).tsum_eq).symm
    have e2 : formE J x x = ∑' j, S.lam j * ⟪S.b j, J x⟫_ℝ ^ 2 := by
      rw [← hs.tsum_eq]; congr 1; funext j; ring
    rw [e2]
    exact hlim.congr fun t => (e1 t).symm
  · have := ((tendsto_slope_exp (S.lam j)).neg).mul_const (⟪S.b j, J x⟫_ℝ ^ 2)
    simp only [neg_neg] at this
    refine this.congr fun t => ?_
    ring
  · refine eventually_nhdsWithin_of_forall fun t ht j => ?_
    have htp : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
    obtain ⟨h0, h1⟩ := S.quot_coeff_bounds hJ htp j
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc _ ≤ S.lam j * ⟪S.b j, J x⟫_ℝ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = _ := by ring

/-- If the energy quotients stay bounded as `t → 0+`, then `f` lies in the form domain. -/
theorem Spec.exists_of_quot_bdd (hJ : IsForm J) (f : H) (M : ℝ)
    (hM : ∀ᶠ t in 𝓝[≠] (0 : NNReal), S.quot hJ t f ≤ M) : ∃ x, J x = f := by
  have hsum : Summable fun j => S.lam j * ⟪S.b j, f⟫_ℝ ^ 2 := by
    refine summable_of_sum_le (c := M) (fun j => mul_nonneg (S.lam_nonneg hJ j) (sq_nonneg _))
      fun u => ?_
    have ht : Tendsto (fun t : NNReal => ∑ j ∈ u,
        (t : ℝ)⁻¹ * (1 - Real.exp (-(t * S.lam j))) * ⟪S.b j, f⟫_ℝ ^ 2)
        (𝓝[≠] (0 : NNReal)) (𝓝 (∑ j ∈ u, S.lam j * ⟪S.b j, f⟫_ℝ ^ 2)) := by
      refine tendsto_finsetSum _ fun j _ => ?_
      have := ((tendsto_slope_exp (S.lam j)).neg).mul_const (⟪S.b j, f⟫_ℝ ^ 2)
      simp only [neg_neg] at this
      refine this.congr fun t => ?_
      ring
    refine le_of_tendsto ht ?_
    filter_upwards [hM, self_mem_nhdsWithin] with t htM htne
    have htp : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr htne)
    refine le_trans ?_ htM
    exact sum_le_hasSum u (fun j _ => by
      obtain ⟨h0, _⟩ := S.quot_coeff_bounds hJ htp j
      positivity) (S.hasSum_quot hJ t f)
  refine S.exists_of_summable hJ f ?_
  refine ((coeff_sq_summable S.b f).add hsum).congr fun j => ?_
  rw [S.mu_inv]; ring

end

end EnergyQuotient

section Construction

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The conclusion of the abstract compact-resolvent and semigroup construction for the form
`(V, J)`, where `J : V → H` is a compact, injective, densely ranged contraction of the form Hilbert
space `V` (`‖x‖_V² = ‖J x‖² + E(x,x)`). -/
def ConstructionStmt (J : V →L[ℝ] H) : Prop :=
    ∃ (ι : Type) (b : HilbertBasis ι ℝ H) (lam : ι → ℝ)
      (R : ℝ → H →L[ℝ] H) (T : NNReal → H →L[ℝ] H) (A : H →ₗ.[ℝ] H),
      (∀ i, 0 ≤ lam i) ∧
      -- unique minimizer, resolvent
      (∀ h : ℝ, 0 < h → ∀ f : H, (∃! x : V, ∀ y, Spec.obj J h f x ≤ Spec.obj J h f y) ∧
        ∀ x : V, (∀ y, Spec.obj J h f x ≤ Spec.obj J h f y) → J x = R h f) ∧
      (∀ h : ℝ, 0 < h → ((R h : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric ∧
        (∀ f, 0 ≤ ⟪R h f, f⟫_ℝ) ∧ Function.Injective (R h) ∧ IsCompactOperator (R h) ∧
        (∀ f, ‖R h f‖ ≤ ‖f‖)) ∧
      (∀ h : ℝ, 0 < h → ∀ i, R h (b i) = (1 + h * lam i)⁻¹ • b i) ∧
      -- generator
      IsSelfAdjoint A ∧ Dense (A.domain : Set H) ∧ (∀ f : A.domain, 0 ≤ ⟪A f, (f : H)⟫_ℝ) ∧
      (∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = lam i • b i) ∧
      (∀ f : A.domain, ∃ x : V, J x = (f : H) ∧ ∀ y, formE J x y = ⟪A f, J y⟫_ℝ) ∧
      (∀ (x : V) (g : H), (∀ y, formE J x y = ⟪g, J y⟫_ℝ) →
        ∃ hx : J x ∈ A.domain, A ⟨J x, hx⟩ = g) ∧
      -- semigroup
      (∀ (t : NNReal) f, HasSum (fun i => (Real.exp (-(t * lam i)) * ⟪b i, f⟫_ℝ) • b i) (T t f)) ∧
      (∀ f, T 0 f = f) ∧ (∀ (s t : NNReal) f, T (s + t) f = T s (T t f)) ∧
      (∀ t : NNReal, ((T t : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric) ∧
      (∀ (t : NNReal) f, 0 ≤ ⟪T t f, f⟫_ℝ) ∧ (∀ (t : NNReal) f, ‖T t f‖ ≤ ‖f‖) ∧
      (∀ f, Continuous fun t : NNReal => T t f) ∧
      (∀ f : A.domain, Tendsto (fun t : NNReal => (t : ℝ)⁻¹ • (T t (f : H) - (f : H)))
        (𝓝[≠] (0 : NNReal)) (𝓝 (-A f))) ∧
      -- the form is the closed energy of the semigroup
      (∀ x : V, Tendsto (fun t : NNReal => (t : ℝ)⁻¹ * (‖J x‖ ^ 2 - ⟪T t (J x), J x⟫_ℝ))
        (𝓝[≠] (0 : NNReal)) (𝓝 (formE J x x))) ∧
      (∀ (f : H) (M : ℝ), (∀ᶠ t : NNReal in 𝓝[≠] (0 : NNReal),
          (t : ℝ)⁻¹ * (‖f‖ ^ 2 - ⟪T t f, f⟫_ℝ) ≤ M) → ∃ x : V, J x = f) ∧
      -- product formula
      (∀ (t : NNReal) (f : H), Tendsto (fun n : ℕ => ((R ((t : ℝ) / n)) ^ n) f) atTop
        (𝓝 (T t f))) 

theorem construction {J : V →L[ℝ] H} (hJ : IsForm J) : ConstructionStmt J := by
  unfold ConstructionStmt
  obtain ⟨S⟩ := hJ.nonempty_spec
  classical
  refine ⟨S.ι, S.b, S.lam, fun h => if hh : 0 ≤ h then S.resolvent hJ hh else 0,
    S.semigroup hJ, S.gen, S.lam_nonneg hJ, ?_, ?_, ?_, S.gen_selfAdjoint, S.dense_genDom,
    S.gen_nonneg hJ, ?_, S.exists_form_of_mem_gen_domain hJ, ?_, S.hasSum_semigroup hJ,
    S.semigroup_zero hJ, S.semigroup_add hJ, S.semigroup_isSymmetric hJ, S.semigroup_pos hJ,
    S.norm_semigroup_le hJ, S.semigroup_continuous hJ, S.semigroup_hasDerivWithin_zero hJ,
    ?_, ?_, ?_⟩
  · intro h hh f
    refine ⟨S.existsUnique_minimizer hJ hh f, fun x hx => ?_⟩
    simp only [hh.le, ↓reduceDIte]
    exact (S.minimizer_iff hJ hh f x).mp hx
  · intro h hh
    simp only [hh.le, ↓reduceDIte]
    exact ⟨S.resolvent_isSymmetric hJ hh.le, S.resolvent_pos hJ hh.le,
      S.resolvent_injective hJ hh.le, S.resolvent_compact hJ hh, S.norm_resolvent_le hJ hh.le⟩
  · intro h hh i
    simp only [hh.le, ↓reduceDIte]
    exact mulOp_basis _ _ _ _
  · exact fun i => ⟨S.b_mem_genDom i, S.gen_basis i⟩
  · intro x g hg
    exact S.mem_genDom_of_form (J x) x rfl g hg
  · intro x
    exact S.tendsto_quot_of_mem_range hJ x
  · intro f M hM
    exact S.exists_of_quot_bdd hJ f M hM
  · intro t f
    refine (S.tendsto_resolvent_pow hJ t f).congr fun n => ?_
    have hc : (0 : ℝ) ≤ (t : ℝ) / n := div_nonneg t.2 (Nat.cast_nonneg n)
    have e : (if hh : 0 ≤ (t : ℝ) / n then S.resolvent hJ hh else 0) = S.resolvent hJ hc := by
      simp [hc]
    show _ = ((if hh : 0 ≤ (t : ℝ) / n then S.resolvent hJ hh else 0) ^ n) f
    rw [e]

end Construction


section WMeasure

open DGPS

variable {d : ℕ}

/-- The weighted measure `w m` on the torus. -/
noncomputable def wMeasure (d : ℕ) (w : Torus d → ℝ) : Measure (Torus d) :=
  (haar d).withDensity fun x => ENNReal.ofReal (w x)

variable {w : Torus d → ℝ} {c C : ℝ}

theorem wMeasure_le (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    wMeasure d w ≤ ENNReal.ofReal C • haar d := by
  rw [← withDensity_const]
  refine withDensity_mono ?_
  filter_upwards [hwb] with x hx
  exact ENNReal.ofReal_le_ofReal hx.2

theorem wMeasure_ge (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    ENNReal.ofReal c • haar d ≤ wMeasure d w := by
  rw [← withDensity_const]
  refine withDensity_mono ?_
  filter_upwards [hwb] with x hx
  exact ENNReal.ofReal_le_ofReal hx.1

theorem memLp_wMeasure_iff (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    {E : Type*} [NormedAddCommGroup E] {f : Torus d → E} {p : ℝ≥0∞} :
    MemLp f p (wMeasure d w) ↔ MemLp f p (haar d) := by
  constructor
  · intro h
    have h1 : MemLp f p (ENNReal.ofReal c • haar d) := h.mono_measure (wMeasure_ge hwb)
    have h2 := h1.smul_measure (c := (ENNReal.ofReal c)⁻¹)
      (ENNReal.inv_ne_top.mpr (by simpa using hc))
    rwa [smul_smul, ENNReal.inv_mul_cancel (by simpa using hc) ENNReal.ofReal_ne_top,
      one_smul] at h2
  · intro h
    exact (h.smul_measure (c := ENNReal.ofReal C) ENNReal.ofReal_ne_top).mono_measure
      (wMeasure_le hwb)

theorem haar_ac_wMeasure (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    haar d ≪ wMeasure d w := by
  intro s hs
  have := wMeasure_ge hwb s
  rw [hs] at this
  have h2 : (ENNReal.ofReal c • haar d) s = 0 := le_antisymm this zero_le
  simp only [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 (by simpa using hc)
  · exact h2

theorem wMeasure_ac_haar : wMeasure d w ≪ haar d :=
  withDensity_absolutelyContinuous _ _

theorem ae_wMeasure_iff (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    {P : Torus d → Prop} : (∀ᵐ x ∂wMeasure d w, P x) ↔ ∀ᵐ x ∂haar d, P x :=
  ⟨fun h => (haar_ac_wMeasure hc hwb).ae_le h, fun h => wMeasure_ac_haar.ae_le h⟩

theorem ae_eq_haar (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    {E : Type*} {f g : Torus d → E} (h : f =ᵐ[wMeasure d w] g) : f =ᵐ[haar d] g :=
  (haar_ac_wMeasure hc hwb).ae_le h

theorem ae_eq_wMeasure {E : Type*} {f g : Torus d → E} (h : f =ᵐ[haar d] g) :
    f =ᵐ[wMeasure d w] g :=
  wMeasure_ac_haar.ae_le h

end WMeasure

section WIntegral

open DGPS

variable {d : ℕ} {w : Torus d → ℝ} {c C : ℝ}

theorem integral_wMeasure (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : Torus d → E) :
    ∫ x, φ x ∂wMeasure d w = ∫ x, w x • φ x ∂haar d := by
  unfold wMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hwb] with x hx
  rw [ENNReal.toReal_ofReal (hc.le.trans hx.1)]

theorem inner_Lp_wMeasure (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : Lp E 2 (wMeasure d w)) :
    ⟪a, b⟫_ℝ = ∫ x, ⟪(a : Torus d → E) x, (b : Torus d → E) x⟫_ℝ * w x ∂haar d := by
  rw [L2.inner_def, integral_wMeasure hw hc hwb]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [mul_comm]

end WIntegral

section Space

open DGPS

variable (d : ℕ) (w : Torus d → ℝ)

/-- The Hilbert space `L²(w m)`. -/
noncomputable abbrev Hw := Lp ℝ 2 (wMeasure d w)

/-- Vector fields in `L²(w m; ℝ^d)`. -/
noncomputable abbrev Gw := Lp (Tangent d) 2 (wMeasure d w)

/-- The ambient Hilbert space `L²(w m) × L²(w m; ℝ^d)` with the `ℓ²`-product norm. -/
noncomputable abbrev Amb := WithLp 2 (Hw d w × Gw d w)

variable {d w} {c C : ℝ}

theorem norm_sq_Hw (hw : Measurable w) (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (a : Hw d w) : ‖a‖ ^ 2 = ∫ x, (a : Torus d → ℝ) x ^ 2 * w x ∂haar d := by
  rw [← real_inner_self_eq_norm_sq, inner_Lp_wMeasure hw hc hwb]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq]

theorem norm_sq_Gw (hw : Measurable w) (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (a : Gw d w) : ‖a‖ ^ 2 = ∫ x, ‖(a : Torus d → Tangent d) x‖ ^ 2 * w x ∂haar d := by
  rw [← real_inner_self_eq_norm_sq, inner_Lp_wMeasure hw hc hwb]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp

theorem norm_sq_Amb (hw : Measurable w) (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (p : Amb d w) : ‖p‖ ^ 2 = ∫ x, (p.ofLp.1 : Torus d → ℝ) x ^ 2 * w x ∂haar d +
      ∫ x, ‖(p.ofLp.2 : Torus d → Tangent d) x‖ ^ 2 * w x ∂haar d := by
  have h0 : ‖p‖ ^ 2 = ‖p.ofLp.1‖ ^ 2 + ‖p.ofLp.2‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 p
  rw [h0, norm_sq_Hw hw hc hwb, norm_sq_Gw hw hc hwb]

theorem norm_sq_Amb_sub (hw : Measurable w) (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (p q : Amb d w) : ‖p - q‖ ^ 2 =
      ∫ x, ((p.ofLp.1 : Torus d → ℝ) x - (q.ofLp.1 : Torus d → ℝ) x) ^ 2 * w x ∂haar d +
      ∫ x, ‖(p.ofLp.2 : Torus d → Tangent d) x - (q.ofLp.2 : Torus d → Tangent d) x‖ ^ 2 * w x
        ∂haar d := by
  rw [norm_sq_Amb hw hc hwb]
  have e1 : (p - q).ofLp.1 = p.ofLp.1 - q.ofLp.1 := rfl
  have e2 : (p - q).ofLp.2 = p.ofLp.2 - q.ofLp.2 := rfl
  rw [e1, e2]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [ae_eq_haar hc hwb (Lp.coeFn_sub p.ofLp.1 q.ofLp.1)] with x hx
    rw [hx]; rfl
  · refine integral_congr_ae ?_
    filter_upwards [ae_eq_haar hc hwb (Lp.coeFn_sub p.ofLp.2 q.ofLp.2)] with x hx
    rw [hx]; rfl

end Space

section Kspace

open DGPS

variable {d : ℕ} {w : Torus d → ℝ} {c C : ℝ}

/-- The form space `V`: pairs `(u, g)` in `L²(w m) × L²(w m; ℝ^d)` with `g` a weak gradient
of `u`. -/
noncomputable def Kspace (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    Submodule ℝ (Amb d w) where
  carrier := {p | IsWeakGradient (p.ofLp.1 : Torus d → ℝ) (p.ofLp.2 : Torus d → Tangent d)}
  zero_mem' := isWeakGradient_zero.congr_ae
    (ae_eq_haar hc hwb (Lp.coeFn_zero _ _ _)).symm
    (ae_eq_haar hc hwb (Lp.coeFn_zero _ _ _)).symm
  add_mem' ha hb :=
    (IsWeakGradient.add ha hb).congr_ae
      (ae_eq_haar hc hwb (Lp.coeFn_add _ _)).symm
      (ae_eq_haar hc hwb (Lp.coeFn_add _ _)).symm
  smul_mem' r p hp :=
    (hp.smul r).congr_ae
      (ae_eq_haar hc hwb (Lp.coeFn_smul r p.ofLp.1)).symm
      (ae_eq_haar hc hwb (Lp.coeFn_smul r p.ofLp.2)).symm

theorem mem_Kspace (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) {p : Amb d w} :
    p ∈ Kspace hc hwb ↔
      IsWeakGradient (p.ofLp.1 : Torus d → ℝ) (p.ofLp.2 : Torus d → Tangent d) := Iff.rfl

theorem completeSpace_Kspace (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) : CompleteSpace (Kspace hc hwb) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hg : ∀ n, IsWeakGradient ((u n : Amb d w).ofLp.1 : Torus d → ℝ)
      ((u n : Amb d w).ofLp.2 : Torus d → Tangent d) := fun n => (u n).2
  have hdist : ∀ m n, dist (u n) (u m) ^ 2 =
      ∫ x, (((u n : Amb d w).ofLp.1 : Torus d → ℝ) x - ((u m : Amb d w).ofLp.1 : Torus d → ℝ) x)
        ^ 2 * w x ∂haar d +
      ∫ x, ‖((u n : Amb d w).ofLp.2 : Torus d → Tangent d) x -
        ((u m : Amb d w).ofLp.2 : Torus d → Tangent d) x‖ ^ 2 * w x ∂haar d := by
    intro m n
    rw [Subtype.dist_eq, dist_eq_norm, norm_sq_Amb_sub hw hc hwb]
  have hcau : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
      ∫ x, (((u n : Amb d w).ofLp.1 : Torus d → ℝ) x - ((u m : Amb d w).ofLp.1 : Torus d → ℝ) x)
        ^ 2 * w x ∂haar d +
      ∫ x, ‖((u n : Amb d w).ofLp.2 : Torus d → Tangent d) x -
        ((u m : Amb d w).ofLp.2 : Torus d → Tangent d) x‖ ^ 2 * w x ∂haar d < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [← hdist m n]
    have := hN n hn m hm
    exact (Real.lt_sqrt dist_nonneg).mp this
  obtain ⟨v, G, hvG, hT⟩ := weighted_form_complete hw hwb hc hg hcau
  have hvμ : MemLp v 2 (wMeasure d w) := (memLp_wMeasure_iff hc hwb).mpr hvG.memLp
  have hGμ : MemLp G 2 (wMeasure d w) := (memLp_wMeasure_iff hc hwb).mpr hvG.memLp_grad
  let q : Amb d w := WithLp.toLp 2 (hvμ.toLp v, hGμ.toLp G)
  have hq : q ∈ Kspace hc hwb := by
    refine hvG.congr_ae ?_ ?_
    · exact (ae_eq_haar hc hwb hvμ.coeFn_toLp).symm
    · exact (ae_eq_haar hc hwb hGμ.coeFn_toLp).symm
  refine ⟨⟨q, hq⟩, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hsq : ∀ n, dist (u n) ⟨q, hq⟩ ^ 2 =
      ∫ x, ((u n : Amb d w).ofLp.1 x - v x) ^ 2 * w x ∂haar d +
        ∫ x, ‖(u n : Amb d w).ofLp.2 x - G x‖ ^ 2 * w x ∂haar d := by
    intro n
    rw [Subtype.dist_eq, dist_eq_norm, norm_sq_Amb_sub hw hc hwb]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [ae_eq_haar hc hwb hvμ.coeFn_toLp] with x hx
      show _ = _
      simp only [q, hx]
    · refine integral_congr_ae ?_
      filter_upwards [ae_eq_haar hc hwb hGμ.coeFn_toLp] with x hx
      simp only [q, hx]
  have := (Real.continuous_sqrt.tendsto 0).comp hT
  rw [Real.sqrt_zero] at this
  refine this.congr fun n => ?_
  simp only [Function.comp]
  rw [← hsq, Real.sqrt_sq dist_nonneg]

end Kspace

section CompactCriterion

theorem isCompactOperator_of_subseq {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (J : V →L[ℝ] H)
    (h : ∀ (x : ℕ → V), (∀ n, ‖x n‖ ≤ 1) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : H,
      Tendsto (fun n => J (x (φ n))) atTop (𝓝 y)) : IsCompactOperator J := by
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall (J : V →ₗ[ℝ] H) (r := 1)
    one_pos).mpr ?_
  refine IsSeqCompact.isCompact fun y hy => ?_
  have hex : ∀ n : ℕ, ∃ z : V, ‖z‖ ≤ 1 ∧ dist (J z) (y n) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨_, ⟨z, hz, rfl⟩, hd⟩ := Metric.mem_closure_iff.mp (hy n) (1 / ((n : ℝ) + 1))
      (by positivity)
    exact ⟨z, by simpa using hz, by rwa [dist_comm]⟩
  choose z hz hd using hex
  obtain ⟨φ, hφ, y0, hy0⟩ := h z hz
  refine ⟨y0, ?_, φ, hφ, ?_⟩
  · refine isClosed_closure.mem_of_tendsto hy0 (Eventually.of_forall fun n => ?_)
    exact subset_closure ⟨z (φ n), by simpa using hz (φ n), rfl⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    have h1 : Tendsto (fun n => dist (J (z (φ n))) y0) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp hy0
    have h2 : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact this.comp hφ.tendsto_atTop
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (by simpa using h2.add h1)
    calc dist (y (φ n)) y0 ≤ dist (y (φ n)) (J (z (φ n))) + dist (J (z (φ n))) y0 :=
          dist_triangle _ _ _
      _ ≤ _ := by
        rw [dist_comm (y (φ n))]
        have := (hd (φ n)).le
        rw [one_div] at this
        exact add_le_add this le_rfl

end CompactCriterion

section FormJ

open DGPS

variable {d : ℕ} {w : Torus d → ℝ} {c C : ℝ}

/-- The embedding `J (u, g) = u` of the form space into `L²(w m)`. -/
noncomputable def formJ (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    Kspace hc hwb →L[ℝ] Hw d w :=
  (ContinuousLinearMap.fst ℝ (Hw d w) (Gw d w)).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (Hw d w) (Gw d w)).toContinuousLinearMap.comp
      (Kspace hc hwb).subtypeL)

theorem formJ_apply (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (x : Kspace hc hwb) :
    formJ hc hwb x = (x : Amb d w).ofLp.1 := rfl

/-- The gradient component of a point of the form space. -/
noncomputable def formGrad (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (x : Kspace hc hwb) : Torus d → Tangent d := ((x : Amb d w).ofLp.2 : Torus d → Tangent d)

theorem isWeakGradient_formJ (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (x : Kspace hc hwb) : IsWeakGradient (formJ hc hwb x : Torus d → ℝ) (formGrad hc hwb x) :=
  x.2

theorem inner_Kspace (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (x y : Kspace hc hwb) :
    ⟪x, y⟫_ℝ = ⟪formJ hc hwb x, formJ hc hwb y⟫_ℝ +
      ⟪(x : Amb d w).ofLp.2, (y : Amb d w).ofLp.2⟫_ℝ := by
  rw [Submodule.coe_inner, WithLp.prod_inner_apply]
  rfl

theorem formE_formJ (hw : Measurable w) (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (x y : Kspace hc hwb) :
    formE (formJ hc hwb) x y = weightedForm w (formGrad hc hwb x) (formGrad hc hwb y) := by
  unfold formE
  rw [inner_Kspace hc hwb, add_sub_cancel_left, inner_Lp_wMeasure hw hc hwb]
  rfl

theorem norm_sq_Kspace (hw : Measurable w) (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (x : Kspace hc hwb) : ‖x‖ ^ 2 = ∫ u, (formJ hc hwb x : Torus d → ℝ) u ^ 2 * w u ∂haar d +
      weightedForm w (formGrad hc hwb x) (formGrad hc hwb x) := by
  rw [weightedForm_self]
  exact norm_sq_Amb hw hc hwb x

theorem norm_formJ_le (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (x : Kspace hc hwb) : ‖formJ hc hwb x‖ ≤ ‖x‖ := by
  have h0 : ‖(x : Amb d w)‖ ^ 2 = ‖(x : Amb d w).ofLp.1‖ ^ 2 + ‖(x : Amb d w).ofLp.2‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 _
  have h1 : ‖x‖ = ‖(x : Amb d w)‖ := rfl
  have h2 : ‖formJ hc hwb x‖ = ‖(x : Amb d w).ofLp.1‖ := rfl
  rw [h1, h2]
  by_contra hlt
  replace hlt := not_le.mp hlt
  nlinarith [norm_nonneg ((x : Amb d w).ofLp.2), norm_nonneg ((x : Amb d w)),
    norm_nonneg ((x : Amb d w).ofLp.1)]

theorem formJ_injective (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    Function.Injective (formJ hc hwb) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hu : (formJ hc hwb x : Torus d → ℝ) =ᵐ[haar d] 0 := by
    have : (formJ hc hwb x : Hw d w) = 0 := hx
    rw [this]
    exact ae_eq_haar hc hwb (Lp.coeFn_zero _ _ _)
  have hg : IsWeakGradient (fun _ : Torus d => (0 : ℝ)) (formGrad hc hwb x) :=
    (isWeakGradient_formJ hc hwb x).congr_ae hu (Eventually.of_forall fun _ => rfl)
  have hg0 := hg.ae_eq isWeakGradient_zero
  have : (x : Amb d w).ofLp.2 = 0 := by
    refine Lp.ext ?_
    exact (ae_eq_wMeasure hg0).trans (Lp.coeFn_zero _ _ _).symm
  refine Subtype.ext ?_
  refine WithLp.ofLp_injective 2 ?_
  refine Prod.ext hx ?_
  exact this

end FormJ

section FormJ2

open DGPS

variable {d : ℕ} {w : Torus d → ℝ} {c C : ℝ}

theorem dist_Hw_sq (hw : Measurable w) (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (a b : Hw d w) : dist a b ^ 2 =
      ∫ x, ((a : Torus d → ℝ) x - (b : Torus d → ℝ) x) ^ 2 * w x ∂haar d := by
  rw [dist_eq_norm, norm_sq_Hw hw hc hwb]
  refine integral_congr_ae ?_
  filter_upwards [ae_eq_haar hc hwb (Lp.coeFn_sub a b)] with x hx
  rw [hx]; rfl

theorem tendsto_Hw_of_integral (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) {ι : Type*} {l : Filter ι} {a : ι → Hw d w}
    {b : Hw d w}
    (h : Tendsto (fun i => ∫ x, ((a i : Torus d → ℝ) x - (b : Torus d → ℝ) x) ^ 2 * w x ∂haar d)
      l (𝓝 0)) : Tendsto a l (𝓝 b) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at this
  refine this.congr fun n => ?_
  simp only [Function.comp]
  rw [← dist_Hw_sq hw hc hwb, Real.sqrt_sq dist_nonneg]

theorem formJ_denseRange (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) : DenseRange (formJ hc hwb) := by
  intro f
  have hf : MemLp (f : Torus d → ℝ) 2 (haar d) := (memLp_wMeasure_iff hc hwb).mp (Lp.memLp f)
  obtain ⟨v, -, hvg, hT⟩ := weighted_L2_density hw hwb hc hf
  have hvμ : ∀ n, MemLp (v n) 2 (wMeasure d w) := fun n =>
    (memLp_wMeasure_iff hc hwb).mpr (hvg n).memLp
  have hgμ : ∀ n, MemLp (smoothGrad (v n)) 2 (wMeasure d w) := fun n =>
    (memLp_wMeasure_iff hc hwb).mpr (hvg n).memLp_grad
  let q : ℕ → Amb d w := fun n => WithLp.toLp 2 ((hvμ n).toLp (v n), (hgμ n).toLp (smoothGrad (v n)))
  have hq : ∀ n, q n ∈ Kspace hc hwb := fun n =>
    (hvg n).congr_ae (ae_eq_haar hc hwb (hvμ n).coeFn_toLp).symm
      (ae_eq_haar hc hwb (hgμ n).coeFn_toLp).symm
  refine mem_closure_of_tendsto (b := atTop) (f := fun n => formJ hc hwb ⟨q n, hq n⟩) ?_
    (Eventually.of_forall fun n => ⟨_, rfl⟩)
  refine tendsto_Hw_of_integral hw hc hwb ?_
  refine hT.congr fun n => ?_
  refine integral_congr_ae ?_
  filter_upwards [ae_eq_haar hc hwb (hvμ n).coeFn_toLp] with x hx
  show (v n x - f x) ^ 2 * w x = ((hvμ n).toLp (v n) x - f x) ^ 2 * w x
  rw [hx]

theorem formJ_isCompactOperator (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) : IsCompactOperator (formJ hc hwb) := by
  refine isCompactOperator_of_subseq _ fun x hx => ?_
  obtain ⟨φ, v, hφ, hv, hlim⟩ := exists_subseq_tendsto_weighted_of_h1_bounded
    (fun n => (formJ hc hwb (x n) : Torus d → ℝ)) (fun n => formGrad hc hwb (x n)) 1 hw hwb hc
    (fun n => isWeakGradient_formJ hc hwb (x n)) (fun n => by
      have h1 := norm_sq_Kspace hw hc hwb (x n)
      rw [weightedForm_self] at h1
      have h2 : ‖x n‖ ^ 2 ≤ 1 := by
        have := hx n
        nlinarith [norm_nonneg (x n)]
      linarith)
  have hvμ : MemLp v 2 (wMeasure d w) := (memLp_wMeasure_iff hc hwb).mpr hv
  refine ⟨φ, hφ, hvμ.toLp v, ?_⟩
  refine tendsto_Hw_of_integral hw hc hwb ?_
  refine hlim.congr fun n => ?_
  refine integral_congr_ae ?_
  filter_upwards [ae_eq_haar hc hwb hvμ.coeFn_toLp] with u hu
  show ((formJ hc hwb (x (φ n)) : Torus d → ℝ) u - v u) ^ 2 * w u =
    ((formJ hc hwb (x (φ n)) : Torus d → ℝ) u - (hvμ.toLp v) u) ^ 2 * w u
  rw [hu]

theorem isForm_formJ (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) : IsForm (formJ hc hwb) where
  norm_le := norm_formJ_le hc hwb
  inj := formJ_injective hc hwb
  dense := formJ_denseRange hw hc hwb
  compact := formJ_isCompactOperator hw hc hwb

end FormJ2

end DGPS.Analysis.CompactResolvent

namespace DGPS.Analysis

open DGPS DGPS.Analysis.CompactResolvent MeasureTheory

/-- FOU009: compact resolvent and semigroup construction for the weighted form `E_w` on
`L²(w m)`.  The form domain is the closed space `V` of weak-gradient pairs, embedded in
`L²(w m)` by `J`; `J` is a compact, injective, densely ranged contraction with
`E_w(x, y) = ∫ ⟨∇x, ∇y⟩ w`, and the abstract construction (unique minimizers, compact positive
resolvent, orthonormal eigenbasis, nonnegative self-adjoint generator, strongly continuous
self-adjoint contraction semigroup `e^{-tA}`, energy quotient, product formula) holds for it. -/
theorem compact_resolvent_and_semigroup_construction {d : ℕ} {w : Torus d → ℝ} {c C : ℝ}
    (hw : Measurable w) (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    IsForm (formJ hc hwb) ∧
    (∀ x : Kspace hc hwb, IsWeakGradient (formJ hc hwb x : Torus d → ℝ) (formGrad hc hwb x)) ∧
    (∀ x y : Kspace hc hwb,
      formE (formJ hc hwb) x y = weightedForm w (formGrad hc hwb x) (formGrad hc hwb y)) ∧
    (∀ a : Hw d w, ‖a‖ ^ 2 = ∫ x, (a : Torus d → ℝ) x ^ 2 * w x ∂haar d) ∧
    ConstructionStmt (formJ hc hwb) := by
  have := completeSpace_Kspace hw hc hwb
  have hJ := isForm_formJ hw hc hwb
  exact ⟨hJ, isWeakGradient_formJ hc hwb, formE_formJ hw hc hwb, norm_sq_Hw hw hc hwb,
    construction hJ⟩

end DGPS.Analysis
