import DGPS.Lipschitz.WeightedGenerator

open MeasureTheory Filter Topology
open scoped InnerProductSpace Real

namespace DGPS.Lipschitz.WeightedSpectrum

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

section Abstract

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma tendsto_quot_exp (l : ℝ) :
    Tendsto (fun t : NNReal => (t : ℝ)⁻¹ * (1 - Real.exp (-((t : ℝ) * l))))
      (𝓝[≠] (0 : NNReal)) (𝓝 l) := by
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-(s * l))) (-l) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => -(s * l)) (-l) 0 := by
      have := ((hasDerivAt_id (0:ℝ)).mul_const l).neg
      convert this using 1
      · ext s; simp
      · simp
    simpa using h1.exp
  have h2 := hd.tendsto_slope_zero
  have h3 : Tendsto (fun t : NNReal => (t : ℝ)) (𝓝[≠] (0 : NNReal)) (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  have h4 := (h2.comp h3).neg
  rw [neg_neg] at h4
  refine h4.congr fun t => ?_
  simp only [Function.comp, smul_eq_mul, zero_add, zero_mul, neg_zero, Real.exp_zero]
  ring


lemma hasSum_energy_quot {ι : Type} (b : HilbertBasis ι ℝ H) (lam : ι → ℝ) (hl : ∀ i, 0 ≤ lam i)
    (T : NNReal → H →L[ℝ] H)
    (hT : ∀ (t : NNReal) f, HasSum (fun i => (Real.exp (-(t * lam i)) * ⟪b i, f⟫_ℝ) • b i) (T t f))
    (f : H) (E : ℝ)
    (hq : Tendsto (fun t : NNReal => (t : ℝ)⁻¹ * (‖f‖ ^ 2 - ⟪T t f, f⟫_ℝ)) (𝓝[≠] (0 : NNReal))
      (𝓝 E)) :
    HasSum (fun i => lam i * ⟪b i, f⟫_ℝ ^ 2) E := by
  have hA : ∀ t : NNReal, HasSum (fun i => (1 - Real.exp (-((t : ℝ) * lam i))) * ⟪b i, f⟫_ℝ ^ 2)
      (‖f‖ ^ 2 - ⟪T t f, f⟫_ℝ) := by
    intro t
    have hP := b.hasSum_inner_mul_inner f f
    have hQ := (hT t f).mapL (innerSL ℝ f)
    have hQ' : HasSum (fun i => Real.exp (-((t : ℝ) * lam i)) * ⟪b i, f⟫_ℝ ^ 2)
        ⟪T t f, f⟫_ℝ := by
      rw [real_inner_comm]
      convert hQ using 1
      swap
      · rfl
      ext i
      simp only [innerSL_apply_apply, inner_smul_right, real_inner_comm f (b i)]
      ring
    have hP' : HasSum (fun i => ⟪b i, f⟫_ℝ ^ 2) (‖f‖ ^ 2) := by
      rw [← real_inner_self_eq_norm_sq]
      convert hP using 1
      ext i
      simp only [real_inner_comm f (b i)]
      ring
    convert hP'.sub hQ' using 1
    ext i; ring
  have hnn : ∀ (t : NNReal) i, 0 ≤ (1 - Real.exp (-((t : ℝ) * lam i))) := by
    intro t i
    have : Real.exp (-((t : ℝ) * lam i)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_nonneg (NNReal.coe_nonneg t) (hl i)
      linarith
    linarith
  have hle : ∀ (t : NNReal) i, (1 - Real.exp (-((t : ℝ) * lam i))) ≤ t * lam i := by
    intro t i
    have := Real.add_one_le_exp (-((t : ℝ) * lam i))
    linarith
  have hB : ∀ t : NNReal, HasSum
      (fun i => ((t : ℝ)⁻¹ * (1 - Real.exp (-((t : ℝ) * lam i)))) * ⟪b i, f⟫_ℝ ^ 2)
      ((t : ℝ)⁻¹ * (‖f‖ ^ 2 - ⟪T t f, f⟫_ℝ)) := by
    intro t
    convert (hA t).mul_left ((t : ℝ)⁻¹) using 1
    ext i; ring
  have hφ0 : ∀ (t : NNReal), t ≠ 0 → ∀ i, 0 ≤ (t : ℝ)⁻¹ * (1 - Real.exp (-((t : ℝ) * lam i))) := by
    intro t ht i
    have : 0 < (t : ℝ) := by positivity
    exact mul_nonneg (inv_nonneg.mpr this.le) (hnn t i)
  have hφl : ∀ (t : NNReal), t ≠ 0 → ∀ i, (t : ℝ)⁻¹ * (1 - Real.exp (-((t : ℝ) * lam i))) ≤ lam i := by
    intro t ht i
    have : 0 < (t : ℝ) := by positivity
    calc (t : ℝ)⁻¹ * (1 - Real.exp (-((t : ℝ) * lam i))) ≤ (t : ℝ)⁻¹ * (t * lam i) :=
          mul_le_mul_of_nonneg_left (hle t i) (inv_nonneg.mpr this.le)
      _ = lam i := by field_simp
  have hev : ∀ᶠ t : NNReal in 𝓝[≠] (0 : NNReal), t ≠ 0 := self_mem_nhdsWithin
  have hc0 : ∀ i, 0 ≤ ⟪b i, f⟫_ℝ ^ 2 := fun i => sq_nonneg _
  have hfin : ∀ F : Finset ι, ∑ i ∈ F, lam i * ⟪b i, f⟫_ℝ ^ 2 ≤ E := by
    intro F
    refine le_of_tendsto_of_tendsto
      (tendsto_finsetSum F fun i _ => (tendsto_quot_exp (lam i)).mul_const _) hq ?_
    filter_upwards [hev] with t ht
    exact sum_le_hasSum F (fun i _ => mul_nonneg (hφ0 t ht i) (hc0 i)) (hB t)
  have hsum : Summable (fun i => lam i * ⟪b i, f⟫_ℝ ^ 2) :=
    summable_of_sum_le (fun i => mul_nonneg (hl i) (hc0 i)) hfin
  have hle1 : ∑' i, lam i * ⟪b i, f⟫_ℝ ^ 2 ≤ E := hsum.tsum_le_of_sum_le hfin
  have hle2 : E ≤ ∑' i, lam i * ⟪b i, f⟫_ℝ ^ 2 := by
    refine le_of_tendsto hq ?_
    filter_upwards [hev] with t ht
    exact hasSum_le (fun i => mul_le_mul_of_nonneg_right (hφl t ht i) (hc0 i)) (hB t)
      hsum.hasSum
  have : ∑' i, lam i * ⟪b i, f⟫_ℝ ^ 2 = E := le_antisymm hle1 hle2
  rw [← this]
  exact hsum.hasSum

variable [CompleteSpace H]

theorem eigData {J : V →L[ℝ] H} (hJ : ConstructionStmt J) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ H) (lam : ι → ℝ), (∀ i, 0 ≤ lam i) ∧
      (∀ i, ∃ x : V, J x = b i ∧ ∀ y, formE J x y = lam i * ⟪b i, J y⟫_ℝ) ∧
      (∀ x : V, HasSum (fun i => lam i * ⟪b i, J x⟫_ℝ ^ 2) (formE J x x)) := by
  obtain ⟨ι, b, lam, R, T, A, hl, -, -, -, -, -, -, heig, hform, -, hs, -, -, -, -, -, -, -, hq, -, -⟩ := hJ
  refine ⟨ι, b, lam, hl, fun i => ?_, fun x => hasSum_energy_quot b lam hl T hs (J x) _ (hq x)⟩
  obtain ⟨hi, hAi⟩ := heig i
  obtain ⟨x, hx1, hx2⟩ := hform ⟨b i, hi⟩
  refine ⟨x, hx1, fun y => ?_⟩
  rw [hx2 y, hAi, inner_smul_left]
  simp

end Abstract

section Concrete

variable {d : ℕ} {w : Torus d → ℝ} {c C : ℝ}

/-- Spectral data of the weighted form: an orthonormal basis `b` of `L²(w m)` of weak eigenfunctions
with eigenvalues `lam` and gradients `G`, satisfying the energy identity. -/
structure SpectralData (w : Torus d → ℝ) {ι : Type} (b : HilbertBasis ι ℝ (Hw d w))
    (lam : ι → ℝ) (G : ι → Torus d → Tangent d) : Prop where
  nonneg : ∀ i, 0 ≤ lam i
  grad : ∀ i, IsWeakGradient ((b i : Hw d w) : Torus d → ℝ) (G i)
  eig : ∀ i (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
    weightedForm w (G i) Y = lam i * ⟪b i, f⟫_ℝ
  energy : ∀ (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
    HasSum (fun i => lam i * ⟪b i, f⟫_ℝ ^ 2) (weightedForm w Y Y)

theorem exists_spectralData (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (Hw d w)) (lam : ι → ℝ) (G : ι → Torus d → Tangent d),
      SpectralData w b lam G := by
  have := DGPS.Lipschitz.WeightedGenerator.isFiniteMeasure_wMeasure hwb
  obtain ⟨-, -, -, -, hJ⟩ := compact_resolvent_and_semigroup_construction hw hc hwb
  obtain ⟨ι, b, lam, hl, heig, hen⟩ := eigData hJ
  choose x hx1 hx2 using heig
  have key : ∀ (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
      ∃ k : Kspace hc hwb, formJ hc hwb k = f ∧ formGrad hc hwb k =ᵐ[haar d] Y := by
    intro f Y hy
    obtain ⟨k, hk1, hk2⟩ := DGPS.Lipschitz.WeightedGenerator.exists_kspace hc hwb hy
    refine ⟨k, Lp.ext (ae_eq_wMeasure hk1), hk2⟩
  refine ⟨ι, b, lam, fun i => formGrad hc hwb (x i), hl, fun i => ?_, fun i f Y hy => ?_,
    fun f Y hy => ?_⟩
  · have := isWeakGradient_formJ hc hwb (x i)
    rwa [hx1 i] at this
  · obtain ⟨k, hk1, hk2⟩ := key f Y hy
    rw [← weightedForm_congr_ae (Filter.EventuallyEq.refl _ _) hk2,
      ← formE_formJ hw hc hwb, hx2 i k, hk1]
  · obtain ⟨k, hk1, hk2⟩ := key f Y hy
    rw [← weightedForm_congr_ae hk2 hk2, ← formE_formJ hw hc hwb]
    have := hen k
    rwa [hk1] at this

section Fourier

theorem exists_fourier_vec (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    ∃ v : (Fin d → ℤ) → Hw d w, ∀ (f : Hw d w) (k : Fin d → ℤ),
      ⟪v k, f⟫_ℝ = (fourierCoeff (f : Torus d → ℝ) k).re + (fourierCoeff (f : Torus d → ℝ) k).im := by
  have := DGPS.Lipschitz.WeightedGenerator.isFiniteMeasure_wMeasure hwb
  have hex : ∀ k : Fin d → ℤ, ∃ v : Hw d w, (v : Torus d → ℝ) =ᵐ[wMeasure d w] fun x =>
      ((UnitAddTorus.mFourier (-k) x).re + (UnitAddTorus.mFourier (-k) x).im) / w x := by
    intro k
    have hm : Measurable fun x : Torus d => ((UnitAddTorus.mFourier (-k) x).re +
        (UnitAddTorus.mFourier (-k) x).im) / w x := by
      have h1 : Measurable fun x : Torus d => UnitAddTorus.mFourier (-k) x :=
        (UnitAddTorus.mFourier (-k)).continuous.measurable
      exact ((Complex.measurable_re.comp h1).add (Complex.measurable_im.comp h1)).div hw
    have hb : MemLp (fun x : Torus d => ((UnitAddTorus.mFourier (-k) x).re +
        (UnitAddTorus.mFourier (-k) x).im) / w x) 2 (haar d) := by
      refine MemLp.of_bound hm.aestronglyMeasurable (2 / c) ?_
      filter_upwards [hwb] with x hx
      have hw0 : 0 < w x := hc.trans_le hx.1
      have hn : ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
        have := (UnitAddTorus.mFourier (-k)).norm_coe_le_norm x
        rwa [UnitAddTorus.mFourier_norm] at this
      have h1 := Complex.abs_re_le_norm (UnitAddTorus.mFourier (-k) x)
      have h2 := Complex.abs_im_le_norm (UnitAddTorus.mFourier (-k) x)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hw0, div_le_div_iff₀ hw0 hc]
      have h3 := abs_add_le (UnitAddTorus.mFourier (-k) x).re (UnitAddTorus.mFourier (-k) x).im
      calc |(UnitAddTorus.mFourier (-k) x).re + (UnitAddTorus.mFourier (-k) x).im| * c
          ≤ 2 * c := by
            refine mul_le_mul_of_nonneg_right ?_ hc.le
            linarith
        _ ≤ 2 * w x := by nlinarith [hx.1]
    exact ⟨((memLp_wMeasure_iff hc hwb).mpr hb).toLp _, MemLp.coeFn_toLp _⟩
  choose v hv using hex
  refine ⟨v, fun f k => ?_⟩
  have hfi : Integrable (f : Torus d → ℝ) (haar d) :=
    ((memLp_wMeasure_iff hc hwb).mp (Lp.memLp f)).integrable one_le_two
  rw [fourierCoeff_re hfi, fourierCoeff_im hfi, real_inner_comm, inner_Lp_wMeasure hw hc hwb]
  have hmf : Measurable fun x : Torus d => UnitAddTorus.mFourier (-k) x :=
    (UnitAddTorus.mFourier (-k)).continuous.measurable
  have hn : ∀ x, ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
    intro x
    have := (UnitAddTorus.mFourier (-k)).norm_coe_le_norm x
    rwa [UnitAddTorus.mFourier_norm] at this
  have iRe : Integrable (fun x => (f : Torus d → ℝ) x * (UnitAddTorus.mFourier (-k) x).re)
      (haar d) := by
    refine Integrable.mono' hfi.norm (hfi.aestronglyMeasurable.mul
      (Complex.measurable_re.comp hmf).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    calc ‖(f : Torus d → ℝ) x‖ * ‖(UnitAddTorus.mFourier (-k) x).re‖ ≤ ‖(f : Torus d → ℝ) x‖ * 1 :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hn x)) (norm_nonneg _)
      _ = _ := mul_one _
  have iIm : Integrable (fun x => (f : Torus d → ℝ) x * (UnitAddTorus.mFourier (-k) x).im)
      (haar d) := by
    refine Integrable.mono' hfi.norm (hfi.aestronglyMeasurable.mul
      (Complex.measurable_im.comp hmf).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    calc ‖(f : Torus d → ℝ) x‖ * ‖(UnitAddTorus.mFourier (-k) x).im‖ ≤ ‖(f : Torus d → ℝ) x‖ * 1 :=
          mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans (hn x)) (norm_nonneg _)
      _ = _ := mul_one _
  rw [← integral_add iRe iIm]
  refine integral_congr_ae ?_
  filter_upwards [ae_eq_haar hc hwb (hv k), hwb] with x hx hx2
  have hw0 : w x ≠ 0 := (hc.trans_le hx2.1).ne'
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  field_simp

end Fourier

section Enum

theorem exists_enum {ι : Type} [Infinite ι] [Countable ι] (lam : ι → ℝ)
    (hfin : ∀ L : ℝ, {i | lam i ≤ L}.Finite) : ∃ σ : ℕ ≃ ι, Monotone (lam ∘ σ) := by
  obtain ⟨g, hg⟩ := exists_injective_nat ι
  let key : ι → ℝ ×ₗ ℕ := fun i => toLex (lam i, g i)
  have hkey : Function.Injective key := by
    intro i j h
    have := congrArg (fun p => (ofLex p).2) h
    exact hg this
  have hlam : ∀ i j, key i < key j → lam i ≤ lam j := by
    intro i j h
    rcases Prod.Lex.lt_iff.mp h with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  let pred : ι → Set ι := fun i => {j | key j < key i}
  have hpf : ∀ i, (pred i).Finite := fun i => (hfin (lam i)).subset fun j hj => hlam j i hj
  let r : ι → ℕ := fun i => (pred i).ncard
  have hr : ∀ i j, key i < key j → r i < r j := by
    intro i j h
    refine Set.ncard_lt_ncard ⟨fun k hk => lt_trans hk h, fun hsub => ?_⟩ (hpf j)
    have : i ∈ pred i := hsub h
    exact lt_irrefl (key i) this
  have hinj : Function.Injective r := by
    intro i j h
    by_contra hne
    rcases lt_trichotomy (key i) (key j) with h1 | h1 | h1
    · exact (hr i j h1).ne h
    · exact hne (hkey h1)
    · exact (hr j i h1).ne h.symm
  have hinf : Infinite (Set.range r) := (Set.infinite_range_of_injective hinj).to_subtype
  let σ : ℕ ≃ ι := (Nat.Subtype.orderIsoOfNat (Set.range r)).toEquiv.trans
    (Equiv.ofInjective r hinj).symm
  refine ⟨σ, fun n m hnm => ?_⟩
  have h1 : r (σ n) ≤ r (σ m) := by
    have := (Nat.Subtype.orderIsoOfNat (Set.range r)).monotone hnm
    have e : ∀ k, r (σ k) = ((Nat.Subtype.orderIsoOfNat (Set.range r)) k : ℕ) := by
      intro k
      simp only [σ, Equiv.trans_apply]
      exact congrArg Subtype.val ((Equiv.ofInjective r hinj).apply_symm_apply _)
    rw [e, e]
    exact this
  by_contra hlt
  have hlt' : lam (σ m) < lam (σ n) := not_le.mp hlt
  have : key (σ m) < key (σ n) := Prod.Lex.lt_iff.mpr (Or.inl hlt')
  exact absurd h1 (not_le.mpr (hr _ _ this))

end Enum

section Counting

variable {ι : Type} {b : HilbertBasis ι ℝ (Hw d w)} {lam : ι → ℝ} {G : ι → Torus d → Tangent d}

theorem exists_grad_of_mem_span (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hsd : SpectralData w b lam G) (S : Finset ι) {f : Hw d w}
    (hf : f ∈ Submodule.span ℝ (Set.range fun i : S => (b i : Hw d w))) :
    ∃ Y, IsWeakGradient (f : Torus d → ℝ) Y := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨_, hsd.grad i⟩
  | zero =>
    exact ⟨_, isWeakGradient_zero.congr_ae
      (ae_eq_haar hc hwb (Lp.coeFn_zero _ _ _)).symm (Filter.EventuallyEq.refl _ _)⟩
  | add x y _ _ hx hy =>
    obtain ⟨Yx, hYx⟩ := hx
    obtain ⟨Yy, hYy⟩ := hy
    exact ⟨_, (hYx.add hYy).congr_ae (ae_eq_haar hc hwb (Lp.coeFn_add x y)).symm
      (Filter.EventuallyEq.refl _ _)⟩
  | smul a x _ hx =>
    obtain ⟨Yx, hYx⟩ := hx
    refine ⟨_, (hYx.smul a).congr_ae ?_ (Filter.EventuallyEq.refl _ _)⟩
    filter_upwards [ae_eq_haar hc hwb (Lp.coeFn_smul a x)] with p hp
    rw [hp]; rfl

theorem eq_zero_of_fourier_vanish (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (K : Finset (Fin d → ℤ)) (L : ℝ) (hK : ∀ k, k ∉ K → L < gradWeight k) {f : Hw d w}
    {Y : Torus d → Tangent d} (hY : IsWeakGradient (f : Torus d → ℝ) Y)
    (hb : ∫ x, ‖Y x‖ ^ 2 ∂haar d ≤ L * ∫ x, (f : Torus d → ℝ) x ^ 2 ∂haar d)
    (hf : ∀ k ∈ K, fourierCoeff (f : Torus d → ℝ) k = 0) : f = 0 := by
  have hu : MemLp (f : Torus d → ℝ) 2 (haar d) := (memLp_wMeasure_iff hc hwb).mp (Lp.memLp f)
  have hP := hasSum_sq_fourierCoeff hu
  have hG := hasSum_gradWeight_weakGradient hY
  have hD := hG.sub (hP.mul_left L)
  have hterm : ∀ k, 0 ≤ gradWeight k * ‖fourierCoeff (f : Torus d → ℝ) k‖ ^ 2 -
      L * ‖fourierCoeff (f : Torus d → ℝ) k‖ ^ 2 := by
    intro k
    by_cases hk : k ∈ K
    · simp [hf k hk]
    · have := hK k hk
      rw [← sub_mul]
      exact mul_nonneg (by linarith) (by positivity)
  have hz : ∀ k, ‖fourierCoeff (f : Torus d → ℝ) k‖ ^ 2 = 0 := by
    intro k
    have h1 := le_hasSum hD k fun j _ => hterm j
    have h2 : (gradWeight k * ‖fourierCoeff (f : Torus d → ℝ) k‖ ^ 2 -
        L * ‖fourierCoeff (f : Torus d → ℝ) k‖ ^ 2) ≤ 0 := by
      refine h1.trans ?_
      linarith
    by_cases hk : k ∈ K
    · simp [hf k hk]
    · have h3 : (gradWeight k - L) * ‖fourierCoeff (f : Torus d → ℝ) k‖ ^ 2 ≤ 0 := by
        rw [sub_mul]; exact h2
      have h4 : 0 < gradWeight k - L := by linarith [hK k hk]
      have h5 : 0 ≤ ‖fourierCoeff (f : Torus d → ℝ) k‖ ^ 2 := by positivity
      nlinarith
  have hI : ∫ x, (f : Torus d → ℝ) x ^ 2 ∂haar d = 0 := by
    refine hP.unique ?_
    simp [hz]
  have hi : Integrable (fun x => (f : Torus d → ℝ) x ^ 2) (haar d) := hu.integrable_sq
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi).mp hI
  refine Lp.ext (ae_eq_wMeasure ?_ |>.trans (Lp.coeFn_zero _ _ _).symm)
  filter_upwards [hae] with x hx
  simpa using hx

theorem inner_eq_zero_of_mem_span (S : Finset ι) {f : Hw d w}
    (hf : f ∈ Submodule.span ℝ (Set.range fun i : S => (b i : Hw d w))) {j : ι} (hj : j ∉ S) :
    ⟪b j, f⟫_ℝ = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact b.orthonormal.inner_eq_zero (fun h => hj (h ▸ i.2))
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]

theorem exists_grad_energy_le (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hsd : SpectralData w b lam G) (S : Finset ι) (L : ℝ) (hL : ∀ i ∈ S, lam i ≤ L)
    {f : Hw d w} (hf : f ∈ Submodule.span ℝ (Set.range fun i : S => (b i : Hw d w))) :
    ∃ Y, IsWeakGradient (f : Torus d → ℝ) Y ∧ weightedForm w Y Y ≤ L * ‖f‖ ^ 2 := by
  obtain ⟨Y, hY⟩ := exists_grad_of_mem_span hc hwb hsd S hf
  refine ⟨Y, hY, ?_⟩
  have h1 := hsd.energy f Y hY
  have h2 := b.hasSum_inner_mul_inner f f
  have h3 : HasSum (fun i => L * ⟪b i, f⟫_ℝ ^ 2) (L * ‖f‖ ^ 2) := by
    have : HasSum (fun i => ⟪b i, f⟫_ℝ ^ 2) (‖f‖ ^ 2) := by
      convert h2 using 1
      · ext i; rw [real_inner_comm, sq]
      · rw [real_inner_self_eq_norm_sq]
    exact this.mul_left L
  refine hasSum_le (fun i => ?_) h1 h3
  by_cases hi : i ∈ S
  · exact mul_le_mul_of_nonneg_right (hL i hi) (sq_nonneg _)
  · rw [inner_eq_zero_of_mem_span S hf hi]; simp

theorem card_le_of_lam_le (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hsd : SpectralData w b lam G)
    (S : Finset ι) (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ i ∈ S, lam i ≤ L)
    (K : Finset (Fin d → ℤ)) (hKneg : ∀ k ∈ K, -k ∈ K)
    (hK : ∀ k, k ∉ K → C * L / c < gradWeight k) : S.card ≤ K.card := by
  obtain ⟨v, hv⟩ := exists_fourier_vec hw hc hwb
  set U : Submodule ℝ (Hw d w) := Submodule.span ℝ (Set.range fun i : S => (b i : Hw d w)) with hU
  have hli : LinearIndependent ℝ (fun i : S => (b i : Hw d w)) :=
    b.orthonormal.linearIndependent.comp (fun i : S => (i : ι)) Subtype.val_injective
  have hrank : Module.finrank ℝ U = S.card := by
    rw [hU, finrank_span_eq_card hli, Fintype.card_coe]
  let Ψ : U →ₗ[ℝ] (K → ℝ) :=
    LinearMap.pi fun k : K => (innerSL ℝ (v k)).toLinearMap ∘ₗ U.subtype
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hk : ∀ k ∈ K, ⟪v k, (f : Hw d w)⟫_ℝ = 0 := fun k hk => by
      have := congrFun hf ⟨k, hk⟩
      simpa [Ψ] using this
    have hz : ∀ k ∈ K, fourierCoeff ((f : Hw d w) : Torus d → ℝ) k = 0 := by
      intro k hkK
      have h1 := hk k hkK
      have h2 := hk (-k) (hKneg k hkK)
      rw [hv, ] at h1 h2
      rw [fourierCoeff_neg] at h2
      simp only [Complex.conj_re, Complex.conj_im] at h2
      apply Complex.ext <;> simp <;> linarith
    obtain ⟨Y, hY, hYb⟩ := exists_grad_energy_le hc hwb hsd S L hL f.2
    have hu : MemLp ((f : Hw d w) : Torus d → ℝ) 2 (haar d) :=
      (memLp_wMeasure_iff hc hwb).mp (Lp.memLp _)
    have hYi : Integrable (fun x => ‖Y x‖ ^ 2) (haar d) := hY.memLp_grad.norm.integrable_sq
    have h1 := mul_integral_le_integral_mul_weight hYi (fun x => sq_nonneg _) hw hwb hc
    have hi : Integrable (fun x => ((f : Hw d w) : Torus d → ℝ) x ^ 2) (haar d) := hu.integrable_sq
    have h2 := integral_mul_weight_le hi (fun x => sq_nonneg _) hw hwb hc
    have hnorm : ‖(f : Hw d w)‖ ^ 2 = ∫ x, ((f : Hw d w) : Torus d → ℝ) x ^ 2 * w x ∂haar d := by
      rw [← real_inner_self_eq_norm_sq, inner_Lp_wMeasure hw hc hwb]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    rw [weightedForm_self] at hYb
    have hfin : ∫ x, ‖Y x‖ ^ 2 ∂haar d ≤ C * L / c *
        ∫ x, ((f : Hw d w) : Torus d → ℝ) x ^ 2 ∂haar d := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      have h3 : L * ∫ x, ((f : Hw d w) : Torus d → ℝ) x ^ 2 * w x ∂haar d ≤
          L * (C * ∫ x, ((f : Hw d w) : Torus d → ℝ) x ^ 2 ∂haar d) :=
        mul_le_mul_of_nonneg_left h2 hL0
      rw [hnorm] at hYb
      nlinarith
    have := eq_zero_of_fourier_vanish hc hwb K (C * L / c) hK hY hfin hz
    exact Subtype.ext this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  exact this

theorem card_freqBox (N : ℕ) : (freqBox d N).card = (2 * N + 1) ^ d := by
  unfold freqBox
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem neg_mem_freqBox {N : ℕ} {k : Fin d → ℤ} (hk : k ∈ freqBox d N) : -k ∈ freqBox d N := by
  rw [mem_freqBox] at hk ⊢
  intro j
  simpa using hk j

theorem four_pi_sq_le_gradWeight {k : Fin d → ℤ} (hk : k ≠ 0) : 4 * π ^ 2 ≤ gradWeight k := by
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
    by_contra h
    exact hk (funext fun j => by simpa using (not_exists.mp h j))
  unfold gradWeight
  have h1 : (1 : ℝ) ≤ ((k j : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (k j) ^ 2 := by
      have := sq_pos_of_ne_zero hj
      omega
    exact_mod_cast this
  have h2 : ((k j : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun i => ((k i : ℤ) : ℝ) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  have : 0 < π ^ 2 := by positivity
  nlinarith

theorem pow_two_div_le {n t : ℝ} (hd : 0 < d) (hn : 0 ≤ n) (ht : 0 ≤ t) (h : n ≤ t ^ d) :
    n ^ (2 / (d : ℝ)) ≤ t ^ 2 := by
  have h1 : n ^ (2 / (d : ℝ)) ≤ (t ^ d) ^ (2 / (d : ℝ)) :=
    Real.rpow_le_rpow hn h (by positivity)
  have h2 : (t ^ d) ^ (2 / (d : ℝ)) = t ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    have : (d : ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ this]
    norm_num
  rw [h2] at h1
  exact h1

theorem weyl_bound (hd : 0 < d) (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hsd : SpectralData w b lam G)
    (S : Finset ι) (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ i ∈ S, lam i ≤ L) (hS : 2 ≤ S.card) :
    4 * π ^ 2 * c / (25 * C) * (S.card : ℝ) ^ (2 / (d : ℝ)) ≤ L := by
  obtain ⟨x0, hx0⟩ := hwb.exists
  have hC : 0 < C := hc.trans_le (hx0.1.trans hx0.2)
  have hpi : 0 < π := Real.pi_pos
  set L₁ := C * L / c with hL₁
  have hL₁0 : 0 ≤ L₁ := by positivity
  by_cases hsmall : L₁ < 4 * π ^ 2
  · exfalso
    have := card_le_of_lam_le hw hc hwb hsd S L hL0 hL {0} (by simp) (fun k hk => by
      have hk0 : k ≠ 0 := by simpa using hk
      exact hsmall.trans_le (four_pi_sq_le_gradWeight hk0))
    simp at this
    omega
  replace hsmall := not_lt.mp hsmall
  set s := Real.sqrt L₁ / (2 * π) with hs
  have hs1 : 1 ≤ s := by
    rw [hs, le_div_iff₀ (by positivity), one_mul]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hs2 : s ^ 2 = L₁ / (4 * π ^ 2) := by
    rw [hs, div_pow, Real.sq_sqrt hL₁0]
    ring
  set N := ⌊s⌋₊ + 1 with hN
  have hNs : (N : ℝ) ≤ 2 * s := by
    have := Nat.floor_le (by linarith : 0 ≤ s)
    rw [hN]; push_cast; linarith
  have hNgt : s < N := by rw [hN]; push_cast; exact Nat.lt_floor_add_one s
  have hKbound := card_le_of_lam_le hw hc hwb hsd S L hL0 hL (freqBox d N)
    (fun k hk => neg_mem_freqBox hk) (fun k hk => by
      have h1 := four_pi_sq_mul_le_gradWeight hk
      have h2 : L₁ < 4 * π ^ 2 * (N : ℝ) ^ 2 := by
        have : L₁ < 4 * π ^ 2 * (N : ℝ) ^ 2 := by
          have h3 : s ^ 2 < (N : ℝ) ^ 2 := by nlinarith
          rw [hs2, div_lt_iff₀ (by positivity)] at h3
          linarith
        exact this
      linarith)
  rw [card_freqBox] at hKbound
  have hcard : (S.card : ℝ) ≤ (5 * s) ^ d := by
    have h1 : ((2 * N + 1 : ℕ) : ℝ) ≤ 5 * s := by push_cast; linarith
    calc (S.card : ℝ) ≤ ((2 * N + 1) ^ d : ℕ) := by exact_mod_cast hKbound
      _ = ((2 * N + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
      _ ≤ (5 * s) ^ d := pow_le_pow_left₀ (by positivity) h1 d
  have h2 := pow_two_div_le hd (by positivity) (by positivity) hcard
  have h3 : (5 * s) ^ 2 = 25 * (C * L / c) / (4 * π ^ 2) := by
    rw [mul_pow, hs2]; ring
  rw [h3] at h2
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  rw [le_div_iff₀ (by positivity)] at h2
  have : 4 * π ^ 2 * c * (S.card : ℝ) ^ (2 / (d : ℝ)) ≤ L * (25 * C) := by
    have h4 : (S.card : ℝ) ^ (2 / (d : ℝ)) * (4 * π ^ 2) * c ≤ 25 * (C * L / c) * c := by
      exact mul_le_mul_of_nonneg_right h2 hc.le
    have h5 : 25 * (C * L / c) * c = 25 * C * L := by field_simp
    nlinarith
  linarith

theorem infinite_index (b : HilbertBasis ι ℝ (Hw d w)) (hd : 0 < d) (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    Infinite ι := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have hfd : Module.Finite ℝ (Hw d w) := by
    have h1 : (Submodule.span ℝ (Set.range (b : ι → Hw d w))).topologicalClosure = ⊤ :=
      b.dense_span
    have h3 : FiniteDimensional ℝ (Submodule.span ℝ (Set.range (b : ι → Hw d w))) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    have h2 : Submodule.span ℝ (Set.range (b : ι → Hw d w)) = ⊤ := by
      rw [← h1]
      exact ((Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq).symm
    rw [Module.finite_def, ← h2]
    exact Submodule.fg_span (Set.finite_range _)
  have : Infinite (Torus d) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have h1 : Infinite (AddCircle (1:ℝ)) :=
      (AddCircle.equivIco (1:ℝ) 0).infinite_iff.mpr
        (by rw [zero_add]; exact (Set.Ico_infinite zero_lt_one).to_subtype)
    show Infinite (Fin d → AddCircle (1:ℝ))
    infer_instance
  obtain ⟨U, hUi, hUo, hUd⟩ := exists_seq_infinite_isOpen_pairwise_disjoint (X := Torus d)
  have hfm := DGPS.Lipschitz.WeightedGenerator.isFiniteMeasure_wMeasure hwb
  have hm : ∀ n, MeasurableSet (U n) := fun n => (hUo n).measurableSet
  have hfin' : ∀ n, wMeasure d w (U n) ≠ ⊤ := fun n => measure_ne_top _ _
  have hpos : ∀ n, wMeasure d w (U n) ≠ 0 := by
    intro n h0
    have h1 := wMeasure_ge hwb (U n)
    rw [h0] at h1
    have h2 : (ENNReal.ofReal c • haar d) (U n) = 0 := le_antisymm h1 bot_le
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact (ENNReal.ofReal_pos.mpr hc).ne' h2
    · exact ((hUo n).measure_pos (haar d) (hUi n).nonempty).ne' h2
  let u : ℕ → Hw d w := fun n => indicatorConstLp 2 (hm n) (hfin' n) (1 : ℝ)
  have hu0 : ∀ n, u n ≠ 0 := by
    intro n h
    have h1 := norm_indicatorConstLp (hs := hm n) (hμs := hfin' n) (c := (1:ℝ)) (p := 2)
      (μ := wMeasure d w) (by norm_num) (by norm_num)
    have h2 : ‖u n‖ = 0 := by rw [h]; simp
    have h3 : 0 < (wMeasure d w).real (U n) :=
      ENNReal.toReal_pos (hpos n) (hfin' n)
    have h4 : 0 < (wMeasure d w).real (U n) ^ (1 / (2 : ENNReal).toReal) :=
      Real.rpow_pos_of_pos h3 _
    have h5 : ‖u n‖ = 1 * (wMeasure d w).real (U n) ^ (1 / (2 : ENNReal).toReal) := by
      simpa using h1
    rw [h2] at h5
    linarith
  have horth : Pairwise fun m n => ⟪u m, u n⟫_ℝ = 0 := by
    intro m n hmn
    change ⟪indicatorConstLp 2 (hm m) (hfin' m) (1:ℝ), u n⟫_ℝ = 0
    rw [MeasureTheory.L2.inner_indicatorConstLp_one]
    refine integral_eq_zero_of_ae ?_
    have h1 : ∀ᵐ x ∂(wMeasure d w), x ∉ U n → (u n : Torus d → ℝ) x = 0 :=
      indicatorConstLp_coeFn_notMem
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem (hm m)] with x hx hxm
    refine hx ?_
    intro hxn
    exact Set.disjoint_left.mp (hUd hmn) hxm hxn
  have hli := linearIndependent_of_ne_zero_of_inner_eq_zero hu0 horth
  have := hli.finite_of_isNoetherian
  exact not_finite ℕ

theorem finite_sublevel (hd : 0 < d) (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hsd : SpectralData w b lam G) (L : ℝ)
    (hL0 : 0 ≤ L) : {i | lam i ≤ L}.Finite := by
  by_contra hinf
  obtain ⟨x0, hx0⟩ := hwb.exists
  have hC : 0 < C := hc.trans_le (hx0.1.trans hx0.2)
  have hpi : 0 < π := Real.pi_pos
  set A := 4 * π ^ 2 * c / (25 * C) with hA
  have hApos : 0 < A := by positivity
  have hev : ∀ᶠ n : ℕ in atTop, L / A < (n : ℝ) ^ (2 / (d : ℝ)) :=
    (((tendsto_rpow_atTop (by positivity : 0 < 2 / (d : ℝ))).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop (L / A))
  obtain ⟨n, hn1, hn2⟩ := (hev.and (eventually_ge_atTop 2)).exists
  obtain ⟨S, hS1, hS2⟩ := Set.Infinite.exists_subset_card_eq hinf n
  have := weyl_bound hd hw hc hwb hsd S L hL0 (fun i hi => hS1 hi) (by omega)
  rw [hS2] at this
  have h2 : L < A * (n : ℝ) ^ (2 / (d : ℝ)) := by
    rwa [div_lt_iff₀ hApos, mul_comm] at hn1
  linarith

theorem countable_index (hd : 0 < d) (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hsd : SpectralData w b lam G) : Countable ι := by
  have : (Set.univ : Set ι) = ⋃ n : ℕ, {i | lam i ≤ n} := by
    ext i
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    exact exists_nat_ge (lam i)
  rw [← Set.countable_univ_iff, this]
  exact Set.countable_iUnion fun n =>
    (finite_sublevel hd hw hc hwb hsd n (Nat.cast_nonneg n)).countable

theorem exists_reindex (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (b : HilbertBasis ι ℝ (Hw d w)) (σ : ℕ ≃ ι) (s : ι → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hsd : SpectralData w b lam G) :
    ∃ (e : HilbertBasis ℕ ℝ (Hw d w)) (G' : ℕ → Torus d → Tangent d),
      (∀ n, e n = s (σ n) • b (σ n)) ∧ SpectralData w e (fun n => lam (σ n)) G' := by
  classical
  have hs2 : ∀ i, s i * s i = 1 := fun i => by rcases hs i with h | h <;> rw [h] <;> norm_num
  have horth : Orthonormal ℝ (fun n => s (σ n) • b (σ n)) := by
    rw [orthonormal_iff_ite]
    intro m n
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc]
    have := (orthonormal_iff_ite.mp b.orthonormal) (σ m) (σ n)
    rw [this]
    by_cases h : m = n
    · subst h; simp [hs2]
    · have : σ m ≠ σ n := fun h' => h (σ.injective h')
      simp [h, this]
  have hsp : ⊤ ≤ (Submodule.span ℝ (Set.range fun n => s (σ n) • b (σ n))).topologicalClosure := by
    rw [← b.dense_span]
    refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    have hm := Submodule.smul_mem (Submodule.span ℝ (Set.range fun n => s (σ n) • b (σ n)))
      (s i) (Submodule.subset_span ⟨σ.symm i, rfl⟩)
    simp only [Equiv.apply_symm_apply, smul_smul, hs2, one_smul] at hm
    exact hm
  let e := HilbertBasis.mk horth hsp
  have he : ∀ n, e n = s (σ n) • b (σ n) := fun n => by simp [e]
  refine ⟨e, fun n x => s (σ n) • G (σ n) x, he, ?_⟩
  refine ⟨fun n => hsd.nonneg _, fun n => ?_, fun n f Y hY => ?_, fun f Y hY => ?_⟩
  · have h1 := (hsd.grad (σ n)).smul (s (σ n))
    refine h1.congr_ae ?_ (Filter.EventuallyEq.refl _ _)
    rw [he]
    refine (ae_eq_haar hc hwb (Lp.coeFn_smul (s (σ n)) (b (σ n)))).symm.trans ?_
    exact Filter.EventuallyEq.refl _ _
  · rw [he, weightedForm_smul_left, hsd.eig (σ n) f Y hY, real_inner_smul_left]
    ring
  · have h1 := (σ.hasSum_iff (f := fun i => lam i * ⟪b i, f⟫_ℝ ^ 2)).mpr (hsd.energy f Y hY)
    convert h1 using 1
    ext n
    simp only [Function.comp, he, real_inner_smul_left]
    have := hs2 (σ n)
    calc lam (σ n) * (s (σ n) * ⟪b (σ n), f⟫_ℝ) ^ 2
        = lam (σ n) * ⟪b (σ n), f⟫_ℝ ^ 2 * (s (σ n) * s (σ n)) := by ring
      _ = _ := by rw [this, mul_one]

theorem exists_zero_mode (hd : 0 < d) (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hint : ∫ x, w x ∂haar d = 1)
    (b : HilbertBasis ι ℝ (Hw d w)) (hsd : SpectralData w b lam G) :
    ∃ i0 : ι, lam i0 = 0 ∧ (∀ i, lam i = 0 → i = i0) ∧
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        ((b i0 : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] fun _ => a := by
  classical
  have := DGPS.Lipschitz.WeightedGenerator.isFiniteMeasure_wMeasure hwb
  set one : Hw d w := DGPS.Lipschitz.WeightedGenerator.oneLp (wMeasure d w) with hone
  have hone1 : ((one : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] fun _ => 1 :=
    DGPS.Lipschitz.WeightedGenerator.coeFn_oneLp
  have hog : IsWeakGradient ((one : Hw d w) : Torus d → ℝ) (fun _ => 0) :=
    (isWeakGradient_const (d := d) 1).congr_ae (ae_eq_haar hc hwb hone1).symm
      (Filter.EventuallyEq.refl _ _)
  have hz : ∀ i, lam i * ⟪b i, one⟫_ℝ = 0 := by
    intro i
    rw [← hsd.eig i one _ hog]
    unfold weightedForm
    simp
  have hnorm : ⟪one, one⟫_ℝ = 1 := by
    rw [inner_Lp_wMeasure hw hc hwb]
    refine Eq.trans ?_ hint
    refine integral_congr_ae ?_
    filter_upwards [ae_eq_haar hc hwb hone1] with x hx
    rw [hx]
    simp
  have hsum := b.hasSum_inner_mul_inner one one
  obtain ⟨i0, hi0⟩ : ∃ i0, ⟪b i0, one⟫_ℝ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : HasSum (fun i => ⟪one, b i⟫_ℝ * ⟪b i, one⟫_ℝ) 0 := by
      simp [hcon]
    have := hsum.unique h0
    rw [hnorm] at this
    exact one_ne_zero this
  have hl0 : lam i0 = 0 := by
    rcases mul_eq_zero.mp (hz i0) with h | h
    · exact h
    · exact absurd h hi0
  have huniq : ∀ i, lam i = 0 → i = i0 := by
    intro i hi
    by_contra hne
    have := weyl_bound hd hw hc hwb hsd {i, i0} 0 le_rfl (by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi.le
      · rw [Finset.mem_singleton.mp hj]; exact hl0.le) (by
      rw [Finset.card_pair hne])
    rw [Finset.card_pair hne] at this
    have h2 : (0 : ℝ) < 4 * π ^ 2 * c / (25 * C) * ((2 : ℕ) : ℝ) ^ (2 / (d : ℝ)) := by
      obtain ⟨x0, hx0⟩ := hwb.exists
      have hC : 0 < C := hc.trans_le (hx0.1.trans hx0.2)
      have : 0 < π := Real.pi_pos
      positivity
    linarith
  have hother : ∀ i, i ≠ i0 → ⟪b i, one⟫_ℝ = 0 := by
    intro i hi
    rcases mul_eq_zero.mp (hz i) with h | h
    · exact absurd (huniq i h) hi
    · exact h
  have h1 : HasSum (fun i => ⟪one, b i⟫_ℝ * ⟪b i, one⟫_ℝ) (⟪one, b i0⟫_ℝ * ⟪b i0, one⟫_ℝ) :=
    hasSum_single i0 (fun i hi => by rw [hother i hi, mul_zero])
  have h2 := hsum.unique h1
  rw [hnorm, real_inner_comm] at h2
  set a := ⟪b i0, one⟫_ℝ with ha
  have ha2 : a * a = 1 := h2.symm
  have h3 : HasSum (fun i => b.repr one i • b i) (b.repr one i0 • b i0) :=
    hasSum_single i0 (fun i hi => by rw [HilbertBasis.repr_apply_apply, hother i hi, zero_smul])
  have h4 := (b.hasSum_repr one).unique h3
  rw [HilbertBasis.repr_apply_apply] at h4
  have ha1 : a = 1 ∨ a = -1 := by
    have : (a - 1) * (a + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  refine ⟨i0, hl0, huniq, a, ha1, ?_⟩
  have h5 : b i0 = a • one := by
    have : a • one = a • (a • b i0) := by rw [← h4]
    rw [this, smul_smul, ha2, one_smul]
  rw [h5]
  filter_upwards [ae_eq_wMeasure (w := w) (Lp.coeFn_smul a one |> ae_eq_haar hc hwb),
    hone1] with x hx1 hx2
  rw [hx1]
  simp [hx2]

end Counting

/-- LIP009.  For a measurable weight `c ≤ w ≤ C` (a.e.) on `𝕋^d` (`0 < d`, `c > 0`) with `∫ w = 1`,
the weighted form `E_μ(f) = ∫ ‖∇f‖² w`, `μ = w m`, has an orthonormal eigenbasis `e_0 = 1, e_1, …`
of `L²(μ)`, with `0 = λ₀ < λ₁ ≤ λ₂ ≤ …`, `λ_j → ∞` and the Weyl lower bound
`λ_j ≥ (4π² c / (25 C)) j^{2/d}` for `j ≥ 1`.  Eigenfunctions are weak eigenfunctions
(`E_μ(e_j, f) = λ_j ⟨e_j, f⟩` for every `f ∈ H¹`), and `E_μ(f) = ∑ λ_j ⟨f, e_j⟩²` on `H¹(μ)`. -/
theorem weighted_eigenbasis_and_growth (hd : 0 < d) (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hint : ∫ x, w x ∂haar d = 1) :
    ∃ (e : HilbertBasis ℕ ℝ (Hw d w)) (lam : ℕ → ℝ) (G : ℕ → Torus d → Tangent d),
      (((e 0 : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] fun _ => 1) ∧
      lam 0 = 0 ∧ lam 0 < lam 1 ∧ Monotone lam ∧ Tendsto lam atTop atTop ∧
      (∀ j, IsWeakGradient ((e j : Hw d w) : Torus d → ℝ) (G j)) ∧
      (∀ j (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
        weightedForm w (G j) Y = lam j * ⟪e j, f⟫_ℝ) ∧
      (∀ (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
        HasSum (fun j => lam j * ⟪e j, f⟫_ℝ ^ 2) (weightedForm w Y Y)) ∧
      (∀ j : ℕ, 1 ≤ j → 4 * π ^ 2 * c / (25 * C) * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j) := by
  classical
  obtain ⟨ι, b, lam, G, hsd⟩ := exists_spectralData hw hc hwb
  have hcnt := countable_index hd hw hc hwb hsd
  have hinf := infinite_index b hd hc hwb
  obtain ⟨σ, hσ⟩ := exists_enum lam fun L => by
    by_cases hL : 0 ≤ L
    · exact finite_sublevel hd hw hc hwb hsd L hL
    · convert Set.finite_empty
      ext i
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun h => hL ((hsd.nonneg i).trans h)
  obtain ⟨i0, hl0, huniq, a, ha, hb0⟩ := exists_zero_mode hd hw hc hwb hint b hsd
  let s : ι → ℝ := fun i => if i = i0 then a else 1
  have hs : ∀ i, s i = 1 ∨ s i = -1 := fun i => by
    by_cases h : i = i0
    · simp only [s, h, ite_true]; exact ha
    · simp [s, h]
  obtain ⟨e, G', he, hsd'⟩ := exists_reindex hc hwb b σ s hs hsd
  obtain ⟨x0, hx0⟩ := hwb.exists
  have hC : 0 < C := hc.trans_le (hx0.1.trans hx0.2)
  have hpi : 0 < π := Real.pi_pos
  have hmono : Monotone fun n => lam (σ n) := hσ
  have hσ0 : σ 0 = i0 := by
    apply huniq
    obtain ⟨m, hm⟩ := σ.surjective i0
    have h1 : lam (σ 0) ≤ lam (σ m) := hmono (Nat.zero_le m)
    rw [hm, hl0] at h1
    exact le_antisymm h1 (hsd.nonneg _)
  have hgrow : ∀ j : ℕ, 1 ≤ j →
      4 * π ^ 2 * c / (25 * C) * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam (σ j) := by
    intro j hj
    have hcard : (Finset.image σ (Finset.range (j + 1))).card = j + 1 := by
      rw [Finset.card_image_of_injective _ σ.injective, Finset.card_range]
    have h := weyl_bound hd hw hc hwb hsd (Finset.image σ (Finset.range (j + 1))) (lam (σ j))
      (hsd.nonneg _) (by
        intro i hi
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hi
        exact hmono (by have := Finset.mem_range.mp hn; omega)) (by rw [hcard]; omega)
    rw [hcard] at h
    refine le_trans ?_ h
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ j)
      (by positivity)
  refine ⟨e, fun n => lam (σ n), G', ?_, ?_, ?_, hmono, ?_, hsd'.grad, hsd'.eig, hsd'.energy,
    hgrow⟩
  · rw [he, hσ0]
    have hs0 : s i0 = a := by simp [s]
    rw [hs0]
    have h1 : ∀ᵐ x ∂(wMeasure d w), ((a • b i0 : Hw d w) : Torus d → ℝ) x = a * a := by
      filter_upwards [Lp.coeFn_smul a (b i0), hb0] with x hx1 hx2
      rw [hx1]
      simp [hx2]
    filter_upwards [h1] with x hx
    rw [hx]
    rcases ha with h | h <;> rw [h] <;> norm_num
  · simpa [hσ0] using hl0
  · have hne : σ 1 ≠ i0 := by
      rw [← hσ0]
      exact fun h => absurd (σ.injective h) (by norm_num)
    have h1 : lam (σ 1) ≠ 0 := fun h => hne (huniq _ h)
    have h2 : 0 ≤ lam (σ 1) := hsd.nonneg _
    have h3 : lam (σ 0) = 0 := by rw [hσ0]; exact hl0
    show lam (σ 0) < lam (σ 1)
    rw [h3]
    exact lt_of_le_of_ne h2 (Ne.symm h1)
  · have hA : 0 < 4 * π ^ 2 * c / (25 * C) := by positivity
    have ht : Tendsto (fun n : ℕ => 4 * π ^ 2 * c / (25 * C) * (n : ℝ) ^ (2 / (d : ℝ))) atTop
        atTop :=
      Tendsto.const_mul_atTop hA ((tendsto_rpow_atTop (by positivity : 0 < 2 / (d : ℝ))).comp
        tendsto_natCast_atTop_atTop)
    exact tendsto_atTop_mono' atTop
      ((eventually_ge_atTop 1).mono fun n hn => hgrow n hn) ht

end Concrete
end DGPS.Lipschitz.WeightedSpectrum
