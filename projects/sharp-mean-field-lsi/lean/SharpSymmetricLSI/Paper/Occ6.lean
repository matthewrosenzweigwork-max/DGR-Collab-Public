import SharpSymmetricLSI.Paper.Occ5
import SharpSymmetricLSI.Paper.Tensorize

/-!
# Weak gradients of block tensor products (Phase 3, lane D; R28)

For `uᵢ ∈ W^{1,1}(𝕋^d)`, the function `y ↦ ∏ᵢ uᵢ(yᵢ)` on `𝕋^{N×d}` has weak gradient
`∂_{(i,k)} = ∂ₖuᵢ(yᵢ) ∏_{j≠i} uⱼ(yⱼ)`: mollify each factor (smooth product rule), and pass to the
limit in `L¹` (block integrals factorize; telescoping estimate for products).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {N d : ℕ}

/-- `y ↦ ∏ᵢ aᵢ(yᵢ)` on `𝕋^{N×d}`. -/
def blockProd (a : Fin N → Torus d → ℝ) (y : UnitAddTorus (Fin N × Fin d)) : ℝ :=
  ∏ i, a i (projBlock i y)

theorem blockProd_flat (a : Fin N → Torus d → ℝ) (X : Config N d) :
    blockProd a (flat X) = ∏ i, a i (X i) := rfl

theorem measurePreserving_flatD :
    MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
  ⟨measurable_flat, map_flat_volume N⟩

theorem integrable_blockProd {a : Fin N → Torus d → ℝ} (ha : ∀ i, Integrable (a i) volume) :
    Integrable (blockProd a) volume := by
  rw [← measurePreserving_flatD.integrable_comp_emb (MeasurableEquiv.measurableEmbedding
    ⟨⟨flat, unflat, fun _ => rfl, fun _ => rfl⟩, measurable_flat, measurable_unflat⟩)]
  exact Integrable.fintype_prod (f := fun i x => a i x) ha

theorem integral_blockProd (a : Fin N → Torus d → ℝ) :
    ∫ y, blockProd a y = ∏ i, ∫ x, a i x := by
  rw [← measurePreserving_flatD.integral_comp (MeasurableEquiv.measurableEmbedding
    ⟨⟨flat, unflat, fun _ => rfl, fun _ => rfl⟩, measurable_flat, measurable_unflat⟩)]
  exact integral_fintype_prod_eq_prod (f := fun i x => a i x)

/-- Telescoping estimate for products. -/
theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| * ∏ j ∈ s.erase i, (|a j| + |b j|) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx, Finset.erase_insert hx]
    have h1 : |∏ i ∈ s, a i| ≤ ∏ j ∈ s, (|a j| + |b j|) := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => by
        linarith [abs_nonneg (b j)]
    have hrest : ∀ i ∈ s, ∏ j ∈ (insert x s).erase i, (|a j| + |b j|) =
        (|a x| + |b x|) * ∏ j ∈ s.erase i, (|a j| + |b j|) := fun i hi => by
      have hne : x ≠ i := by rintro rfl; exact hx hi
      rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => hx (Finset.mem_of_mem_erase h))]
    rw [Finset.sum_congr rfl fun i hi => by rw [hrest i hi], ]
    calc |a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i|
        = |(a x - b x) * ∏ i ∈ s, a i + b x * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| := by ring_nf
      _ ≤ |a x - b x| * |∏ i ∈ s, a i| + |b x| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
      _ ≤ |a x - b x| * ∏ j ∈ s, (|a j| + |b j|) +
            (|a x| + |b x|) * ∑ i ∈ s, |a i - b i| * ∏ j ∈ s.erase i, (|a j| + |b j|) := by
          gcongr
          · linarith [abs_nonneg (a x)]
      _ = _ := by
          rw [Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => by ring

/-- `L¹` convergence of block products. -/
theorem tendsto_blockProd {a : ℕ → Fin N → Torus d → ℝ} {b : Fin N → Torus d → ℝ}
    (ha : ∀ n i, Integrable (a n i) volume) (hb : ∀ i, Integrable (b i) volume)
    (hlim : ∀ i, Tendsto (fun n => ∫⁻ x, ‖a n i x - b i x‖ₑ) atTop (𝓝 0))
    (hbd : ∀ n i, ∫ x, |a n i x| ≤ ∫ x, |b i x|) :
    Tendsto (fun n => ∫⁻ y, ‖blockProd (a n) y - blockProd b y‖ₑ) atTop (𝓝 0) := by
  -- the real `L¹` distances
  have hlim' : ∀ i, Tendsto (fun n => ∫ x, |a n i x - b i x|) atTop (𝓝 0) := fun i => by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim i)
    simp only [ENNReal.toReal_zero] at h
    refine h.congr fun n => ?_
    simp only [Function.comp]
    rw [← integral_norm_eq_lintegral_enorm (f := fun x => a n i x - b i x)
      ((ha n i).sub (hb i)).aestronglyMeasurable]
    rfl
  set H : ℕ → UnitAddTorus (Fin N × Fin d) → ℝ := fun n y =>
    ∑ i, |a n i (projBlock i y) - b i (projBlock i y)| *
      ∏ j ∈ Finset.univ.erase i, (|a n j (projBlock j y)| + |b j (projBlock j y)|)
  have hterm : ∀ n i, Integrable (fun y : UnitAddTorus (Fin N × Fin d) =>
      |a n i (projBlock i y) - b i (projBlock i y)| *
        ∏ j ∈ Finset.univ.erase i, (|a n j (projBlock j y)| + |b j (projBlock j y)|)) volume := by
    intro n i
    have := integrable_blockProd (N := N) (d := d)
      (a := fun j => if j = i then fun x => |a n i x - b i x| else fun x => |a n j x| + |b j x|)
      fun j => by
        by_cases h : j = i
        · subst h; simp only [if_true]; exact ((ha n j).sub (hb j)).abs
        · simp only [h, if_false]; exact (ha n j).abs.add (hb j).abs
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [blockProd]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [if_true]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  have hHi : ∀ n, Integrable (H n) volume := fun n =>
    integrable_finsetSum _ fun i _ => hterm n i
  have hHint : ∀ n, ∫ y, H n y = ∑ i, (∫ x, |a n i x - b i x|) *
      ∏ j ∈ Finset.univ.erase i, ((∫ x, |a n j x|) + ∫ x, |b j x|) := fun n => by
    simp only [H]
    rw [integral_finsetSum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have := integral_blockProd (N := N) (d := d)
        (fun j => if j = i then fun x => |a n i x - b i x| else fun x => |a n j x| + |b j x|)
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at this
      simp only [if_true] at this
      convert this using 1
      · congr 1; funext y
        simp only [blockProd]
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        simp only [if_true]
        congr 1
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [if_neg (Finset.ne_of_mem_erase hj)]
      · congr 1
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [if_neg (Finset.ne_of_mem_erase hj), integral_add (ha n j).abs (hb j).abs]
    · exact hterm n i
  -- the bound and the limit
  have hle : ∀ n, ∫⁻ y, ‖blockProd (a n) y - blockProd b y‖ₑ ≤ ENNReal.ofReal (∫ y, H n y) := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal (hHi n) (Eventually.of_forall fun y =>
      Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun j _ =>
        add_nonneg (abs_nonneg _) (abs_nonneg _)))]
    refine lintegral_mono fun y => ?_
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (abs_prod_sub_prod_le _ _ _)
  set C : Fin N → ℝ := fun i => ∏ j ∈ Finset.univ.erase i, (2 * ∫ x, |b j x|)
  have hHle : ∀ n, ∫ y, H n y ≤ ∑ i, (∫ x, |a n i x - b i x|) * C i := fun n => by
    rw [hHint n]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (integral_nonneg fun _ =>
      abs_nonneg _)
    refine Finset.prod_le_prod₀ (fun j _ => add_nonneg (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _)) fun j _ => ?_
    linarith [hbd n j]
  have hH0 : ∀ n, 0 ≤ ∫ y, H n y := fun n => integral_nonneg fun y =>
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun j _ =>
      add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hsum : Tendsto (fun n => ∑ i, (∫ x, |a n i x - b i x|) * C i) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin N)) fun i _ => (hlim' i).mul_const (C i)
    simpa using this
  have hHt : Tendsto (fun n => ∫ y, H n y) atTop (𝓝 0) :=
    squeeze_zero hH0 hHle hsum
  have hHt' := (ENNReal.continuous_ofReal.tendsto 0).comp hHt
  rw [ENNReal.ofReal_zero] at hHt'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hHt'
    (fun n => bot_le) hle


theorem blockProd_update (f : Fin N → Torus d → ℝ) (i : Fin N) (h : Torus d → ℝ)
    (y : UnitAddTorus (Fin N × Fin d)) :
    blockProd (Function.update f i h) y = h (projBlock i y) * ∏ j ∈ Finset.univ.erase i, f j (projBlock j y) := by
  unfold blockProd
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem integral_abs_moll_le (n : ℕ) {u : Torus d → ℝ} (hu : Integrable u volume) :
    ∫ x, |moll n u x| ≤ ∫ x, |u x| := by
  have e1 := integral_norm_eq_lintegral_enorm (integrable_moll n hu).aestronglyMeasurable
  have e2 := integral_norm_eq_lintegral_enorm hu.aestronglyMeasurable
  simp only [Real.norm_eq_abs] at e1 e2
  rw [e1, e2]
  exact ENNReal.toReal_mono hu.2.ne (lintegral_moll_le n hu)

/-- **The weak gradient of a block tensor product.** -/
theorem isWeakGrad_blockProd (u : Fin N → Torus d → ℝ) (g : Fin N → Torus d → Fin d → ℝ)
    (hw : ∀ i, IsWeakGrad (u i) (g i)) (hu : ∀ i, Integrable (u i) volume)
    (hg : ∀ i k, Integrable (fun x => g i x k) volume) :
    IsWeakGrad (blockProd u) (fun y p => blockProd (Function.update u p.1 (fun x => g p.1 x p.2)) y) := by
  set m : ℕ → Fin N → Torus d → ℝ := fun n i => moll n (u i)
  set G : ℕ → UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ := fun n y p =>
    blockProd (Function.update (m n) p.1 (moll n fun x => g p.1 x p.2)) y
  have hΨ : ∀ n i, ContDiff ℝ ∞ (moll n (u i) ∘ liftT) := fun n i => moll_comp_liftT_contDiff n (hu i)
  have hpair : ∀ n, IsWeakGrad (blockProd (m n)) (G n) := by
    intro n
    have hlift : blockProd (m n) ∘ liftT = fun x => ∏ i, (moll n (u i) ∘ liftT) (projBlockL i x) := by
      funext x; simp [blockProd, m, Function.comp, projBlock_liftT]
    have hs : ContDiff ℝ 1 (blockProd (m n) ∘ liftT) := by
      rw [hlift]
      exact contDiff_prod fun i _ => ((hΨ n i).of_le (by simp)).comp (projBlockL i).contDiff
    have hc := isWeakGrad_of_contDiff hs
    convert hc using 1
    funext y p
    have hd : HasFDerivAt (fun x => ∏ i, (moll n (u i) ∘ liftT) (projBlockL i x))
        (∑ i, (∏ j ∈ Finset.univ.erase i, (moll n (u j) ∘ liftT) (projBlockL j (secT y))) •
          ((fderiv ℝ (moll n (u i) ∘ liftT) (projBlockL i (secT y))).comp (projBlockL i)))
        (secT y) := by
      refine HasFDerivAt.finsetProd fun i _ => ?_
      exact (((hΨ n i).differentiable (by simp)) _).hasFDerivAt.comp _ (projBlockL i).hasFDerivAt
    rw [hlift, hd.fderiv]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, projBlockL_single, smul_eq_mul]
    rw [Finset.sum_eq_single p.1]
    · simp only [if_true]
      simp only [G]
      rw [blockProd_update]
      have hlb : ∀ j, liftT (projBlockL j (secT y)) = projBlock j y := fun j => by
        rw [← projBlock_liftT, liftT_secT]
      rw [moll_comp_liftT, fderiv_mollL_of_isWeakGrad (hw p.1) n _ p.2, mul_comm]
      congr 1
      · refine Finset.prod_congr rfl fun j _ => ?_
        simp only [Function.comp, hlb, m]
    · intro i _ hi
      rw [if_neg (Ne.symm hi)]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  refine isWeakGrad_of_tendsto hpair (fun n => integrable_blockProd fun i => integrable_moll n (hu i))
    (fun n p => integrable_blockProd fun j => ?_) (integrable_blockProd hu)
    (fun p => integrable_blockProd fun j => ?_) ?_ (fun p => ?_)
  · by_cases hj : j = p.1
    · subst hj; rw [Function.update_self]; exact integrable_moll n (hg _ _)
    · rw [Function.update_of_ne hj]; exact integrable_moll n (hu j)
  · by_cases hj : j = p.1
    · subst hj; rw [Function.update_self]; exact hg _ _
    · rw [Function.update_of_ne hj]; exact hu j
  · exact tendsto_blockProd (fun n i => integrable_moll n (hu i)) hu (fun i => tendsto_moll (hu i))
      fun n i => integral_abs_moll_le n (hu i)
  · refine tendsto_blockProd (a := fun n => Function.update (m n) p.1 (moll n fun x => g p.1 x p.2))
      (b := Function.update u p.1 (fun x => g p.1 x p.2)) (fun n j => ?_) (fun j => ?_)
      (fun j => ?_) (fun n j => ?_)
    · by_cases hj : j = p.1
      · subst hj; rw [Function.update_self]; exact integrable_moll n (hg _ _)
      · rw [Function.update_of_ne hj]; exact integrable_moll n (hu j)
    · by_cases hj : j = p.1
      · subst hj; rw [Function.update_self]; exact hg _ _
      · rw [Function.update_of_ne hj]; exact hu j
    · by_cases hj : j = p.1
      · subst hj; simp only [Function.update_self]; exact tendsto_moll (hg _ _)
      · simp only [Function.update_of_ne hj, m]; exact tendsto_moll (hu j)
    · by_cases hj : j = p.1
      · subst hj; simp only [Function.update_self]; exact integral_abs_moll_le n (hg _ _)
      · simp only [Function.update_of_ne hj, m]; exact integral_abs_moll_le n (hu j)

end SharpLSI
