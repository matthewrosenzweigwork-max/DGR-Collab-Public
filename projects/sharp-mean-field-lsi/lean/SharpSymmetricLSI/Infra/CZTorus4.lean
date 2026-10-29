import SharpSymmetricLSI.Infra.CZTorus3

/-!
# The `L^{2^{m+1}}` estimate `‖∂_i∂_j u‖ ≤ A ‖Δu‖` on `𝕋^ι` (R23 lane, CZ part 4)

On trigonometric polynomials `∂_i∂_j = -R_iR_jΔ` (symbols), so `riesz_bound` gives
`‖∂_i∂_j P‖_{2^{m+1}} ≤ A²‖ΔP‖_{2^{m+1}}` (`cz_trig`). For `u` with `C²` lift and
`∑ₖ |k|²|û(k)| < ∞` the Fourier series of `∂_i∂_j u` and `Δu` converge uniformly, and the
estimate passes to the limit along the boxes `[-R,R]^ι` (`cz_smooth`).
-/

open MeasureTheory Complex Filter Topology
open scoped ENNReal ComplexConjugate Real
open UnitAddTorus

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Classical partial derivatives -/

/-- The classical partial derivative `∂_i u` (on the lift, at the section `secT`). -/
noncomputable def dpart (u : UnitAddTorus ι → ℝ) (i : ι) (y : UnitAddTorus ι) : ℝ :=
  fderiv ℝ (u ∘ liftT) (secT y) (Pi.single i 1)

theorem dpart_liftT (u : UnitAddTorus ι → ℝ) (i : ι) (x : ι → ℝ) :
    dpart u i (liftT x) = fderiv ℝ (u ∘ liftT) x (Pi.single i 1) := by
  simp only [dpart, fderiv_lift_secT]

theorem dpart_comp_liftT (u : UnitAddTorus ι → ℝ) (i : ι) :
    dpart u i ∘ liftT = fun x => fderiv ℝ (u ∘ liftT) x (Pi.single i 1) :=
  funext fun x => dpart_liftT u i x

theorem contDiff_dpart {n : ℕ} {u : UnitAddTorus ι → ℝ} (hu : ContDiff ℝ (n + 1) (u ∘ liftT))
    (i : ι) : ContDiff ℝ n (dpart u i ∘ liftT) := by
  rw [dpart_comp_liftT]
  exact (hu.fderiv_right (by norm_cast)).clm_apply contDiff_const

theorem continuous_of_liftT' {f : UnitAddTorus ι → ℝ} (h : Continuous (f ∘ liftT)) :
    Continuous f :=
  (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff.mp h

theorem cf_dpart {u : UnitAddTorus ι → ℝ} (hu : ContDiff ℝ 1 (u ∘ liftT)) (i : ι) (k : ι → ℤ) :
    mFourierCoeff (fun y => (dpart u i y : ℂ)) k =
      2 * π * I * k i * mFourierCoeff (fun y => (u y : ℂ)) k :=
  mFourierCoeff_grad_of_contDiff hu k i

/-- The classical Laplacian. -/
noncomputable def lap (u : UnitAddTorus ι → ℝ) (y : UnitAddTorus ι) : ℝ :=
  ∑ i, dpart (dpart u i) i y

/-! ### Symbols -/

/-- The symbol of `∂_i∂_j`. -/
noncomputable def d2Sym (i j : ι) (k : ι → ℤ) : ℂ := -(4 * π ^ 2 * (k i : ℂ) * (k j : ℂ))

/-- The symbol of `Δ`. -/
noncomputable def lapSym (k : ι → ℤ) : ℂ := -(4 * π ^ 2 * ∑ i, ((k i : ℂ)) ^ 2)

theorem norm_kvec_sq (k : ι → ℤ) : ‖kvec k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2 := by
  rw [kvec, EuclideanSpace.norm_sq_eq]
  simp

theorem d2Sym_eq (i j : ι) (k : ι → ℤ) :
    d2Sym i j k = -(rieszSym i k * (rieszSym j k * lapSym k)) := by
  by_cases hk : k = 0
  · subst hk; simp [d2Sym, rieszSym, lapSym]
  have hn : ‖kvec k‖ ≠ 0 := norm_ne_zero_iff.mpr (kvec_ne_zero hk)
  have hsq : (∑ i, ((k i : ℂ)) ^ 2) = ((‖kvec k‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_kvec_sq]; push_cast; rfl
  simp only [d2Sym, rieszSym, lapSym, hsq]
  push_cast
  have hn' : ((‖kvec k‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp
  rw [show (I : ℂ) ^ 2 = -1 from I_sq]
  ring

/-- **The estimate on trigonometric polynomials.** -/
theorem cz_trig (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ (c : TP ι) (i j : ι),
    nr (2 ^ (m + 1)) (synth (mult (d2Sym i j) c)) ≤
      A * nr (2 ^ (m + 1)) (synth (mult lapSym c)) := by
  obtain ⟨B, hB0, hB⟩ := riesz_bound (ι := ι) m
  refine ⟨B * B, mul_nonneg hB0 hB0, fun c i j => ?_⟩
  have e : mult (d2Sym i j) c = -(mult (rieszSym i) (mult (rieszSym j) (mult lapSym c))) := by
    rw [mult_mult, mult_mult, ← map_neg]
    apply AddMonoidAlgebra.coeff_injective
    ext k
    simp only [mult_coeff, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, d2Sym_eq]
    ring
  rw [e, map_neg]
  have hneg : nr (2 ^ (m + 1)) (-synth (mult (rieszSym i) (mult (rieszSym j) (mult lapSym c)))) =
      nr (2 ^ (m + 1)) (synth (mult (rieszSym i) (mult (rieszSym j) (mult lapSym c)))) := by
    unfold nr; rw [eLpNorm_neg]
  rw [hneg]
  calc nr (2 ^ (m + 1)) (synth (mult (rieszSym i) (mult (rieszSym j) (mult lapSym c))))
      ≤ B * nr (2 ^ (m + 1)) (synth (mult (rieszSym j) (mult lapSym c))) := hB i _
    _ ≤ B * (B * nr (2 ^ (m + 1)) (synth (mult lapSym c))) :=
        mul_le_mul_of_nonneg_left (hB j _) hB0
    _ = B * B * nr (2 ^ (m + 1)) (synth (mult lapSym c)) := by ring

/-! ### Passage to smooth functions -/

/-- The truncation of a coefficient family to a finite set, as a trigonometric polynomial. -/
noncomputable def truncTP (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ) : TP ι :=
  AddMonoidAlgebra.ofCoeff (Finsupp.onFinset S (fun k => if k ∈ S then a k else 0)
    (fun k hk => by by_contra h; exact hk (if_neg h)))

theorem synth_mult_truncTP (m : (ι → ℤ) → ℂ) (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ)
    (x : UnitAddTorus ι) :
    synth (mult m (truncTP S a)) x = ∑ k ∈ S, m k * a k * mFourier k x := by
  have hsub : (mult m (truncTP S a)).coeff.support ⊆ S := by
    refine (mult_support _ _).trans fun k hk => ?_
    simp only [truncTP, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.mem_support_iff,
      Finsupp.onFinset_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at hk
    exact hk.1
  rw [synth_apply_of_subset _ hsub]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp [truncTP, mult_coeff, Finsupp.onFinset_apply, hk]

/-- A continuous function with absolutely summable Fourier coefficients is uniformly approximated
by its box partial sums. -/
theorem norm_sub_box_le {f : UnitAddTorus ι → ℂ} (hf : Continuous f)
    (hs : Summable fun k => ‖mFourierCoeff f k‖) (R : ℕ) (x : UnitAddTorus ι) :
    ‖f x - ∑ k ∈ box R, mFourierCoeff f k * mFourier k x‖ ≤
      ∑' k, if k ∈ box R then 0 else ‖mFourierCoeff f k‖ := by
  set F : C(UnitAddTorus ι, ℂ) := ⟨f, hf⟩
  have hsF : Summable (mFourierCoeff F) := hs.of_norm
  have hx := hasSum_mFourier_series_apply_of_summable hsF x
  have hsx : Summable fun k => mFourierCoeff f k * mFourier k x :=
    (hs.mul_right 1).of_norm_bounded fun k => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_mFourier_le k x) (norm_nonneg _)
  have hfx : f x = ∑' k, mFourierCoeff f k * mFourier k x := by
    have := hx.tsum_eq
    simp only [smul_eq_mul] at this
    exact this.symm
  rw [hfx, tsum_split_boxC hsx R, add_sub_cancel_left]
  have hle : ∀ k, ‖(if k ∈ box R then 0 else mFourierCoeff f k * mFourier k x)‖ ≤
      if k ∈ box R then 0 else ‖mFourierCoeff f k‖ := by
    intro k
    split_ifs
    · simp
    · rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_mFourier_le k x)
  have hs2 : Summable fun k => if k ∈ box R then (0 : ℝ) else ‖mFourierCoeff f k‖ :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity)
      (fun k => by split_ifs <;> simp) hs
  have hs1 : Summable fun k => ‖(if k ∈ box R then 0 else mFourierCoeff f k * mFourier k x)‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hs2
  exact (norm_tsum_le_tsum_norm hs1).trans (hs1.tsum_le_tsum hle hs2)

theorem nr_add_le' {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : UnitAddTorus ι → ℂ} (hf : MemLp f p volume)
    (hg : MemLp g p volume) : nr p (f + g) ≤ nr p f + nr p g := by
  unfold nr
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hp)

theorem nr_le_of_bound {p : ℝ≥0∞} {f : UnitAddTorus ι → ℂ} (hf : AEStronglyMeasurable f volume)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : nr p f ≤ C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  unfold nr
  have := eLpNorm_le_of_ae_bound (p := p) hf (Filter.Eventually.of_forall hC)
  rw [measure_univ, ENNReal.one_rpow, one_mul] at this
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top this).trans (by rw [ENNReal.toReal_ofReal hC0])

/-- The estimate, approximating `f` by `S` in sup norm. -/
theorem nr_le_nr_add_of_sup {p : ℝ≥0∞} (hp : 1 ≤ p) {f S : UnitAddTorus ι → ℂ}
    (hf : Continuous f) (hS : Continuous S) {t : ℝ} (ht : ∀ x, ‖f x - S x‖ ≤ t) :
    nr p f ≤ nr p S + t := by
  have h1 : f = S + (f - S) := by abel
  have hfS : MemLp (f - S) p volume :=
    MemLp.of_bound (hf.sub hS).aestronglyMeasurable t (Filter.Eventually.of_forall ht)
  have hSm : MemLp S p volume := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hS).isBounded.exists_norm_le
    exact MemLp.of_bound hS.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => hC _ ⟨x, Set.mem_univ _, rfl⟩)
  calc nr p f = nr p (S + (f - S)) := by rw [← h1]
    _ ≤ nr p S + nr p (f - S) := nr_add_le' hp hSm hfS
    _ ≤ nr p S + t := by
        gcongr
        exact nr_le_of_bound (hf.sub hS).aestronglyMeasurable fun x => by simpa using ht x

theorem continuous_synth_sum (S : Finset (ι → ℤ)) (b : (ι → ℤ) → ℂ) :
    Continuous fun x : UnitAddTorus ι => ∑ k ∈ S, b k * mFourier k x := by fun_prop

/-- **The estimate for `C²` functions with `∑ |k|²|û(k)| < ∞`.** -/
theorem cz_smooth (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ (u : UnitAddTorus ι → ℝ),
    ContDiff ℝ 2 (u ∘ liftT) →
    Summable (fun k => (∑ i, ((k i : ℝ)) ^ 2) * ‖mFourierCoeff (fun y => (u y : ℂ)) k‖) →
    ∀ i j, eLpNorm (dpart (dpart u i) j) (2 ^ (m + 1)) volume ≤
      ENNReal.ofReal A * eLpNorm (lap u) (2 ^ (m + 1)) volume := by
  obtain ⟨A, hA0, hA⟩ := cz_trig (ι := ι) m
  refine ⟨A, hA0, fun u hu hsum i j => ?_⟩
  set p : ℝ≥0∞ := 2 ^ (m + 1) with hp
  have hp1 : 1 ≤ p := one_le_pow₀ (by norm_num)
  set a : (ι → ℤ) → ℂ := mFourierCoeff fun y => (u y : ℂ) with ha
  have hu1 : ContDiff ℝ 1 (u ∘ liftT) := hu.of_le (by norm_num)
  have hdi : ∀ i, ContDiff ℝ 1 (dpart u i ∘ liftT) := fun i => contDiff_dpart (n := 1) hu i
  have hdd : ∀ i j, Continuous (dpart (dpart u i) j) := fun i j =>
    continuous_of_liftT' (contDiff_dpart (n := 0) (hdi i) j).continuous
  set F : UnitAddTorus ι → ℂ := fun y => (dpart (dpart u i) j y : ℂ) with hFdef
  set G : UnitAddTorus ι → ℂ := fun y => (lap u y : ℂ) with hGdef
  have hFc : Continuous F := Complex.continuous_ofReal.comp (hdd i j)
  have hGc : Continuous G := Complex.continuous_ofReal.comp
    (continuous_finset_sum _ fun i _ => hdd i i)
  have hcf2 : ∀ i j k, mFourierCoeff (fun y => (dpart (dpart u i) j y : ℂ)) k = d2Sym i j k * a k := by
    intro i j k
    rw [cf_dpart (hdi i) j k, cf_dpart hu1 i k, d2Sym]
    have : (I : ℂ) * I = -1 := I_mul_I
    linear_combination (4 * π ^ 2 * (k i : ℂ) * (k j : ℂ) * a k) * this
  have hF : ∀ k, mFourierCoeff F k = d2Sym i j k * a k := hcf2 i j
  have hG : ∀ k, mFourierCoeff G k = lapSym k * a k := by
    intro k
    have hint : ∀ l, Integrable (fun t => mFourier (-k) t • (dpart (dpart u l) l t : ℂ)) volume :=
      fun l => ((map_continuous (mFourier (-k))).smul
        (Complex.continuous_ofReal.comp (hdd l l))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have e : (fun t => mFourier (-k) t • G t) =
        fun t => ∑ l, mFourier (-k) t • (dpart (dpart u l) l t : ℂ) := by
      funext t; simp only [hGdef, lap]; push_cast; rw [Finset.smul_sum]
    rw [mFourierCoeff_eq_integral, e, integral_finsetSum _ fun l _ => hint l]
    simp_rw [← mFourierCoeff_eq_integral, hcf2, lapSym, d2Sym, ← Finset.sum_mul]
    simp only [neg_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  -- summability of the coefficients
  have hbF : ∀ k, ‖mFourierCoeff F k‖ ≤ 4 * π ^ 2 * ((∑ i, ((k i : ℝ)) ^ 2) * ‖a k‖) := by
    intro k
    rw [hF, d2Sym, norm_mul, norm_neg]
    have h1 : ‖(4 * π ^ 2 * (k i : ℂ) * (k j : ℂ))‖ ≤ 4 * π ^ 2 * ∑ i, ((k i : ℝ)) ^ 2 := by
      have hn : ‖(4 * π ^ 2 * (k i : ℂ) * (k j : ℂ))‖ =
          4 * π ^ 2 * (|(k i : ℝ)| * |(k j : ℝ)|) := by
        simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Complex.norm_intCast,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        ring
      rw [hn]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hi : ((k i : ℝ)) ^ 2 ≤ ∑ l, ((k l : ℝ)) ^ 2 :=
        Finset.single_le_sum (s := Finset.univ) (f := fun l : ι => ((k l : ℝ)) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      have hj : ((k j : ℝ)) ^ 2 ≤ ∑ l, ((k l : ℝ)) ^ 2 :=
        Finset.single_le_sum (s := Finset.univ) (f := fun l : ι => ((k l : ℝ)) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      nlinarith [sq_abs ((k i : ℝ)), sq_abs ((k j : ℝ)), sq_nonneg (|(k i : ℝ)| - |(k j : ℝ)|)]
    calc ‖4 * π ^ 2 * (k i : ℂ) * (k j : ℂ)‖ * ‖a k‖ ≤ (4 * π ^ 2 * ∑ i, ((k i : ℝ)) ^ 2) * ‖a k‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = _ := by ring
  have hbG : ∀ k, ‖mFourierCoeff G k‖ ≤ 4 * π ^ 2 * ((∑ i, ((k i : ℝ)) ^ 2) * ‖a k‖) := by
    intro k
    rw [hG, lapSym, norm_mul, norm_neg]
    have e : (4 * π ^ 2 * ∑ i, ((k i : ℂ)) ^ 2) = ((4 * π ^ 2 * ∑ i, ((k i : ℝ)) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    ring_nf; rfl
  have hsF : Summable fun k => ‖mFourierCoeff F k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbF (hsum.mul_left _)
  have hsG : Summable fun k => ‖mFourierCoeff G k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbG (hsum.mul_left _)
  -- the estimate along boxes
  set tF : ℕ → ℝ := fun R => ∑' k, if k ∈ box R then 0 else ‖mFourierCoeff F k‖
  set tG : ℕ → ℝ := fun R => ∑' k, if k ∈ box R then 0 else ‖mFourierCoeff G k‖
  have hR : ∀ R, nr p F ≤ A * (nr p G + tG R) + tF R := by
    intro R
    set c := truncTP (box R) a
    have hSF : ∀ x, synth (mult (d2Sym i j) c) x = ∑ k ∈ box R, mFourierCoeff F k * mFourier k x := by
      intro x; rw [synth_mult_truncTP]; simp_rw [hF]
    have hSG : ∀ x, synth (mult lapSym c) x = ∑ k ∈ box R, mFourierCoeff G k * mFourier k x := by
      intro x; rw [synth_mult_truncTP]; simp_rw [hG]
    have h1 : nr p F ≤ nr p (synth (mult (d2Sym i j) c)) + tF R :=
      nr_le_nr_add_of_sup hp1 hFc (continuous_synth _) fun x => by
        rw [hSF]; exact norm_sub_box_le hFc hsF R x
    have h2 : nr p (synth (mult lapSym c)) ≤ nr p G + tG R :=
      nr_le_nr_add_of_sup hp1 (continuous_synth _) hGc fun x => by
        rw [hSG, norm_sub_rev]; exact norm_sub_box_le hGc hsG R x
    calc nr p F ≤ nr p (synth (mult (d2Sym i j) c)) + tF R := h1
      _ ≤ A * nr p (synth (mult lapSym c)) + tF R := by gcongr; exact hA c i j
      _ ≤ A * (nr p G + tG R) + tF R := by gcongr
  have hlim : Tendsto (fun R => A * (nr p G + tG R) + tF R) atTop (𝓝 (A * (nr p G + 0) + 0)) :=
    ((tendsto_tail_box hsG fun _ => norm_nonneg _).const_add _ |>.const_mul _).add
      (tendsto_tail_box hsF fun _ => norm_nonneg _)
  have hFG : nr p F ≤ A * nr p G := by
    have := ge_of_tendsto hlim (Eventually.of_forall hR)
    simpa using this
  -- back to real functions
  have eF : eLpNorm (dpart (dpart u i) j) p volume = eLpNorm F p volume :=
    eLpNorm_congr_norm_ae (hdd i j).aestronglyMeasurable hFc.aestronglyMeasurable
      (Eventually.of_forall fun x => by simp [hFdef])
  have eG : eLpNorm (lap u) p volume = eLpNorm G p volume :=
    eLpNorm_congr_norm_ae (continuous_finset_sum _ fun i _ => hdd i i).aestronglyMeasurable
      hGc.aestronglyMeasurable (Eventually.of_forall fun x => by simp [hGdef])
  have hGm : MemLp G p volume := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hGc).isBounded.exists_norm_le
    exact MemLp.of_bound hGc.aestronglyMeasurable C
      (Eventually.of_forall fun x => hC _ ⟨x, Set.mem_univ _, rfl⟩)
  have hFm : MemLp F p volume := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hFc).isBounded.exists_norm_le
    exact MemLp.of_bound hFc.aestronglyMeasurable C
      (Eventually.of_forall fun x => hC _ ⟨x, Set.mem_univ _, rfl⟩)
  rw [eF, eG, ← ENNReal.ofReal_toReal hFm.eLpNorm_ne_top,
    ← ENNReal.ofReal_toReal hGm.eLpNorm_ne_top, ← ENNReal.ofReal_mul hA0]
  exact ENNReal.ofReal_le_ofReal hFG

end SharpLSI
