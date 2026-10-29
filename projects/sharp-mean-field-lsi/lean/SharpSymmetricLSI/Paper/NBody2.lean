import SharpSymmetricLSI.Paper.NBody1

/-!
# The N-body eigen-identity for smooth functions (Phase 3, lane D; R29 groundwork)

For `F` with `F ∘ liftT ∈ C¹` and a tensor `T_c(X) = ∏ⱼ e_{cⱼ}(Xⱼ)`:
`∫ ∑ₖ ∂_{(i,k)}F · ∂_{(i,k)}T_c dμ^{⊗N} = λ_{c i} ∫ F T_c dμ^{⊗N}` (Fubini over particle `i` and
the weak eigen-equation for the smooth slice).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

/-- Fubini over one coordinate of a finite product. -/
theorem integral_pi_insertNth {n : ℕ} {T : Type*} [MeasurableSpace T] {ν : Measure T}
    [IsProbabilityMeasure ν] (i : Fin (n + 1)) {G : (Fin (n + 1) → T) → ℝ}
    (hG : Integrable G (Measure.pi fun _ => ν)) :
    ∫ X, G X ∂(Measure.pi fun _ => ν) =
      ∫ r, ∫ y, G (Fin.insertNth i y r) ∂ν ∂(Measure.pi fun _ : Fin n => ν) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i
  set E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) i
  have h1 : ∫ X, G X ∂(Measure.pi fun _ => ν) =
      ∫ p, G (E.symm p) ∂(ν.prod (Measure.pi fun _ : Fin n => ν)) := by
    rw [← hmp.symm.integral_comp' (g := G)]
  have hGi : Integrable (fun p => G (E.symm p)) (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
    (hmp.symm.integrable_comp_emb E.symm.measurableEmbedding).mpr hG
  rw [h1, integral_prod_symm _ hGi]
  rfl

section smooth
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : UnitAddTorus ι → ℝ}

theorem exists_bound_of_contDiff (hF : ContDiff ℝ 1 (F ∘ liftT)) : ∃ C, ∀ y, |F y| ≤ C := by
  obtain ⟨C, hC⟩ := periodic_bounded hF.continuous fun m x => lift_periodic F m x
  refine ⟨C, fun y => ?_⟩
  have := hC (secT y)
  rwa [Real.norm_eq_abs, Function.comp_apply, liftT_secT] at this

theorem exists_bound_cgrad (hF : ContDiff ℝ 1 (F ∘ liftT)) : ∃ C, ∀ y p, |cgrad F y p| ≤ C := by
  have hc : Continuous fun x => fderiv ℝ (F ∘ liftT) x :=
    hF.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := periodic_bounded hc fun m x => fderiv_lift_periodic F m x
  refine ⟨C, fun y p => ?_⟩
  unfold cgrad
  calc |fderiv ℝ (F ∘ liftT) (secT y) (Pi.single p 1)|
      ≤ ‖fderiv ℝ (F ∘ liftT) (secT y)‖ * ‖(Pi.single p 1 : ι → ℝ)‖ := by
        rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * 1 := mul_le_mul (hC _) (by rw [Pi.norm_single, norm_one])
          (norm_nonneg _) (le_trans (norm_nonneg _) (hC 0))
    _ = C := mul_one C

theorem measurable_of_contDiff (hF : ContDiff ℝ 1 (F ∘ liftT)) : Measurable F := by
  have : F = (F ∘ liftT) ∘ secT := by funext y; simp [liftT_secT]
  rw [this]
  exact hF.continuous.measurable.comp measurable_secT

theorem measurable_cgrad (hF : ContDiff ℝ 1 (F ∘ liftT)) (p : ι) :
    Measurable fun y => cgrad F y p := by
  unfold cgrad
  have hc : Continuous fun x => fderiv ℝ (F ∘ liftT) x (Pi.single p 1) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact hc.measurable.comp measurable_secT

/-- A bounded `C¹` function on `𝕋^d` is in `H¹(ν)` for `ν ≪ m`. -/
theorem memH1_of_contDiff_ac {ν : Measure (UnitAddTorus ι)} [IsProbabilityMeasure ν]
    (hac : ν ≪ volume) (hF : ContDiff ℝ 1 (F ∘ liftT)) : MemH1 ν F := by
  obtain ⟨C, hC⟩ := exists_bound_of_contDiff hF
  obtain ⟨C', hC'⟩ := exists_bound_cgrad hF
  have hw := isWeakGrad_of_contDiff hF
  have hae : weakGrad F =ᵐ[ν] fun y p => cgrad F y p := hac.ae_le (weakGrad_ae_eq hw)
  refine ⟨⟨_, hw⟩, ?_, ?_⟩
  · exact memLp_of_bounded (a := -C) (b := C) (Eventually.of_forall fun y => abs_le.mp (hC y))
      (measurable_of_contDiff hF).aestronglyMeasurable 2
  · have hm : AEStronglyMeasurable (fun y => Real.sqrt (sqNorm (fun p => cgrad F y p))) ν :=
      (Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun p _ =>
        (measurable_cgrad hF p).pow_const 2)).aestronglyMeasurable
    have hb : MemLp (fun y => Real.sqrt (sqNorm (fun p => cgrad F y p))) 2 ν :=
      memLp_of_bounded (a := -Real.sqrt (Fintype.card ι * C' ^ 2))
        (b := Real.sqrt (Fintype.card ι * C' ^ 2)) (Eventually.of_forall fun y => by
          have h0 := Real.sqrt_nonneg (sqNorm (fun p => cgrad F y p))
          refine ⟨by linarith [Real.sqrt_nonneg (Fintype.card ι * C' ^ 2)],
            Real.sqrt_le_sqrt ?_⟩
          unfold sqNorm
          calc ∑ p, cgrad F y p ^ 2 ≤ ∑ _p : ι, C' ^ 2 :=
                Finset.sum_le_sum fun p _ => by
                  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC' y p) 2
            _ = Fintype.card ι * C' ^ 2 := by simp) hm 2
    exact hb.ae_eq (hae.mono fun y hy => by simp only [hy])

end smooth

section eigen
variable {N d : ℕ} {ν : Measure (Torus d)} [IsProbabilityMeasure ν] (hac : ν ≪ haar d)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis ν e lam)
  {F : UnitAddTorus (Fin N × Fin d) → ℝ} (hF : ContDiff ℝ 1 (F ∘ liftT))
include hac he hF

/-- **Per-particle eigen-identity for smooth `F`.** -/
theorem eigen_tensor_smooth_i (c : Fin N → ℕ) (i : Fin N) :
    ∫ X, ∑ k, cgrad F (flat X) (i, k) * tensorGrad e c i k X ∂(Measure.pi fun _ : Fin N => ν) =
      lam (c i) * ∫ X, F (flat X) * ∏ j, e (c j) (X j) ∂(Measure.pi fun _ : Fin N => ν) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := Nat.exists_eq_succ_of_ne_zero (Fin.pos i).ne'
  set P := Measure.pi fun _ : Fin (n + 1) => ν
  obtain ⟨C, hC⟩ := exists_bound_of_contDiff hF
  obtain ⟨C', hC'⟩ := exists_bound_cgrad hF
  set R : (Fin n → Torus d) → ℝ := fun r => ∏ m, e (c (i.succAbove m)) (r m)
  have hT1 : ∀ y r k, tensorGrad e c i k (Fin.insertNth i y r) =
      R r * weakGrad (e (c i)) y k := fun y r k => by
    unfold tensorGrad
    rw [Fin.prod_univ_succAbove _ i]
    simp only [Function.update_self, Fin.insertNth_apply_same, R]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [Function.update_of_ne (Fin.succAbove_ne i m), Fin.insertNth_apply_succAbove]
  have hT2 : ∀ y r, ∏ j, e (c j) (Fin.insertNth i y r j) = e (c i) y * R r := fun y r => by
    rw [Fin.prod_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, R]
  -- the slices
  set X0 : (Fin n → Torus d) → Config (n + 1) d := fun r => Fin.insertNth i 0 r
  have hS : ∀ y r k, cgrad F (flat (Fin.insertNth i y r)) (i, k) =
      cgrad (sliceF F (X0 r) i) y k := fun y r k => by
    rw [cgrad_sliceF hF, Fin.update_insertNth]
  have hSv : ∀ y r, sliceF F (X0 r) i y = F (flat (Fin.insertNth i y r)) := fun y r => by
    simp only [sliceF, X0, Fin.update_insertNth]
  -- integrability
  have heL1 : ∀ j, Integrable (e j) ν := fun j => (he.memLp j).integrable one_le_two
  have hgL1 : ∀ j k, Integrable (fun x => weakGrad (e j) x k) ν := fun j k =>
    (memLp_grad_comp hac (he.memH1 j) k).integrable one_le_two
  have htg : ∀ k, Integrable (tensorGrad e c i k) P := fun k => by
    unfold tensorGrad
    refine Integrable.fintype_prod (f := fun j => (Function.update (fun j => e (c j)) i
      (fun x => weakGrad (e (c i)) x k)) j) fun j => ?_
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact hgL1 _ k
    · rw [Function.update_of_ne hj]; exact heL1 _
  have hTc : Integrable (fun X : Config (n + 1) d => ∏ j, e (c j) (X j)) P :=
    Integrable.fintype_prod (f := fun j => e (c j)) fun j => heL1 _
  have hG : Integrable (fun X => ∑ k, cgrad F (flat X) (i, k) * tensorGrad e c i k X) P :=
    integrable_finsetSum _ fun k _ => (htg k).bdd_mul (c := C')
      ((measurable_cgrad hF (i, k)).comp measurable_flat).aestronglyMeasurable
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC' _ _)
  have hH : Integrable (fun X : Config (n + 1) d => F (flat X) * ∏ j, e (c j) (X j)) P :=
    hTc.bdd_mul (c := C) ((measurable_of_contDiff hF).comp measurable_flat).aestronglyMeasurable
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC _)
  rw [integral_pi_insertNth i hG, integral_pi_insertNth i hH, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  -- the inner integral for fixed `r`
  have hslice := memH1_of_contDiff_ac hac (contDiff_sliceF hF (X0 r) i)
  have hgae : weakGrad (sliceF F (X0 r) i) =ᵐ[ν] fun y k => cgrad (sliceF F (X0 r) i) y k :=
    hac.ae_le (weakGrad_ae_eq (isWeakGrad_of_contDiff (contDiff_sliceF hF (X0 r) i)))
  have heig := he.eigen (c i) _ hslice
  calc ∫ y, ∑ k, cgrad F (flat (Fin.insertNth i y r)) (i, k) *
        tensorGrad e c i k (Fin.insertNth i y r) ∂ν
      = ∫ y, R r * ∑ k, weakGrad (e (c i)) y k * weakGrad (sliceF F (X0 r) i) y k ∂ν := by
        refine integral_congr_ae (hgae.mono fun y hy => ?_)
        simp only [hy, hT1, hS, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = R r * (lam (c i) * ∫ y, e (c i) y * sliceF F (X0 r) i y ∂ν) := by
        rw [integral_const_mul, heig]
    _ = lam (c i) * ∫ y, F (flat (Fin.insertNth (α := fun _ => Torus d) i y r)) *
          ∏ j, e (c j) (Fin.insertNth (α := fun _ => Torus d) i y r j) ∂ν := by
        rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hT2, hSv]
        ring

end eigen

end SharpLSI
