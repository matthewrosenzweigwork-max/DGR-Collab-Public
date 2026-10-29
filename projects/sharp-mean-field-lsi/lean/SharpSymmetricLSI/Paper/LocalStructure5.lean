import SharpSymmetricLSI.Paper.LocalStructure4

/-!
# Section 4.2: an `L²(μ)`-orthonormal basis of `ker(I+T)` (Phase 3, lane D; R14)
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real Topology BoundedContinuousFunction Module
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- A copy of `InKerIT` from the R14 statement file. -/
def InKerIT' (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (h : Torus d → ℝ) : Prop :=
  MemL20 μ h ∧ (fun x => h x + Top W μ h x) =ᵐ[μ] 0

/-- A copy of `IsKerBasis` from the R14 statement file. -/
def IsKerBasis' (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) {n : ℕ}
    (φ : Fin n → Torus d → ℝ) : Prop :=
  (∀ i, InKerIT' W μ (φ i)) ∧
  (∀ i j, ∫ x, φ i x * φ j x ∂μ = if i = j then 1 else 0) ∧
  (∀ h, InKerIT' W μ h → ∃ a : Fin n → ℝ, h =ᵐ[μ] fun x => ∑ i, a i * φ i x)

section onb
variable (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
include hyp

theorem integrable_bcf_mul (f g : Torus d →ᵇ ℝ) : Integrable (fun x => f x * g x) μ :=
  integrable_bcf hyp μ (f * g)

/-- The `L²(μ)` pairing on `ker(I+T)`. -/
def kerForm : LinearMap.BilinForm ℝ (kerSpace hyp μ) :=
  LinearMap.mk₂ ℝ (fun u v => ∫ x, (u : Torus d →ᵇ ℝ) x * (v : Torus d →ᵇ ℝ) x ∂μ)
    (fun u₁ u₂ v => by
      simp only [Submodule.coe_add, coe_add, Pi.add_apply, add_mul]
      exact integral_add (integrable_bcf_mul hyp μ _ _) (integrable_bcf_mul hyp μ _ _))
    (fun c u v => by
      simp only [Submodule.coe_smul, coe_smul, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _)
    (fun u v₁ v₂ => by
      simp only [Submodule.coe_add, coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_bcf_mul hyp μ _ _) (integrable_bcf_mul hyp μ _ _))
    (fun c u v => by
      simp only [Submodule.coe_smul, coe_smul, smul_eq_mul, mul_left_comm _ c]
      exact integral_const_mul _ _)

theorem kerForm_apply (u v : kerSpace hyp μ) :
    kerForm hyp μ u v = ∫ x, (u : Torus d →ᵇ ℝ) x * (v : Torus d →ᵇ ℝ) x ∂μ := rfl

end onb

section main
variable (hyp : Hyp V W KV KW)
include hyp

/-- **An `L²(μ)`-orthonormal basis of `ker(I+T)`.** -/
theorem exists_kerBasis {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ∃ n : ℕ, ∃ φ : Fin n → Torus d → ℝ, IsKerBasis' W μ φ := by
  set μm := (μ : Measure (Torus d))
  haveI := kerSpace_finiteDimensional hyp μm
  set B := kerForm hyp μm
  have hsymm : LinearMap.IsSymm (kerForm hyp μm) :=
    LinearMap.isSymm_def.mpr fun u v => by
      rw [RingHom.id_apply, kerForm_apply, kerForm_apply]; congr 1; funext x; ring
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℝ) (V := kerSpace hyp μm)
    (B := kerForm hyp μm) hsymm
  -- positivity of the diagonal
  obtain ⟨hpm, hppos, hp1⟩ := elDensity_props hyp μm
  have hμp : μm = densMeasure (elDens V W μm) := minimizer_eq_elDensity hyp hμ
  have hpos : ∀ u : kerSpace hyp μm, u ≠ 0 → 0 < B u u := by
    intro u hu
    rw [kerForm_apply]
    refine lt_of_le_of_ne (integral_nonneg fun x => mul_self_nonneg _) fun h0 => hu ?_
    have hae : (fun x => (u : Torus d →ᵇ ℝ) x * (u : Torus d →ᵇ ℝ) x) =ᵐ[μm] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _)
        (integrable_bcf_mul hyp μm _ _)).mp h0.symm
    have hac : haar d ≪ μm := by
      rw [hμp]
      exact withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hpm).aemeasurable
        (Eventually.of_forall fun x => by simp [hppos x])
    have hhaar : (fun x => (u : Torus d →ᵇ ℝ) x * (u : Torus d →ᵇ ℝ) x) =ᵐ[haar d] 0 :=
      hac.ae_le hae
    have hc : Continuous fun x => (u : Torus d →ᵇ ℝ) x * (u : Torus d →ᵇ ℝ) x :=
      (u : Torus d →ᵇ ℝ).continuous.mul (u : Torus d →ᵇ ℝ).continuous
    have heq := (Continuous.ae_eq_iff_eq (μ := haar d) hc continuous_const).mp hhaar
    refine Subtype.ext (BoundedContinuousFunction.ext fun x => ?_)
    have h1 : (u : Torus d →ᵇ ℝ) x * (u : Torus d →ᵇ ℝ) x = 0 := congrFun heq x
    exact mul_self_eq_zero.mp h1
  have hBpos : ∀ i, 0 < B (v i) (v i) := fun i => hpos _ (by convert v.ne_zero i)
  set c : Fin (finrank ℝ (kerSpace hyp μm)) → ℝ := fun i => (Real.sqrt (B (v i) (v i)))⁻¹ with hc
  set φ : Fin (finrank ℝ (kerSpace hyp μm)) → Torus d → ℝ := fun i x => c i * ((v i : kerSpace hyp μm) : Torus d →ᵇ ℝ) x
  refine ⟨_, φ, ⟨fun i => ?_, fun i j => ?_, fun h hh => ?_⟩⟩
  · -- kernel elements
    have hmem : c i • (v i : Torus d →ᵇ ℝ) ∈ kerSpace hyp μm :=
      (kerSpace hyp μm).smul_mem (c i) (v i).2
    have h20 := memL20_of_ker hyp μm hmem
    refine ⟨h20, Eventually.of_forall fun x => ?_⟩
    have := hmem.1 x
    simpa [φ] using this
  · -- orthonormality
    have e : ∫ x, φ i x * φ j x ∂μm = c i * c j * B (v i) (v j) := by
      rw [kerForm_apply, ← integral_const_mul]
      congr 1; funext x; simp only [φ]; ring
    rw [e]
    split_ifs with hij
    · subst hij
      have hs := Real.sq_sqrt (hBpos i).le
      simp only [hc]
      field_simp
      rw [hs, div_self (hBpos i).ne']
    · rw [show B (v i) (v j) = 0 from hv hij, mul_zero]
  · -- spanning
    obtain ⟨Cc, hCc⟩ := Top_W1inf hyp μm
    obtain ⟨hTb, hTL⟩ := hCc h hh.1
    set T0 : Torus d →ᵇ ℝ := mkOfCompact ⟨fun x => -Top W μm h x, hTL.continuous.neg⟩
    have hhi := hh.1.1.integrable one_le_two
    have hTi : Integrable (Top W μm h) μm := integrable_of_bdd hTL.continuous.measurable
      (C := Cc * Real.sqrt (∫ y, h y ^ 2 ∂μm)) hTb
    have hTh : (fun x => Top W μm h x) =ᵐ[μm] fun x => -h x := by
      filter_upwards [hh.2] with x hx
      simp only [Pi.zero_apply] at hx; linarith
    have hT0mem : T0 ∈ kerSpace hyp μm := by
      refine ⟨fun x => ?_, ?_⟩
      · have e1 : Top W μm (⇑T0) x = -Top W μm (Top W μm h) x := by
          have := Top_lin hyp μm hTi hTi (-1) 0 x
          simp only [zero_mul, add_zero, neg_one_mul] at this
          rw [← this]; rfl
        have e2 : Top W μm (Top W μm h) x = Top W μm (fun y => -h y) x := Top_congr_ae hyp μm hTh x
        have e3 : Top W μm (fun y => -h y) x = -Top W μm h x := by
          have := Top_lin hyp μm hhi hhi (-1) 0 x
          simp only [zero_mul, add_zero, neg_one_mul] at this
          exact this
        show -Top W μm h x + Top W μm (⇑T0) x = 0
        rw [e1, e2, e3]; ring
      · show ∫ x, -Top W μm h x ∂μm = 0
        rw [integral_neg, integral_Top hyp μm hhi, neg_zero]
    set u : kerSpace hyp μm := ⟨T0, hT0mem⟩
    refine ⟨fun i => v.repr u i * Real.sqrt (B (v i) (v i)), ?_⟩
    have hsum := v.sum_repr u
    filter_upwards [hh.2] with x hx
    simp only [Pi.zero_apply] at hx
    have hux : h x = (u : Torus d →ᵇ ℝ) x := by
      show h x = -Top W μm h x; linarith
    have hx' : (u : Torus d →ᵇ ℝ) x = ∑ i, v.repr u i * (v i : Torus d →ᵇ ℝ) x := by
      conv_lhs => rw [← hsum]
      simp only [Submodule.coe_sum, Submodule.coe_smul, coe_sum, coe_smul, Finset.sum_apply,
        smul_eq_mul]
    rw [hux, hx']
    simp only [φ, hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (Real.sqrt_pos.mpr (hBpos i)).ne'
    field_simp

end main

end SharpLSI
