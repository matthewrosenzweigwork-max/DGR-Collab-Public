import DGPS.Foundations.TotalVariation
import DGPS.Particle.ConditionalEntropy

/-!
# Conditional products and collision bounds (LIP044)

For a bounded measurable `k`-variable test `A`, the mean conditional density `ρ̄_S` of the
unrevealed labels given the revealed ones is realised here as the density-free `meanCond`
(the mean of the conditional kernels).  The main theorem
`DGPS.Lipschitz.conditional_products_and_collision_bounds` compares, summed over `j < N - M`
and averaged over orderings, the integral of `A` against `ρ̄_S^{⊗ k}` with the integral of `A`
against `L_N^{⊗ k}`; the error is `C (1 + √H(ν | Q_N))` with `C` depending only on
`k`, a sup-bound of `A`, and `τ ≤ M / N`.
-/

namespace DGPS.Lipschitz

section PartA
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

section Swap

variable {Y W X : Type*} [MeasurableSpace Y] [MeasurableSpace W] [MeasurableSpace X]

/-- the coordinate swap `((y,w),x) ↦ ((y,x),w)` -/
def swapMid (Y W X : Type*) [MeasurableSpace Y] [MeasurableSpace W] [MeasurableSpace X] :
    (Y × W) × X ≃ᵐ (Y × X) × W where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    show Measurable fun p : (Y × W) × X => ((p.1.1, p.2), p.1.2)
    fun_prop
  measurable_invFun := by
    show Measurable fun p : (Y × X) × W => ((p.1.1, p.2), p.1.2)
    fun_prop

theorem klDiv_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  have := klDiv_map_comp_eq (id : α → α) e e.symm measurable_id e.measurable e.symm.measurable
    (fun ω => e.symm_apply_apply ω) μ ν
  simpa [Function.comp_def, Measure.map_id] using this

theorem swap_compProd (m : Measure Y) [IsProbabilityMeasure m] (ξ : Kernel Y W) [IsMarkovKernel ξ]
    (κ : Kernel Y X) [IsMarkovKernel κ] :
    ((m ⊗ₘ ξ) ⊗ₘ Kernel.prodMkRight W κ).map (swapMid Y W X)
      = (m ⊗ₘ κ) ⊗ₘ Kernel.prodMkRight X ξ := by
  refine Measure.ext_prod₃' ?_
  intro s t u hs ht hu
  rw [Measure.map_apply (swapMid Y W X).measurable ((hs.prod ht).prod hu)]
  have hpre : swapMid Y W X ⁻¹' ((s ×ˢ t) ×ˢ u) = (s ×ˢ u) ×ˢ t := by
    ext p; simp [swapMid]; tauto
  rw [hpre, Measure.compProd_apply_prod (hs.prod hu) ht,
    Measure.compProd_apply_prod (hs.prod ht) hu]
  simp only [Kernel.prodMkRight_apply]
  rw [Measure.setLIntegral_compProd (f := fun a : Y × W => κ a.1 t)
      ((Kernel.measurable_coe _ ht).comp measurable_fst) hs hu,
    Measure.setLIntegral_compProd (f := fun a : Y × X => ξ a.1 u)
      ((Kernel.measurable_coe _ hu).comp measurable_fst) hs ht]
  simp only [setLIntegral_const]
  refine lintegral_congr fun y => ?_
  exact mul_comm _ _

theorem klDiv_step {Y W X : Type*} [MeasurableSpace Y] [MeasurableSpace W] [MeasurableSpace X]
    [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace X] [Nonempty X]
    (N : Measure ((Y × W) × X)) [IsProbabilityMeasure N]
    (R : Measure (Y × W)) [IsProbabilityMeasure R] (RY : Measure Y) [IsProbabilityMeasure RY]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    klDiv N (R.prod μ) + klDiv (N.map (fun p : (Y × W) × X => (p.1.1, p.2))).fst RY
      = klDiv N.fst R
        + klDiv N (N.fst ⊗ₘ Kernel.prodMkRight W (N.map (fun p : (Y × W) × X => (p.1.1, p.2))).condKernel)
        + klDiv (N.map (fun p : (Y × W) × X => (p.1.1, p.2))) (RY.prod μ) := by
  set NYX : Measure (Y × X) := N.map (fun p : (Y × W) × X => (p.1.1, p.2)) with hNYX
  set NY : Measure Y := NYX.fst with hNY
  set κ : Kernel Y X := NYX.condKernel with hκ
  have hmeasg : Measurable (fun p : (Y × W) × X => (p.1.1, p.2)) := by fun_prop
  have hfst : N.fst.fst = NY := by
    simp only [Measure.fst, hNY, hNYX]
    rw [Measure.map_map measurable_fst measurable_fst, Measure.map_map measurable_fst hmeasg]
    rfl
  set ξ : Kernel Y W := N.fst.condKernel with hξ
  have hN1 : N.fst = NY ⊗ₘ ξ := by
    have := Measure.disintegrate N.fst N.fst.condKernel
    rw [hfst] at this
    exact this.symm
  have hN2 : NYX = NY ⊗ₘ κ := (Measure.disintegrate NYX NYX.condKernel).symm
  set N'' : Measure ((Y × X) × W) := N.map (swapMid Y W X) with hN''
  have hfst'' : N''.fst = NYX := by
    simp only [Measure.fst, hN'', hNYX]
    rw [Measure.map_map measurable_fst (swapMid Y W X).measurable]
    rfl
  set ζ : Kernel (Y × X) W := N''.condKernel with hζ
  have hN3 : N'' = NYX ⊗ₘ ζ := by
    have := Measure.disintegrate N'' N''.condKernel
    rw [hfst''] at this
    exact this.symm
  have hconst : Kernel.prodMkRight W (Kernel.const Y μ) = Kernel.const (Y × W) μ := rfl
  -- the key identity
  have key : klDiv N (N.fst.prod μ)
      = klDiv N (N.fst ⊗ₘ Kernel.prodMkRight W κ) + klDiv NYX (NY.prod μ) := by
    have e1 : klDiv N (N.fst.prod μ) = klDiv N'' ((N.fst.prod μ).map (swapMid Y W X)) :=
      (klDiv_map_equiv (swapMid Y W X) N (N.fst.prod μ)).symm
    have e2 : (N.fst.prod μ).map (swapMid Y W X) = (NY.prod μ) ⊗ₘ Kernel.prodMkRight X ξ := by
      rw [← Measure.compProd_const, hN1, ← hconst, swap_compProd, Measure.compProd_const]
    have e3 : klDiv N (N.fst ⊗ₘ Kernel.prodMkRight W κ)
        = klDiv N'' (NYX ⊗ₘ Kernel.prodMkRight X ξ) := by
      rw [← klDiv_map_equiv (swapMid Y W X) N (N.fst ⊗ₘ Kernel.prodMkRight W κ)]
      congr 1
      rw [hN1, swap_compProd, ← hN2]
    rw [e1, e2, e3, hN3, klDiv_compProd_eq_add, add_comm]
  have h1 := klDiv_pyth N R μ
  have h2 := klDiv_pyth NYX RY μ
  rw [h1, h2, key]
  ring

end Swap

end PartA

section PartB
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

section PiKernel

variable {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]

theorem measurable_measure_pi {ι : Type*} [Fintype ι] (κ : ι → Kernel Y X)
    [∀ i, IsMarkovKernel (κ i)] : Measurable (fun y => Measure.pi fun i => κ i y) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := Set.pi Set.univ '' Set.pi Set.univ fun _ : ι => {s : Set X | MeasurableSet s})
    generateFrom_pi.symm isPiSystem_pi ?_
  rintro _ ⟨s, hs, rfl⟩
  simp only [Measure.pi_pi]
  exact Finset.measurable_prod _ fun i _ => Kernel.measurable_coe _ (hs i (Set.mem_univ i))

/-- the product kernel `y ↦ ⊗_{l<m} κ_l(y)` -/
noncomputable def piK (κs : ℕ → Kernel Y X) [∀ l, IsMarkovKernel (κs l)] (m : ℕ) :
    Kernel Y (Fin m → X) where
  toFun y := Measure.pi fun l : Fin m => κs l y
  measurable' := measurable_measure_pi (fun l : Fin m => κs l)

theorem piK_apply (κs : ℕ → Kernel Y X) [∀ l, IsMarkovKernel (κs l)] (m : ℕ) (y : Y) :
    piK κs m y = Measure.pi fun l : Fin m => κs l y := rfl

instance piK_markov (κs : ℕ → Kernel Y X) [∀ l, IsMarkovKernel (κs l)] (m : ℕ) :
    IsMarkovKernel (piK κs m) :=
  ⟨fun y => by rw [piK_apply]; infer_instance⟩

theorem measurable_snoc (m : ℕ) :
    Measurable (fun p : (Fin m → X) × X => (Fin.snoc p.1 p.2 : Fin (m + 1) → X)) := by
  refine measurable_pi_iff.2 fun i => ?_
  induction i using Fin.lastCases with
  | last => simpa using measurable_snd
  | cast i =>
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply i).comp measurable_fst

theorem pi_snoc (m : ℕ) (η : Fin (m + 1) → Measure X) [∀ i, IsProbabilityMeasure (η i)] :
    ((Measure.pi fun l : Fin m => η l.castSucc).prod (η (Fin.last m))).map
      (fun p : (Fin m → X) × X => (Fin.snoc p.1 p.2 : Fin (m + 1) → X)) = Measure.pi η := by
  refine (Measure.pi_eq (μ := η) fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_snoc m) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin m → X) × X => (Fin.snoc p.1 p.2 : Fin (m + 1) → X)) ⁻¹' (Set.univ.pi s)
      = (Set.univ.pi fun l : Fin m => s l.castSucc) ×ˢ s (Fin.last m) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod,
      Fin.forall_fin_succ' (P := fun i => (Fin.snoc p.1 p.2 : Fin (m + 1) → X) i ∈ s i),
      Fin.snoc_castSucc, Fin.snoc_last]
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Fin.prod_univ_castSucc, mul_comm]

theorem measurable_snocPair (Y : Type*) [MeasurableSpace Y] (m : ℕ) :
    Measurable (fun p : (Y × (Fin m → X)) × X => (p.1.1, (Fin.snoc p.1.2 p.2 : Fin (m + 1) → X))) :=
  (measurable_fst.comp measurable_fst).prodMk
    ((measurable_snoc m).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem piK_succ (κs : ℕ → Kernel Y X) [∀ l, IsMarkovKernel (κs l)] (ν0 : Measure Y)
    [IsProbabilityMeasure ν0] (m : ℕ) :
    ν0 ⊗ₘ piK κs (m + 1)
      = ((ν0 ⊗ₘ piK κs m) ⊗ₘ Kernel.prodMkRight (Fin m → X) (κs m)).map
        (fun p : (Y × (Fin m → X)) × X => (p.1.1, (Fin.snoc p.1.2 p.2 : Fin (m + 1) → X))) := by
  ext E hE
  have hF := measurable_snocPair (X := X) Y m
  rw [Measure.map_apply hF hE, Measure.compProd_apply (hF hE), Measure.compProd_apply hE,
    Measure.lintegral_compProd (Kernel.measurable_kernel_prodMk_left (hF hE))]
  refine lintegral_congr fun y => ?_
  rw [piK_apply, ← pi_snoc m (fun l : Fin (m + 1) => κs l y)]
  have hm : MeasurableSet ((fun p : (Fin m → X) × X => (Fin.snoc p.1 p.2 : Fin (m + 1) → X)) ⁻¹'
      (Prod.mk y ⁻¹' E)) := (measurable_snoc m) (measurable_prodMk_left hE)
  rw [Measure.map_apply (measurable_snoc m) (measurable_prodMk_left hE), Measure.prod_apply hm]
  simp only [Fin.val_castSucc, Fin.val_last]
  rfl

end PiKernel

end PartB

section PartC
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

section Readout

variable {X : Type*} [MeasurableSpace X] {N : ℕ}

/-- `φ` reads exactly the coordinates in `C`: a measurable invertible relabelling of `rst C`. -/
def Readout (C : Finset (Fin N)) {V : Type*} [MeasurableSpace V] (φ : (Fin N → X) → V) : Prop :=
  ∃ (F : (C → X) → V) (G : V → (C → X)), Measurable F ∧ Measurable G ∧
    (∀ ω, F (rst (X := X) C ω) = φ ω) ∧ ∀ ω, G (φ ω) = rst (X := X) C ω

theorem readout_rst (C : Finset (Fin N)) : Readout C (rst (X := X) C) :=
  ⟨id, id, measurable_id, measurable_id, fun _ => rfl, fun _ => rfl⟩

theorem readout_eval (i : Fin N) : Readout {i} (fun ω : Fin N → X => ω i) := by
  refine ⟨fun z => z ⟨i, Finset.mem_singleton_self i⟩, fun x _ => x, measurable_pi_apply _,
    measurable_pi_iff.2 fun _ => measurable_id, fun ω => rfl, fun ω => ?_⟩
  funext j
  simp only [rst]
  rw [Finset.mem_singleton.1 j.2]

theorem readout_tuple (S : Finset (Fin N)) (t : ℕ → Fin N) (m : ℕ) :
    Readout (S ∪ (Finset.range m).image t)
      (fun ω : Fin N → X => (rst (X := X) S ω, fun l : Fin m => ω (t l))) := by
  classical
  refine ⟨fun z => (fun i => z ⟨i.1, Finset.mem_union_left _ i.2⟩,
      fun l => z ⟨t l, Finset.mem_union_right _ (Finset.mem_image_of_mem t
        (Finset.mem_range.2 l.2))⟩),
    fun p i => if h : i.1 ∈ S then p.1 ⟨i.1, h⟩ else
      p.2 ⟨Classical.choose (Finset.mem_image.1 ((Finset.mem_union.1 i.2).resolve_left h)),
        Finset.mem_range.1 (Classical.choose_spec
          (Finset.mem_image.1 ((Finset.mem_union.1 i.2).resolve_left h))).1⟩, ?_, ?_, fun ω => rfl,
    fun ω => ?_⟩
  · refine Measurable.prodMk (measurable_pi_iff.2 fun i => measurable_pi_apply _)
      (measurable_pi_iff.2 fun l => measurable_pi_apply _)
  · refine measurable_pi_iff.2 fun i => ?_
    by_cases h : i.1 ∈ S
    · simp only [h, dite_true]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h, dite_false]
      exact (measurable_pi_apply _).comp measurable_snd
  · funext i
    by_cases h : i.1 ∈ S
    · simp [rst, h]
    · simp only [rst, h, dite_false]
      have := (Classical.choose_spec
          (Finset.mem_image.1 ((Finset.mem_union.1 i.2).resolve_left h))).2
      rw [this]

variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem kl_readout {V : Type*} [MeasurableSpace V] {C : Finset (Fin N)} {φ : (Fin N → X) → V}
    (h : Readout C φ) (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] :
    klDiv (ν.map φ) ((refLaw μ N).map φ) = margKL μ ν C := by
  obtain ⟨F, G, hF, hG, h1, h2⟩ := h
  have := klDiv_map_comp_eq (rst (X := X) C) F G (measurable_rst C) hF hG
    (fun ω => by rw [h1, h2]) ν (refLaw μ N)
  have hφ : F ∘ rst (X := X) C = φ := funext h1
  rw [hφ] at this
  exact this

theorem kl_pair_readout {V1 V2 : Type*} [MeasurableSpace V1] [MeasurableSpace V2]
    {C1 C2 : Finset (Fin N)} {φ1 : (Fin N → X) → V1} {φ2 : (Fin N → X) → V2}
    (h1 : Readout C1 φ1) (h2 : Readout C2 φ2) (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] :
    klDiv (ν.map (fun ω => (φ1 ω, φ2 ω))) ((refLaw μ N).map (fun ω => (φ1 ω, φ2 ω)))
      = margKL μ ν (C1 ∪ C2) := by
  obtain ⟨F1, G1, hF1, hG1, e1, d1⟩ := h1
  obtain ⟨F2, G2, hF2, hG2, e2, d2⟩ := h2
  have := klDiv_map_comp_eq (fun ω : Fin N → X => (rst (X := X) C1 ω, rst (X := X) C2 ω))
    (Prod.map F1 F2) (Prod.map G1 G2) ((measurable_rst C1).prodMk (measurable_rst C2))
    (hF1.prodMap hF2) (hG1.prodMap hG2)
    (fun ω => by simp only [Prod.map, e1, e2, d1, d2]) ν (refLaw μ N)
  have hφ : Prod.map F1 F2 ∘ (fun ω : Fin N → X => (rst (X := X) C1 ω, rst (X := X) C2 ω))
      = fun ω => (φ1 ω, φ2 ω) := funext fun ω => by simp only [Function.comp, Prod.map, e1, e2]
  rw [hφ] at this
  rw [this]
  exact margKL_pair_eq ν C1 C2

theorem refLaw_map_eval (i : Fin N) : (refLaw μ N).map (fun ω : Fin N → X => ω i) = μ := by
  classical
  have := Measure.pi_map_eval (μ := fun _ : Fin N => μ) i
  simpa [refLaw] using this

theorem indep_ref {V1 V2 : Type*} [MeasurableSpace V1] [MeasurableSpace V2]
    {C1 C2 : Finset (Fin N)} {φ1 : (Fin N → X) → V1} {φ2 : (Fin N → X) → V2}
    (h1 : Readout C1 φ1) (h2 : Readout C2 φ2) (hd : Disjoint C1 C2) :
    (refLaw μ N).map (fun ω => (φ1 ω, φ2 ω))
      = ((refLaw μ N).map φ1).prod ((refLaw μ N).map φ2) := by
  obtain ⟨F1, G1, hF1, hG1, e1, d1⟩ := h1
  obtain ⟨F2, G2, hF2, hG2, e2, d2⟩ := h2
  have hφ : (fun ω => (φ1 ω, φ2 ω)) = Prod.map F1 F2 ∘
      (fun ω : Fin N → X => (rst (X := X) C1 ω, rst (X := X) C2 ω)) :=
    funext fun ω => by simp only [Function.comp, Prod.map, e1, e2]
  have hφ1 : φ1 = F1 ∘ rst (X := X) C1 := funext fun ω => (e1 ω).symm
  have hφ2 : φ2 = F2 ∘ rst (X := X) C2 := funext fun ω => (e2 ω).symm
  rw [hφ, ← Measure.map_map (hF1.prodMap hF2) ((measurable_rst C1).prodMk (measurable_rst C2)),
    pi_map_rst_prod μ C1 C2 hd, ← Measure.map_prod_map _ _ hF1 hF2, hφ1, hφ2,
    ← Measure.map_map hF1 (measurable_rst C1), ← Measure.map_map hF2 (measurable_rst C2)]

end Readout

end PartC

section PartD
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

section Pinsker

variable {α : Type*} [MeasurableSpace α]

theorem pinsker_integral (ν P : Measure α) [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    (h : klDiv ν P ≠ ⊤) (f : α → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂ν - ∫ x, f x ∂P| ≤ B * Real.sqrt (2 * (klDiv ν P).toReal) := by
  have hrel : DGPS.relativeEntropy ν P = klDiv ν P := DGPS.Analysis.relativeEntropy_eq_klDiv
  have hP := DGPS.pinsker_fullVariation_real ν P (hrel ▸ h)
  rw [hrel] at hP
  have hFV : DGPS.fullVariation ν P ≤ Real.sqrt (2 * (klDiv ν P).toReal) :=
    Real.le_sqrt_of_sq_le hP
  have : Nonempty α := nonempty_of_isProbabilityMeasure ν
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (Classical.arbitrary _))
  set μ : Measure α := ν + P with hμ
  have hνμ : ν ≪ μ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hPμ : P ≪ μ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hfi : ∀ ρ : Measure α, IsFiniteMeasure ρ → Integrable f ρ := fun ρ hρ =>
    Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
      simpa using hB x)
  have hfν : Integrable f ν := hfi ν inferInstance
  have hfP : Integrable f P := hfi P inferInstance
  have hi1 : Integrable (fun x => (ν.rnDeriv μ x).toReal * f x) μ :=
    (integrable_toReal_rnDeriv_mul_iff hνμ).2 hfν
  have hi2 : Integrable (fun x => (P.rnDeriv μ x).toReal * f x) μ :=
    (integrable_toReal_rnDeriv_mul_iff hPμ).2 hfP
  have e1 : ∫ x, f x ∂ν = ∫ x, (ν.rnDeriv μ x).toReal * f x ∂μ :=
    (integral_toReal_rnDeriv_mul hνμ).symm
  have e2 : ∫ x, f x ∂P = ∫ x, (P.rnDeriv μ x).toReal * f x ∂μ :=
    (integral_toReal_rnDeriv_mul hPμ).symm
  have hd : ∫ x, f x ∂ν - ∫ x, f x ∂P
      = ∫ x, ((ν.rnDeriv μ x).toReal - (P.rnDeriv μ x).toReal) * f x ∂μ := by
    rw [e1, e2, ← integral_sub hi1 hi2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [sub_mul])
  have hia : Integrable (fun x => |(ν.rnDeriv μ x).toReal - (P.rnDeriv μ x).toReal|) μ :=
    ((Measure.integrable_toReal_rnDeriv).sub (Measure.integrable_toReal_rnDeriv)).abs
  have hFVeq := DGPS.fullVariation_eq_integral_abs_add ν P
  have hle : |∫ x, ((ν.rnDeriv μ x).toReal - (P.rnDeriv μ x).toReal) * f x ∂μ|
      ≤ B * DGPS.fullVariation ν P := by
    rw [hFVeq]
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (hia.const_mul B) (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [abs_mul]
    nlinarith [abs_nonneg ((ν.rnDeriv μ x).toReal - (P.rnDeriv μ x).toReal), hB x]
  rw [hd]
  exact hle.trans (mul_le_mul_of_nonneg_left hFV hB0)

end Pinsker

end PartD

section PartE
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

section Chain

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] {N : ℕ}

omit [StandardBorelSpace X] [Nonempty X] in
theorem measurable_rst_eval (S : Finset (Fin N)) (i : Fin N) :
    Measurable (fun ω : Fin N → X => (rst (X := X) S ω, ω i)) :=
  (measurable_rst S).prodMk (measurable_pi_apply i)

/-- conditional law of the label `i` given the labels in `S` -/
noncomputable def condLaw (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] (S : Finset (Fin N))
    (i : Fin N) : Kernel (S → X) X :=
  (ν.map (fun ω : Fin N → X => (rst (X := X) S ω, ω i))).condKernel

instance condLaw_markov (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] (S : Finset (Fin N))
    (i : Fin N) : IsMarkovKernel (condLaw ν S i) := by
  unfold condLaw
  infer_instance

/-- the tuple map `ω ↦ (ω|_S, (ω (t l))_{l<m})` -/
def Tm (S : Finset (Fin N)) (t : ℕ → Fin N) (m : ℕ) :
    (Fin N → X) → (S → X) × (Fin m → X) := fun ω => (rst (X := X) S ω, fun l => ω (t l))

omit [StandardBorelSpace X] [Nonempty X] in
theorem measurable_Tm (S : Finset (Fin N)) (t : ℕ → Fin N) (m : ℕ) :
    Measurable (Tm (X := X) S t m) :=
  (measurable_rst S).prodMk (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

/-- the product comparison law `ν_S ⊗ ⊗_l κ_l` -/
noncomputable def Pm (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] (S : Finset (Fin N))
    (t : ℕ → Fin N) (m : ℕ) : Measure ((S → X) × (Fin m → X)) :=
  (ν.map (rst (X := X) S)) ⊗ₘ piK (fun l => condLaw ν S (t l)) m

instance Pm_prob (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] (S : Finset (Fin N))
    (t : ℕ → Fin N) (m : ℕ) : IsProbabilityMeasure (Pm ν S t m) := by
  unfold Pm; infer_instance

theorem klDiv_map_left_inv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (F : α → β)
    (G : β → α) (hF : Measurable F) (hG : Measurable G) (hFG : ∀ a, G (F a) = a)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map F) (ν.map F) = klDiv μ ν := by
  have := klDiv_map_comp_eq (id : α → α) F G measurable_id hF hG (fun a => hFG a) μ ν
  simpa [Function.comp_def, Measure.map_id] using this

theorem klDiv_step' {Y W X : Type*} [MeasurableSpace Y] [MeasurableSpace W] [MeasurableSpace X]
    [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace X] [Nonempty X]
    (N : Measure ((Y × W) × X)) [IsProbabilityMeasure N]
    (R : Measure (Y × W)) [IsProbabilityMeasure R] (RY : Measure Y) [IsProbabilityMeasure RY]
    (μ : Measure X) [IsProbabilityMeasure μ] (NYX : Measure (Y × X)) [IsProbabilityMeasure NYX]
    (hNYX : N.map (fun p : (Y × W) × X => (p.1.1, p.2)) = NYX) :
    klDiv N (R.prod μ) + klDiv NYX.fst RY
      = klDiv N.fst R + klDiv N (N.fst ⊗ₘ Kernel.prodMkRight W NYX.condKernel)
        + klDiv NYX (RY.prod μ) := by
  subst hNYX
  exact klDiv_step N R RY μ


section Step

variable (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν]

/-- tuple map with one more coordinate split off -/
def Tp (S : Finset (Fin N)) (t : ℕ → Fin N) (m : ℕ) :
    (Fin N → X) → ((S → X) × (Fin m → X)) × X := fun ω => (Tm S t m ω, ω (t m))

omit [StandardBorelSpace X] [Nonempty X] in
theorem measurable_Tp (S : Finset (Fin N)) (t : ℕ → Fin N) (m : ℕ) :
    Measurable (Tp (X := X) S t m) :=
  (measurable_Tm S t m).prodMk (measurable_pi_apply _)

omit [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] in
theorem Tm_succ (S : Finset (Fin N)) (t : ℕ → Fin N) (m : ℕ) :
    (Tm (X := X) S t (m + 1))
      = (fun p : ((S → X) × (Fin m → X)) × X => (p.1.1, (Fin.snoc p.1.2 p.2 : Fin (m + 1) → X)))
        ∘ Tp S t m := by
  funext ω
  simp only [Tm, Tp, Function.comp]
  refine Prod.ext rfl ?_
  funext l
  induction l using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem klDiv_succ_eq (S : Finset (Fin N)) (t : ℕ → Fin N) (m : ℕ) :
    klDiv (ν.map (Tm S t (m + 1))) (Pm ν S t (m + 1))
      = klDiv (ν.map (Tm S t m)) (Pm ν S t m)
        + klDiv (ν.map (Tp S t m))
          ((ν.map (Tp S t m)).fst ⊗ₘ Kernel.prodMkRight (Fin m → X) (condLaw ν S (t m))) := by
  set N' : Measure (((S → X) × (Fin m → X)) × X) := ν.map (Tp S t m) with hN'
  set F : ((S → X) × (Fin m → X)) × X → (S → X) × (Fin (m + 1) → X) :=
    fun p => (p.1.1, (Fin.snoc p.1.2 p.2 : Fin (m + 1) → X)) with hFdef
  have hF : Measurable F := measurable_snocPair (S → X) m
  have hG : Measurable (fun q : (S → X) × (Fin (m + 1) → X) =>
      ((q.1, Fin.init q.2), q.2 (Fin.last m))) :=
    (measurable_fst.prodMk (measurable_pi_iff.2 fun i =>
      (measurable_pi_apply _).comp measurable_snd)).prodMk
      ((measurable_pi_apply _).comp measurable_snd)
  have hFG : ∀ a, (fun q : (S → X) × (Fin (m + 1) → X) =>
      ((q.1, Fin.init q.2), q.2 (Fin.last m))) (F a) = a := by
    intro a
    simp [hFdef, Fin.init_snoc]
  have h1 : ν.map (Tm S t (m + 1)) = N'.map F := by
    rw [hN', Measure.map_map hF (measurable_Tp S t m), ← Tm_succ]
  have h2 : Pm ν S t (m + 1)
      = (Pm ν S t m ⊗ₘ Kernel.prodMkRight (Fin m → X) (condLaw ν S (t m))).map F :=
    piK_succ (fun l => condLaw ν S (t l)) (ν.map (rst (X := X) S)) m
  rw [h1, h2, klDiv_map_left_inv F _ hF hG hFG]
  have hfst : N'.fst = ν.map (Tm S t m) := by
    simp only [Measure.fst, hN']
    rw [Measure.map_map measurable_fst (measurable_Tp S t m)]
    rfl
  have := klDiv_compProd_eq_add N'.fst (Pm ν S t m) N'.condKernel
    (Kernel.prodMkRight (Fin m → X) (condLaw ν S (t m)))
  rw [Measure.disintegrate N' N'.condKernel, hfst] at this
  rw [this]
  rw [hfst]


/-- the index set of the first `m` tuple labels together with `S` -/
def Bset (S : Finset (Fin N)) (t : ℕ → Fin N) (m : ℕ) : Finset (Fin N) :=
  S ∪ (Finset.range m).image t

theorem Bset_succ (S : Finset (Fin N)) (t : ℕ → Fin N) (m : ℕ) :
    Bset S t (m + 1) = Bset S t m ∪ {t m} := by
  ext x
  simp only [Bset, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h | h
      · exact Or.inl (Or.inr ⟨a, h, rfl⟩)
      · exact Or.inr (by rw [h])
  · rintro ((h | ⟨a, ha, rfl⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨a, by omega, rfl⟩
    · exact Or.inr ⟨m, by omega, h.symm⟩

variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem chain_identity (S : Finset (Fin N)) (t : ℕ → Fin N) (m : ℕ) (h1 : t m ∉ S)
    (h2 : t m ∉ (Finset.range m).image t) :
    margKL μ ν (Bset S t (m + 1)) + margKL μ ν S
      = margKL μ ν (Bset S t m)
        + klDiv (ν.map (Tp S t m))
          ((ν.map (Tp S t m)).fst ⊗ₘ Kernel.prodMkRight (Fin m → X) (condLaw ν S (t m)))
        + margKL μ ν (insert (t m) S) := by
  have hd1 : Disjoint (Bset S t m) {t m} := by
    rw [Finset.disjoint_singleton_right]
    simp only [Bset, Finset.mem_union, not_or]
    exact ⟨h1, h2⟩
  have hd2 : Disjoint S {t m} := by
    rw [Finset.disjoint_singleton_right]; exact h1
  have hstep := klDiv_step' (ν.map (Tp S t m)) ((refLaw μ N).map (Tm S t m))
    ((refLaw μ N).map (rst (X := X) S)) μ (ν.map (fun ω : Fin N → X => (rst (X := X) S ω, ω (t m))))
    (by rw [Measure.map_map (by fun_prop) (measurable_Tp S t m)]; rfl)
  have rd1 : ((refLaw μ N).map (Tm S t m)).prod μ = (refLaw μ N).map (Tp S t m) := by
    have := indep_ref μ (readout_tuple (X := X) S t m) (readout_eval (X := X) (t m)) hd1
    rw [refLaw_map_eval] at this
    exact this.symm
  have rd2 : ((refLaw μ N).map (rst (X := X) S)).prod μ
      = (refLaw μ N).map (fun ω : Fin N → X => (rst (X := X) S ω, ω (t m))) := by
    have := indep_ref μ (readout_rst (X := X) S) (readout_eval (X := X) (t m)) hd2
    rw [refLaw_map_eval] at this
    exact this.symm
  have ka : klDiv (ν.map (Tp S t m)) ((refLaw μ N).map (Tp S t m))
      = margKL μ ν (Bset S t (m + 1)) := by
    rw [Bset_succ]
    exact kl_pair_readout μ (readout_tuple (X := X) S t m) (readout_eval (X := X) (t m)) ν
  have kb : klDiv ((ν.map (fun ω : Fin N → X => (rst (X := X) S ω, ω (t m)))).fst)
      ((refLaw μ N).map (rst (X := X) S)) = margKL μ ν S := by
    have : (ν.map (fun ω : Fin N → X => (rst (X := X) S ω, ω (t m)))).fst = ν.map (rst S) := by
      simp only [Measure.fst]
      rw [Measure.map_map measurable_fst (measurable_rst_eval S (t m))]
      rfl
    rw [this]; rfl
  have kc : klDiv (ν.map (Tp S t m)).fst ((refLaw μ N).map (Tm S t m)) = margKL μ ν (Bset S t m) := by
    have : (ν.map (Tp S t m)).fst = ν.map (Tm S t m) := by
      simp only [Measure.fst]
      rw [Measure.map_map measurable_fst (measurable_Tp S t m)]
      rfl
    rw [this]
    exact kl_readout μ (readout_tuple (X := X) S t m) ν
  have ke : klDiv (ν.map (fun ω : Fin N → X => (rst (X := X) S ω, ω (t m))))
      (((refLaw μ N).map (rst (X := X) S)).prod μ) = margKL μ ν (insert (t m) S) := by
    rw [rd2, Finset.insert_eq, Finset.union_comm]
    exact kl_pair_readout μ (readout_rst (X := X) S) (readout_eval (X := X) (t m)) ν
  rw [rd1, ka, kb, kc, ke] at hstep
  exact hstep


theorem eq_of_fst_eq_of_unique {α V : Type*} [MeasurableSpace α] [MeasurableSpace V] [Unique V]
    (a b : Measure (α × V)) (h : a.fst = b.fst) : a = b := by
  have key : ∀ c : Measure (α × V), c = c.fst.map (fun x => (x, (default : V))) := by
    intro c
    simp only [Measure.fst]
    have hg : Measurable (fun x : α => (x, (default : V))) := by fun_prop
    rw [Measure.map_map hg measurable_fst]
    have : ((fun x => (x, (default : V))) ∘ Prod.fst : α × V → α × V) = id := by
      funext p; simp only [Function.comp, id]; exact Prod.ext rfl (Subsingleton.elim _ _)
    rw [this, Measure.map_id]
  rw [key a, key b, h]

theorem klDiv_tuple_zero (S : Finset (Fin N)) (t : ℕ → Fin N) :
    ν.map (Tm S t 0) = Pm ν S t 0 := by
  refine eq_of_fst_eq_of_unique _ _ ?_
  unfold Pm
  rw [Measure.fst_compProd]
  simp only [Measure.fst]
  rw [Measure.map_map measurable_fst (measurable_Tm S t 0)]
  rfl

theorem klDiv_tuple (hfin : klDiv ν (refLaw μ N) ≠ ⊤) (S : Finset (Fin N)) (t : ℕ → Fin N)
    (k : ℕ) (hS : ∀ l, l < k → t l ∉ S) (hinj : ∀ a b, a < k → b < k → t a = t b → a = b) :
    ∀ m, m ≤ k → klDiv (ν.map (Tm S t m)) (Pm ν S t m) ≠ ⊤ ∧
      (klDiv (ν.map (Tm S t m)) (Pm ν S t m)).toReal
        = (margEnt μ ν (Bset S t m) - margEnt μ ν S)
          - ∑ a ∈ Finset.range m, (margEnt μ ν (insert (t a) S) - margEnt μ ν S) := by
  have hne : ∀ C, margKL μ ν C ≠ ⊤ := fun C => ne_top_of_le_ne_top hfin (margKL_le_top_of ν C)
  intro m
  induction m with
  | zero =>
    intro _
    rw [klDiv_tuple_zero, klDiv_self]
    refine ⟨by simp, ?_⟩
    simp [Bset]
  | succ m ih =>
    intro hm
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have h1 : t m ∉ S := hS m (by omega)
    have h2 : t m ∉ (Finset.range m).image t := by
      simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
      intro a ha hta
      have := hinj a m (by omega) (by omega) hta
      omega
    have hid := chain_identity ν μ S t m h1 h2
    have hsucc := klDiv_succ_eq ν S t m
    set d := klDiv (ν.map (Tp S t m))
      ((ν.map (Tp S t m)).fst ⊗ₘ Kernel.prodMkRight (Fin m → X) (condLaw ν S (t m))) with hd
    have hdne : d ≠ ⊤ := by
      intro hd'
      have : margKL μ ν (Bset S t (m + 1)) + margKL μ ν S ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨hne _, hne _⟩
      apply this
      rw [hid, hd']; simp
    have hreal := congrArg ENNReal.toReal hid
    rw [ENNReal.toReal_add (hne _) (hne _), ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hne _, hdne⟩)
      (hne _), ENNReal.toReal_add (hne _) hdne] at hreal
    refine ⟨?_, ?_⟩
    · rw [hsucc]; exact ENNReal.add_ne_top.2 ⟨ih1, hdne⟩
    · rw [hsucc, ENNReal.toReal_add ih1 hdne, ih2, Finset.sum_range_succ]
      unfold margEnt
      linarith
  
end Step

end Chain

end PartE

section PartF
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

section Core

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] {N : ℕ}

/-- the entropy-defect expression for the labels `t 0, …, t (k-1)` given `S` -/
noncomputable def tcR (μ : Measure X) (ν : Measure (Fin N → X)) (S : Finset (Fin N))
    (t : ℕ → Fin N) (k : ℕ) : ℝ :=
  (margEnt μ ν (Bset S t k) - margEnt μ ν S)
    - ∑ a ∈ Finset.range k, (margEnt μ ν (insert (t a) S) - margEnt μ ν S)

theorem core_bound (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Fin N → X))
    [IsProbabilityMeasure ν] (hfin : klDiv ν (refLaw μ N) ≠ ⊤) (S : Finset (Fin N))
    (t : ℕ → Fin N) (k : ℕ) (hS : ∀ l, l < k → t l ∉ S)
    (hinj : ∀ a b, a < k → b < k → t a = t b → a = b)
    (A : (Fin k → X) → ℝ) (hA : Measurable A) (B : ℝ) (hB : ∀ x, |A x| ≤ B) :
    |∫ y, ∫ x, A x ∂(Measure.pi fun l : Fin k => condLaw ν S (t l) y) ∂(ν.map (rst (X := X) S))
        - ∫ ω, A (fun l : Fin k => ω (t l)) ∂ν|
      ≤ B * Real.sqrt (2 * tcR μ ν S t k) := by
  obtain ⟨hne, hreal⟩ := klDiv_tuple ν μ hfin S t k hS hinj k le_rfl
  have hf : Measurable (fun p : (S → X) × (Fin k → X) => A p.2) := hA.comp measurable_snd
  have hp := pinsker_integral (ν.map (Tm S t k)) (Pm ν S t k) hne (fun p => A p.2) hf B
    (fun p => hB _)
  rw [hreal] at hp
  have e1 : ∫ p, A p.2 ∂(ν.map (Tm S t k)) = ∫ ω, A (fun l : Fin k => ω (t l)) ∂ν := by
    rw [integral_map (measurable_Tm S t k).aemeasurable hf.aestronglyMeasurable]
    rfl
  have e2 : ∫ p, A p.2 ∂(Pm ν S t k)
      = ∫ y, ∫ x, A x ∂(Measure.pi fun l : Fin k => condLaw ν S (t l) y)
          ∂(ν.map (rst (X := X) S)) := by
    unfold Pm
    have hint : Integrable (fun p : (S → X) × (Fin k → X) => A p.2)
        ((ν.map (rst (X := X) S)) ⊗ₘ piK (fun l => condLaw ν S (t l)) k) :=
      Integrable.of_bound hf.aestronglyMeasurable B
        (Filter.Eventually.of_forall fun x => by simpa using hB _)
    rw [Measure.integral_compProd hint]
    rfl
  rw [e1, e2] at hp
  rw [abs_sub_comm]
  exact hp
  
end Core

end PartF

section PartG
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

section Expand

variable {X : Type*} [MeasurableSpace X]

theorem pi_sum_smul {n k : ℕ} (w : ℝ≥0) (κ : Fin n → Measure X) [∀ p, IsFiniteMeasure (κ p)] :
    Measure.pi (fun _ : Fin k => ∑ p, (w : ℝ≥0∞) • κ p)
      = ∑ b : Fin k → Fin n, ((w : ℝ≥0∞) ^ k) • Measure.pi (fun l => κ (b l)) := by
  have : ∀ p, IsFiniteMeasure ((w : ℝ≥0∞) • κ p) := fun p =>
    Measure.smul_finite (κ p) ENNReal.coe_ne_top
  have : IsFiniteMeasure (∑ p, (w : ℝ≥0∞) • κ p) :=
    ⟨by
      rw [Measure.finsetSum_apply]
      exact ENNReal.sum_lt_top.2 fun p _ => measure_lt_top _ _⟩
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  rw [Finset.prod_congr rfl (fun l _ => Measure.finsetSum_apply _ _ _)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem pi_dirac' {k : ℕ} [MeasurableSingletonClass X] (x : Fin k → X) :
    Measure.pi (fun l => Measure.dirac (x l)) = Measure.dirac x := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp only [Measure.dirac_apply' _ (hs _)]
  by_cases h : x ∈ Set.univ.pi s
  · simp only [Set.indicator_of_mem h, Pi.one_apply]
    refine (Finset.prod_eq_one fun l _ => ?_).symm
    exact Set.indicator_of_mem (by simpa using h l) _
  · rw [Set.indicator_of_notMem h]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at h
    obtain ⟨l, hl⟩ := h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp [Set.indicator_of_notMem hl])

theorem integral_pi_sum_smul {n k : ℕ} (w : ℝ≥0) (κ : Fin n → Measure X)
    [∀ p, IsProbabilityMeasure (κ p)] (A : (Fin k → X) → ℝ) (hA : Measurable A) (B : ℝ)
    (hB : ∀ x, |A x| ≤ B) :
    ∫ x, A x ∂(Measure.pi (fun _ : Fin k => ∑ p, (w : ℝ≥0∞) • κ p))
      = ∑ b : Fin k → Fin n, (w : ℝ) ^ k * ∫ x, A x ∂(Measure.pi (fun l => κ (b l))) := by
  rw [pi_sum_smul]
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_smul_measure]
    simp [ENNReal.toReal_pow]
  · intro b _
    have : IsFiniteMeasure (((w : ℝ≥0∞) ^ k) • Measure.pi (fun l => κ (b l))) :=
      Measure.smul_finite _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    exact Integrable.of_bound hA.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by simpa using hB x)

end Expand

end PartG

section PartH
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

section MeanY

variable {X : Type*} [MeasurableSpace X] {Y : Type*} [MeasurableSpace Y]

/-- the product of kernels as a kernel (finite index) -/
noncomputable def piKF {m : ℕ} (κs : Fin m → Kernel Y X) [∀ l, IsMarkovKernel (κs l)] :
    Kernel Y (Fin m → X) where
  toFun y := Measure.pi fun l : Fin m => κs l y
  measurable' := measurable_measure_pi κs

theorem piKF_apply {m : ℕ} (κs : Fin m → Kernel Y X) [∀ l, IsMarkovKernel (κs l)] (y : Y) :
    piKF κs y = Measure.pi fun l : Fin m => κs l y := rfl

instance piKF_markov {m : ℕ} (κs : Fin m → Kernel Y X) [∀ l, IsMarkovKernel (κs l)] :
    IsMarkovKernel (piKF κs) :=
  ⟨fun y => by rw [piKF_apply]; infer_instance⟩

theorem measurable_integral_pi {m : ℕ} (κs : Fin m → Kernel Y X) [∀ l, IsMarkovKernel (κs l)]
    (A : (Fin m → X) → ℝ) (hA : Measurable A) :
    Measurable (fun y => ∫ x, A x ∂(Measure.pi fun l : Fin m => κs l y)) :=
  (hA.stronglyMeasurable.integral_kernel (κ := piKF κs)).measurable

theorem abs_integral_le_of_prob {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (A : α → ℝ) (B : ℝ) (hB : ∀ x, |A x| ≤ B) :
    |∫ x, A x ∂P| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := A) (C := B)
    (Filter.Eventually.of_forall fun x => by simpa using hB x)
  simpa using this

theorem integral_mean_expand {n k : ℕ} (w : ℝ≥0) (κs : Fin n → Kernel Y X)
    [∀ p, IsMarkovKernel (κs p)] (m : Measure Y) [IsFiniteMeasure m]
    (A : (Fin k → X) → ℝ) (hA : Measurable A) (B : ℝ) (hB : ∀ x, |A x| ≤ B)
    (M : Y → Measure X) (hM : ∀ y, M y = ∑ p, (w : ℝ≥0∞) • κs p y) :
    ∫ y, ∫ x, A x ∂(Measure.pi fun _ : Fin k => M y) ∂m
      = ∑ b : Fin k → Fin n, (w : ℝ) ^ k *
          ∫ y, ∫ x, A x ∂(Measure.pi fun l : Fin k => κs (b l) y) ∂m := by
  have h1 : ∀ y, ∫ x, A x ∂(Measure.pi fun _ : Fin k => M y)
      = ∑ b : Fin k → Fin n, (w : ℝ) ^ k * ∫ x, A x ∂(Measure.pi fun l : Fin k => κs (b l) y) := by
    intro y
    simp only [hM]
    exact integral_pi_sum_smul w (fun p => κs p y) A hA B hB
  simp only [h1]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]
  · intro b _
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound (C := B) ?_ ?_
    · exact (measurable_integral_pi (fun l : Fin k => κs (b l)) A hA).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => by
        simpa using abs_integral_le_of_prob _ A B hB

end MeanY

end PartH

section PartI
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

section Defs

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] {N : ℕ}

/-- The mean conditional law of the unrevealed labels given the revealed ones `S`
(the mean of the conditional laws of the labels outside `S`; its density with respect to the
reference law is the mean conditional density). -/
noncomputable def meanCond (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν]
    (S : Finset (Fin N)) (y : S → X) : Measure X :=
  ∑ i ∈ Sᶜ, (((Sᶜ.card : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • condLaw ν S i y

/-- The empirical measure `L_N(ω) = N⁻¹ ∑_i δ_{ω i}`. -/
noncomputable def empirical (ω : Fin N → X) : Measure X :=
  ∑ i : Fin N, (((N : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • Measure.dirac (ω i)

/-- the label at position `j + p` of the ordering `σ` -/
def posLbl (σ : Equiv.Perm (Fin N)) (j : ℕ) (p : Fin (N - j)) : Fin N :=
  σ ⟨j + p, by omega⟩

theorem sum_compl_revealed {M : Type*} [AddCommMonoid M] (σ : Equiv.Perm (Fin N)) (j : ℕ)
    (h : Fin N → M) :
    ∑ i ∈ (revealed σ j)ᶜ, h i = ∑ p : Fin (N - j), h (posLbl σ j p) := by
  symm
  refine Finset.sum_bij (fun p _ => posLbl σ j p) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p _
    simp [revealed, posLbl]
  · intro p _ q _ hpq
    have := σ.injective hpq
    simp only [Fin.mk.injEq] at this
    exact Fin.ext (by omega)
  · intro i hi
    simp only [revealed, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at hi
    refine ⟨⟨(σ.symm i : ℕ) - j, by have := (σ.symm i).2; omega⟩, Finset.mem_univ _, ?_⟩
    simp only [posLbl]
    have : (⟨j + ((σ.symm i : ℕ) - j), by have := (σ.symm i).2; omega⟩ : Fin N) = σ.symm i :=
      Fin.ext (by simp; omega)
    rw [this]; simp

theorem card_compl_revealed (σ : Equiv.Perm (Fin N)) (j : ℕ) :
    ((revealed σ j)ᶜ).card = N - j := by
  have := sum_compl_revealed σ j (fun _ => (1 : ℕ))
  simpa using this

theorem meanCond_eq (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] (σ : Equiv.Perm (Fin N))
    (j : ℕ) (y : revealed σ j → X) :
    meanCond ν (revealed σ j) y
      = ∑ p : Fin (N - j), ((((N - j : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) •
          condLaw ν (revealed σ j) (posLbl σ j p) y := by
  unfold meanCond
  rw [card_compl_revealed]
  exact sum_compl_revealed σ j (fun i => (((((N - j : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) •
    condLaw ν (revealed σ j) i y))

omit [Nonempty X] in
theorem integral_empirical_expand (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] (k : ℕ)
    (A : (Fin k → X) → ℝ) (hA : Measurable A) (B : ℝ) (hB : ∀ x, |A x| ≤ B) :
    ∫ ω, ∫ x, A x ∂(Measure.pi fun _ : Fin k => empirical ω) ∂ν
      = ∑ g : Fin k → Fin N, (((N : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) ^ k *
          ∫ ω, A (fun l => ω (g l)) ∂ν := by
  have h1 : ∀ ω : Fin N → X, ∫ x, A x ∂(Measure.pi fun _ : Fin k => empirical ω)
      = ∑ g : Fin k → Fin N, (((N : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) ^ k * A (fun l => ω (g l)) := by
    intro ω
    unfold empirical
    rw [integral_pi_sum_smul (((N : ℝ≥0)⁻¹ : ℝ≥0)) (fun i => Measure.dirac (ω i)) A hA B hB]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [pi_dirac', integral_dirac]
  simp only [h1]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [integral_const_mul]
  · intro g _
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound (C := B) ?_ ?_
    · exact (hA.comp (measurable_pi_iff.2 fun l => measurable_pi_apply (g l))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by simpa using hB _

end Defs

end PartI

section PartJ
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open Equiv

section PermFacts

open Equiv

theorem sum_perm_comp_inj {N : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (ι : β → Fin N)
    (hι : Function.Injective ι) (F : (β → Fin N) → ℝ) :
    (∑ σ : Perm (Fin N), F (fun x => σ (ι x))) *
        ((Finset.univ.filter (fun g : β → Fin N => Function.Injective g)).card : ℝ)
      = (N.factorial : ℝ) *
        ∑ g ∈ Finset.univ.filter (fun g : β → Fin N => Function.Injective g), F g := by
  classical
  set I := Finset.univ.filter (fun g : β → Fin N => Function.Injective g) with hI
  have hmaps : ∀ σ ∈ (Finset.univ : Finset (Perm (Fin N))), (fun σ : Perm (Fin N) => fun x => σ (ι x)) σ ∈ I := by
    intro σ _
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]
    exact σ.injective.comp hι
  have hc : ∀ g ∈ I, (Finset.univ.filter (fun σ : Perm (Fin N) => (fun x => σ (ι x)) = g)).card
      = (Finset.univ.filter (fun σ : Perm (Fin N) => (fun x => σ (ι x)) = ι)).card := by
    intro g hg
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨κ, hκ⟩ := Equiv.Perm.exists_extending_pair ι g hι hg
    refine Finset.card_nbij' (fun σ => κ⁻¹ * σ) (fun σ => κ * σ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
      funext x
      have := congrFun hσ x
      simp only [Perm.coe_mul, Function.comp_apply] at this ⊢
      rw [this, ← hκ x]; simp
    · intro σ hσ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
      funext x
      have := congrFun hσ x
      simp only [Perm.coe_mul, Function.comp_apply] at this ⊢
      rw [this]; exact hκ x
    · intro σ _; simp
    · intro σ _; simp
  set c0 := (Finset.univ.filter (fun σ : Perm (Fin N) => (fun x => σ (ι x)) = ι)).card with hc0
  have h1 : ∑ σ : Perm (Fin N), F (fun x => σ (ι x)) = (c0 : ℝ) * ∑ g ∈ I, F g := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Finset.sum_congr rfl (g := fun _ => F g) (fun σ hσ => by
      simp only [Finset.mem_filter] at hσ; rw [hσ.2])]
    rw [Finset.sum_const, nsmul_eq_mul, hc g hg]
  have h2 : (N.factorial : ℝ) = (c0 : ℝ) * (I.card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at this
    rw [this]
    push_cast
    rw [Finset.sum_congr rfl (fun g hg => by rw [hc g hg])]
    simp [Finset.sum_const, mul_comm]
  rw [h1, h2]; ring

/-- the tuple of positions `0, 1, …, k-1` -/
def bZero (N j k : ℕ) (h : j + k ≤ N) : Fin k → Fin (N - j) := fun l => ⟨l, by omega⟩

theorem sum_lbl_rho {N j k : ℕ} (h : j + k ≤ N) (b : Fin k → Fin (N - j))
    (hb : Function.Injective b) (Θ : Finset (Fin N) → (Fin k → Fin N) → ℝ) :
    ∑ σ : Perm (Fin N), Θ (revealed σ j) (fun l => posLbl σ j (b l))
      = ∑ σ : Perm (Fin N), Θ (revealed σ j) (fun l => posLbl σ j (bZero N j k h l)) := by
  let u : {p : Fin N // (p : ℕ) < j} ⊕ Fin k → Fin N :=
    Sum.elim (fun p => p.1) (fun l => ⟨j + l, by omega⟩)
  let v : {p : Fin N // (p : ℕ) < j} ⊕ Fin k → Fin N :=
    Sum.elim (fun p => p.1) (fun l => ⟨j + b l, by have := (b l).2; omega⟩)
  have hu : Function.Injective u := by
    rintro (p | l) (q | l') hpq
    · simp only [u, Sum.elim_inl] at hpq; exact congrArg Sum.inl (Subtype.ext hpq)
    · have h := congrArg Fin.val hpq
      simp only [u, Sum.elim_inl, Sum.elim_inr] at h
      have := p.2; omega
    · have h := congrArg Fin.val hpq
      simp only [u, Sum.elim_inl, Sum.elim_inr] at h
      have := q.2; omega
    · simp only [u, Sum.elim_inr, Fin.mk.injEq] at hpq
      exact congrArg Sum.inr (Fin.ext (by omega))
  have hv : Function.Injective v := by
    rintro (p | l) (q | l') hpq
    · simp only [v, Sum.elim_inl] at hpq; exact congrArg Sum.inl (Subtype.ext hpq)
    · have h := congrArg Fin.val hpq
      simp only [v, Sum.elim_inl, Sum.elim_inr] at h
      have := p.2; omega
    · have h := congrArg Fin.val hpq
      simp only [v, Sum.elim_inl, Sum.elim_inr] at h
      have := q.2; omega
    · simp only [v, Sum.elim_inr, Fin.mk.injEq] at hpq
      exact congrArg Sum.inr (hb (Fin.ext (by omega)))
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair u v hu hv
  have hρ1 : ∀ p : Fin N, (p : ℕ) < j → ρ p = p := fun p hp => by
    simpa [u, v] using hρ (Sum.inl ⟨p, hp⟩)
  have hρ2 : ∀ l : Fin k, ρ ⟨j + l, by omega⟩ = ⟨j + b l, by have := (b l).2; omega⟩ :=
    fun l => by simpa [u, v] using hρ (Sum.inr l)
  have hrev : ∀ σ : Perm (Fin N), revealed (σ * ρ) j = revealed σ j := by
    intro σ
    ext i
    have e : (σ * ρ).symm i = ρ.symm (σ.symm i) := rfl
    simp only [revealed, Finset.mem_filter, Finset.mem_univ, true_and, e]
    generalize σ.symm i = q
    constructor
    · intro hq
      have := hρ1 (ρ.symm q) hq
      have h2 : q = ρ.symm q := by
        conv_lhs => rw [← ρ.apply_symm_apply q]
        exact this
      rw [h2]; exact hq
    · intro hq
      rw [← hρ1 q hq]
      simpa using hq
  have hlbl : ∀ σ : Perm (Fin N), (fun l => posLbl (σ * ρ) j (bZero N j k h l))
      = (fun l => posLbl σ j (b l)) := by
    intro σ; funext l
    simp only [posLbl, bZero, Perm.coe_mul, Function.comp_apply]
    rw [hρ2 l]
  calc ∑ σ : Perm (Fin N), Θ (revealed σ j) (fun l => posLbl σ j (b l))
      = ∑ σ : Perm (Fin N), Θ (revealed (σ * ρ) j)
          (fun l => posLbl (σ * ρ) j (bZero N j k h l)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [hrev, hlbl]
    _ = _ := Equiv.sum_comp (Equiv.mulRight ρ)
          (fun σ => Θ (revealed σ j) (fun l => posLbl σ j (bZero N j k h l)))

end PermFacts

end PartJ

section PartK
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

section Collision

theorem card_inj_tuples (n k : ℕ) :
    (Finset.univ.filter (fun b : Fin k → Fin n => Function.Injective b)).card = n.descFactorial k := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fin n))]
  simp [Fintype.card_embedding_eq]

theorem desc_ratio_ge (n : ℕ) (hn : 0 < n) :
    ∀ k : ℕ, k ≤ n → 1 - (k : ℝ) * (k - 1) / (2 * n) ≤ (n.descFactorial k : ℝ) / (n : ℝ) ^ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := by omega
    have ih' := ih hkn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (n : ℝ) ^ k := pow_pos hn' k
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hkn, pow_succ]
    have hx : (0 : ℝ) ≤ 1 - (k : ℝ) / n := by
      rw [sub_nonneg, div_le_one hn']; exact_mod_cast hkn
    have e : ((n : ℝ) - k) * (n.descFactorial k : ℝ) / ((n : ℝ) ^ k * n)
        = ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) * (1 - (k : ℝ) / n) := by
      field_simp
    rw [e]
    have hc : (0 : ℝ) ≤ (k : ℝ) * (k - 1) / (2 * n) * ((k : ℝ) / n) := by
      have : (0 : ℝ) ≤ (k : ℝ) * (k - 1) := by
        rcases Nat.eq_zero_or_pos k with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ k := by exact_mod_cast h
          nlinarith
      positivity
    push_cast
    calc 1 - ((k : ℝ) + 1) * ((k : ℝ) + 1 - 1) / (2 * n)
        ≤ (1 - (k : ℝ) * (k - 1) / (2 * n)) * (1 - (k : ℝ) / n) := by
          have : ((k : ℝ) + 1) * ((k : ℝ) + 1 - 1) / (2 * n)
              = (k : ℝ) * (k - 1) / (2 * n) + (k : ℝ) / n := by
            field_simp; ring
          rw [this]; nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right ih' hx

theorem desc_ratio_le (n k : ℕ) (hn : 0 < n) :
    (n.descFactorial k : ℝ) / (n : ℝ) ^ k ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_one (pow_pos hn' k)]
  exact_mod_cast Nat.descFactorial_le_pow n k

theorem avgAll_avgInj (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (F : (Fin k → Fin n) → ℝ) (B : ℝ)
    (hF : ∀ b, |F b| ≤ B) :
    |(1 / (n : ℝ) ^ k) * ∑ b, F b
        - (1 / (n.descFactorial k : ℝ)) *
          ∑ b ∈ Finset.univ.filter (fun b : Fin k → Fin n => Function.Injective b), F b|
      ≤ 2 * B * ((k : ℝ) * (k - 1) / (2 * n)) := by
  classical
  set I := Finset.univ.filter (fun b : Fin k → Fin n => Function.Injective b) with hI
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set P : ℝ := (n : ℝ) ^ k with hP
  have hPpos : 0 < P := pow_pos hn' k
  have hDpos : (0 : ℝ) < n.descFactorial k := by exact_mod_cast Nat.descFactorial_pos.2 hk
  set D : ℝ := (n.descFactorial k : ℝ) with hD
  have hcard : (I.card : ℝ) = D := by rw [hI, card_inj_tuples]
  have hDP : D ≤ P := by
    have := desc_ratio_le n k hn
    rw [div_le_one hPpos] at this; exact this
  have hB : 0 ≤ B := by
    have b0 : Fin k → Fin n := fun _ => ⟨0, hn⟩
    exact le_trans (abs_nonneg _) (hF b0)
  have hsplit : ∑ b, F b = ∑ b ∈ I, F b + ∑ b ∈ Finset.univ.filter (fun b => ¬ Function.Injective b), F b := by
    rw [hI, Finset.sum_filter_add_sum_filter_not]
  set a := ∑ b ∈ I, F b with ha
  set r := ∑ b ∈ Finset.univ.filter (fun b : Fin k → Fin n => ¬ Function.Injective b), F b with hr
  have ha_bd : |a| ≤ B * D := by
    calc |a| ≤ ∑ b ∈ I, |F b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ I, B := Finset.sum_le_sum fun b _ => hF b
      _ = B * D := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  have hcard2 : ((Finset.univ.filter (fun b : Fin k → Fin n => ¬ Function.Injective b)).card : ℝ) = P - D := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k → Fin n)))
      (fun b : Fin k → Fin n => Function.Injective b)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
    have h2 : (((Finset.univ.filter (fun b : Fin k → Fin n => Function.Injective b)).card : ℕ) : ℝ) = D := hcard
    have h3 : (n : ℝ) ^ k = ((Finset.univ.filter (fun b : Fin k → Fin n => Function.Injective b)).card : ℝ)
        + ((Finset.univ.filter (fun b : Fin k → Fin n => ¬ Function.Injective b)).card : ℝ) := by
      exact_mod_cast this.symm
    rw [h2] at h3
    rw [hP]; linarith
  have hr_bd : |r| ≤ B * (P - D) := by
    calc |r| ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin k → Fin n => ¬ Function.Injective b), |F b| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin k → Fin n => ¬ Function.Injective b), B :=
          Finset.sum_le_sum fun b _ => hF b
      _ = B * (P - D) := by rw [Finset.sum_const, nsmul_eq_mul, hcard2]; ring
  have key : (1 / P) * (a + r) - (1 / D) * a = a * (D - P) / (P * D) + r / P := by
    field_simp; ring
  rw [hsplit, key]
  have hε : (P - D) / P ≤ (k : ℝ) * (k - 1) / (2 * n) := by
    have := desc_ratio_ge n hn k hk
    have e : (P - D) / P = 1 - D / P := by field_simp
    rw [e]; linarith
  have t1 : |a * (D - P) / (P * D)| ≤ B * ((P - D) / P) := by
    rw [abs_div, abs_mul, abs_of_nonpos (by linarith : D - P ≤ 0), abs_of_pos (mul_pos hPpos hDpos)]
    rw [div_le_iff₀ (mul_pos hPpos hDpos)]
    have : |a| * (-(D - P)) ≤ B * D * (P - D) := by
      have : -(D - P) = P - D := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right ha_bd (by linarith)
    calc |a| * -(D - P) ≤ B * D * (P - D) := this
      _ = B * ((P - D) / P) * (P * D) := by field_simp
  have t2 : |r / P| ≤ B * ((P - D) / P) := by
    rw [abs_div, abs_of_pos hPpos, div_le_iff₀ hPpos]
    calc |r| ≤ B * (P - D) := hr_bd
      _ = B * ((P - D) / P) * P := by field_simp
  calc |a * (D - P) / (P * D) + r / P| ≤ |a * (D - P) / (P * D)| + |r / P| := abs_add_le _ _
    _ ≤ B * ((P - D) / P) + B * ((P - D) / P) := add_le_add t1 t2
    _ = 2 * B * ((P - D) / P) := by ring
    _ ≤ 2 * B * ((k : ℝ) * (k - 1) / (2 * n)) := by
        exact mul_le_mul_of_nonneg_left hε (by linarith)

end Collision

end PartK

section PartL
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

section CoreF

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] {N : ℕ}

/-- entropy defect of a tuple `f` of labels given `S` -/
noncomputable def tcF (μ : Measure X) (ν : Measure (Fin N → X)) (S : Finset (Fin N)) {k : ℕ}
    (f : Fin k → Fin N) : ℝ :=
  (margEnt μ ν (S ∪ Finset.univ.image f) - margEnt μ ν S)
    - ∑ a : Fin k, (margEnt μ ν (insert (f a) S) - margEnt μ ν S)

theorem core_bound_f (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Fin N → X))
    [IsProbabilityMeasure ν] (hfin : klDiv ν (refLaw μ N) ≠ ⊤) (S : Finset (Fin N)) {k : ℕ}
    (d : Fin N) (f : Fin k → Fin N) (hS : ∀ l, f l ∉ S) (hinj : Function.Injective f)
    (A : (Fin k → X) → ℝ) (hA : Measurable A) (B : ℝ) (hB : ∀ x, |A x| ≤ B) :
    |∫ y, ∫ x, A x ∂(Measure.pi fun l : Fin k => condLaw ν S (f l) y) ∂(ν.map (rst (X := X) S))
        - ∫ ω, A (fun l : Fin k => ω (f l)) ∂ν|
      ≤ B * Real.sqrt (2 * tcF μ ν S f) := by
  let t : ℕ → Fin N := fun l => if h : l < k then f ⟨l, h⟩ else d
  have ht : ∀ l : Fin k, t l = f l := fun l => by simp [t]
  have h1 := core_bound μ ν hfin S t k (fun l hl => by
      have := hS ⟨l, hl⟩; simpa [t, hl] using this)
    (fun a b ha hb hab => by
      simp only [t, ha, hb, ↓reduceDIte] at hab
      exact congrArg Fin.val (hinj hab)) A hA B hB
  have e : tcR μ ν S t k = tcF μ ν S f := by
    unfold tcR tcF Bset
    have himg : (Finset.range k).image t = Finset.univ.image f := by
      ext i
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨l, hl, rfl⟩; exact ⟨⟨l, hl⟩, (ht ⟨l, hl⟩).symm⟩
      · rintro ⟨a, rfl⟩; exact ⟨a, a.2, ht a⟩
    rw [himg]
    congr 1
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun a _ => by rw [ht a]
  rw [e] at h1
  simpa only [ht] using h1

theorem revealed_add_eq (σ : Equiv.Perm (Fin N)) (j k : ℕ) (h : j + k ≤ N) :
    revealed σ (j + k) = revealed σ j ∪ Finset.univ.image
      (fun l : Fin k => σ ⟨j + l, by omega⟩) := by
  ext i
  simp only [revealed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_image]
  constructor
  · intro hi
    by_cases hj : (σ.symm i : ℕ) < j
    · exact Or.inl hj
    · refine Or.inr ⟨⟨(σ.symm i : ℕ) - j, by omega⟩, ?_⟩
      have : (⟨j + ((σ.symm i : ℕ) - j), by omega⟩ : Fin N) = σ.symm i :=
        Fin.ext (by simp; omega)
      simp [this]
  · rintro (hi | ⟨l, rfl⟩)
    · omega
    · simp

theorem revealedPlus_eq (σ : Equiv.Perm (Fin N)) (j a : ℕ) (h : j + a < N) :
    revealedPlus σ j a = insert (σ ⟨j + a, h⟩) (revealed σ j) := by
  ext i
  simp only [revealedPlus, revealed, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro (hi | hi)
    · exact Or.inr hi
    · left
      have : σ.symm i = ⟨j + a, h⟩ := Fin.ext hi
      rw [← this]; simp
  · rintro (rfl | hi)
    · right; simp
    · exact Or.inl hi

omit [StandardBorelSpace X] [Nonempty X] in
theorem tcF_eq_totalCorr (μ : Measure X) (ν : Measure (Fin N → X)) (σ : Equiv.Perm (Fin N))
    (j k : ℕ) (h : j + k ≤ N) :
    tcF μ ν (revealed σ j) (fun l : Fin k => σ ⟨j + l, by omega⟩) = totalCorr μ ν σ j k := by
  unfold tcF totalCorr jointCondEnt condEnt
  rw [← revealed_add_eq σ j k h, Finset.sum_range]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [revealedPlus_eq σ j a (by have := a.2; omega)]

end CoreF

end PartL

section PartM
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

section PerSigma

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] {N : ℕ}

/-- tuple of labels from position offsets -/
def lbl (σ : Equiv.Perm (Fin N)) (j : ℕ) {k : ℕ} (b : Fin k → Fin (N - j)) : Fin k → Fin N :=
  fun l => posLbl σ j (b l)

/-- test integral against the product of conditional laws -/
noncomputable def Gb (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] {k : ℕ}
    (A : (Fin k → X) → ℝ) (σ : Equiv.Perm (Fin N)) (j : ℕ) (b : Fin k → Fin (N - j)) : ℝ :=
  ∫ y, ∫ x, A x ∂(Measure.pi fun l : Fin k => condLaw ν (revealed σ j) (lbl σ j b l) y)
    ∂(ν.map (rst (X := X) (revealed σ j)))

/-- test integral against the original law at a tuple of labels -/
noncomputable def Tt (ν : Measure (Fin N → X)) {k : ℕ} (A : (Fin k → X) → ℝ)
    (g : Fin k → Fin N) : ℝ := ∫ ω, A (fun l => ω (g l)) ∂ν

omit [StandardBorelSpace X] [Nonempty X] in
theorem abs_Tt_le (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] {k : ℕ}
    (A : (Fin k → X) → ℝ) (B : ℝ) (hB : ∀ x, |A x| ≤ B) (g : Fin k → Fin N) :
    |Tt ν A g| ≤ B :=
  abs_integral_le_of_prob ν _ B fun _ => hB _

theorem abs_Gb_le (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] {k : ℕ}
    (A : (Fin k → X) → ℝ) (B : ℝ) (hB : ∀ x, |A x| ≤ B) (σ : Equiv.Perm (Fin N)) (j : ℕ)
    (b : Fin k → Fin (N - j)) : |Gb ν A σ j b| ≤ B :=
  abs_integral_le_of_prob _ _ B fun _ => abs_integral_le_of_prob _ A B hB

theorem lbl_inj (σ : Equiv.Perm (Fin N)) (j : ℕ) {k : ℕ} (b : Fin k → Fin (N - j))
    (hb : Function.Injective b) : Function.Injective (lbl σ j b) := by
  intro l l' h
  have := σ.injective h
  simp only [Fin.mk.injEq] at this
  exact hb (Fin.ext (by omega))

theorem lbl_notin (σ : Equiv.Perm (Fin N)) (j : ℕ) {k : ℕ} (b : Fin k → Fin (N - j)) (l : Fin k) :
    lbl σ j b l ∉ revealed σ j := by
  simp [lbl, posLbl, revealed]

theorem meanCond_integral (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] {k : ℕ}
    (A : (Fin k → X) → ℝ) (hA : Measurable A) (B : ℝ) (hB : ∀ x, |A x| ≤ B)
    (σ : Equiv.Perm (Fin N)) (j : ℕ) :
    ∫ y, ∫ x, A x ∂(Measure.pi fun _ : Fin k => meanCond ν (revealed σ j) y)
        ∂(ν.map (rst (X := X) (revealed σ j)))
      = (1 / ((N - j : ℕ) : ℝ) ^ k) * ∑ b : Fin k → Fin (N - j), Gb ν A σ j b := by
  rw [integral_mean_expand (((N - j : ℕ) : ℝ≥0)⁻¹)
    (fun p : Fin (N - j) => condLaw ν (revealed σ j) (posLbl σ j p))
    (ν.map (rst (X := X) (revealed σ j))) A hA B hB _ (fun y => meanCond_eq ν σ j y)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hw : (((((N - j : ℕ) : ℝ≥0)⁻¹ : ℝ≥0)) : ℝ) ^ k = 1 / ((N - j : ℕ) : ℝ) ^ k := by
    rw [NNReal.coe_inv, NNReal.coe_natCast, one_div, inv_pow]
  rw [hw]
  rfl

theorem per_sigma (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Fin N → X))
    [IsProbabilityMeasure ν] (hfin : klDiv ν (refLaw μ N) ≠ ⊤) {k : ℕ}
    (A : (Fin k → X) → ℝ) (hA : Measurable A) (B : ℝ) (hB : ∀ x, |A x| ≤ B)
    (σ : Equiv.Perm (Fin N)) (j : ℕ) (hj : j < N) (hjk : j + k ≤ N) :
    |(∫ y, ∫ x, A x ∂(Measure.pi fun _ : Fin k => meanCond ν (revealed σ j) y)
        ∂(ν.map (rst (X := X) (revealed σ j))))
      - (1 / ((N - j).descFactorial k : ℝ)) *
        ∑ b ∈ Finset.univ.filter (fun b : Fin k → Fin (N - j) => Function.Injective b),
          Tt ν A (lbl σ j b)|
    ≤ 2 * B * ((k : ℝ) * (k - 1) / (2 * ((N - j : ℕ) : ℝ))) +
      B * ((1 / ((N - j).descFactorial k : ℝ)) *
        ∑ b ∈ Finset.univ.filter (fun b : Fin k → Fin (N - j) => Function.Injective b),
          Real.sqrt (2 * tcF μ ν (revealed σ j) (lbl σ j b))) := by
  classical
  set n := N - j with hn
  set I := Finset.univ.filter (fun b : Fin k → Fin n => Function.Injective b) with hI
  have hnpos : 0 < n := by omega
  have hkn : k ≤ n := by omega
  have hDpos : (0 : ℝ) < (n.descFactorial k : ℝ) := by exact_mod_cast Nat.descFactorial_pos.2 hkn
  have hcard : (I.card : ℝ) = (n.descFactorial k : ℝ) := by rw [hI, card_inj_tuples]
  rw [meanCond_integral ν A hA B hB σ j]
  have h1 := avgAll_avgInj n k hnpos hkn (fun b => Gb ν A σ j b) B (abs_Gb_le ν A B hB σ j)
  have h2 : |(1 / (n.descFactorial k : ℝ)) * ∑ b ∈ I, Gb ν A σ j b
      - (1 / (n.descFactorial k : ℝ)) * ∑ b ∈ I, Tt ν A (lbl σ j b)|
      ≤ B * ((1 / (n.descFactorial k : ℝ)) *
        ∑ b ∈ I, Real.sqrt (2 * tcF μ ν (revealed σ j) (lbl σ j b))) := by
    have hd : (0 : ℝ) < 1 / (n.descFactorial k : ℝ) := by positivity
    have hB0 : 0 ≤ B := by
      have b0 : Fin k → X := fun _ => Classical.arbitrary X
      exact le_trans (abs_nonneg _) (hB b0)
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos hd]
    have : |∑ b ∈ I, (Gb ν A σ j b - Tt ν A (lbl σ j b))|
        ≤ ∑ b ∈ I, B * Real.sqrt (2 * tcF μ ν (revealed σ j) (lbl σ j b)) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun b hb => ?_)
      have hbi : Function.Injective b := by
        simpa [hI] using hb
      obtain ⟨d⟩ : Nonempty (Fin N) := ⟨⟨j, hj⟩⟩
      exact core_bound_f μ ν hfin (revealed σ j) d (lbl σ j b) (lbl_notin σ j b)
        (lbl_inj σ j b hbi) A hA B hB
    rw [← Finset.mul_sum] at this
    calc 1 / (n.descFactorial k : ℝ) * |∑ b ∈ I, (Gb ν A σ j b - Tt ν A (lbl σ j b))|
        ≤ 1 / (n.descFactorial k : ℝ) * (B * ∑ b ∈ I, Real.sqrt (2 * tcF μ ν (revealed σ j) (lbl σ j b))) :=
          mul_le_mul_of_nonneg_left this hd.le
      _ = _ := by ring
  exact le_trans (abs_sub_le _ ((1 / (n.descFactorial k : ℝ)) * ∑ b ∈ I, Gb ν A σ j b) _)
    (add_le_add h1 h2)

end PerSigma

end PartM

section PartN
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

section PerJ

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] {N : ℕ}

theorem abs_permAvg_le (f g : Equiv.Perm (Fin N) → ℝ) (h : ∀ σ, |f σ| ≤ g σ) :
    |permAvg N f| ≤ permAvg N g := by
  unfold permAvg
  have hf : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  rw [abs_div, abs_of_pos hf]
  exact div_le_div_of_nonneg_right
    (le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun σ _ => h σ)) hf.le

omit [StandardBorelSpace X] [Nonempty X] in
theorem permAvg_Tinj (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] {k : ℕ}
    (A : (Fin k → X) → ℝ) (j : ℕ) (hjk : j + k ≤ N) :
    permAvg N (fun σ => (1 / ((N - j).descFactorial k : ℝ)) *
        ∑ b ∈ Finset.univ.filter (fun b : Fin k → Fin (N - j) => Function.Injective b),
          Tt ν A (lbl σ j b))
      = (1 / (N.descFactorial k : ℝ)) *
        ∑ g ∈ Finset.univ.filter (fun g : Fin k → Fin N => Function.Injective g), Tt ν A g := by
  classical
  set n := N - j with hn
  set I := Finset.univ.filter (fun b : Fin k → Fin n => Function.Injective b) with hI
  have hkn : k ≤ n := by omega
  have hkN : k ≤ N := by omega
  have hDn : (0 : ℝ) < (n.descFactorial k : ℝ) := by exact_mod_cast Nat.descFactorial_pos.2 hkn
  have hDN : (0 : ℝ) < (N.descFactorial k : ℝ) := by exact_mod_cast Nat.descFactorial_pos.2 hkN
  have hcard : (I.card : ℝ) = (n.descFactorial k : ℝ) := by rw [hI, card_inj_tuples]
  set ι : Fin k → Fin N := fun l => ⟨j + l, by omega⟩ with hι
  have hιinj : Function.Injective ι := by
    intro l l' h
    simp only [hι, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hcardN : ((Finset.univ.filter (fun g : Fin k → Fin N => Function.Injective g)).card : ℝ)
      = (N.descFactorial k : ℝ) := by rw [card_inj_tuples]
  have hF : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  unfold permAvg
  have e1 : ∑ σ : Equiv.Perm (Fin N), (1 / (n.descFactorial k : ℝ)) *
        ∑ b ∈ I, Tt ν A (lbl σ j b)
      = ∑ σ : Equiv.Perm (Fin N), Tt ν A (fun l => σ (ι l)) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    have : ∀ b ∈ I, ∑ σ : Equiv.Perm (Fin N), Tt ν A (lbl σ j b)
        = ∑ σ : Equiv.Perm (Fin N), Tt ν A (fun l => σ (ι l)) := by
      intro b hb
      have hbi : Function.Injective b := by simpa [hI] using hb
      exact sum_lbl_rho hjk b hbi (fun _ t => Tt ν A t)
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
  rw [e1]
  have hU' : ∑ σ : Equiv.Perm (Fin N), Tt ν A (fun l => σ (ι l))
      = (N.factorial : ℝ) * ((1 / (N.descFactorial k : ℝ)) *
        ∑ g ∈ Finset.univ.filter (fun g : Fin k → Fin N => Function.Injective g), Tt ν A g) := by
    have := sum_perm_comp_inj ι hιinj (Tt ν A)
    rw [hcardN] at this
    field_simp
    linarith
  rw [hU']
  field_simp

omit [StandardBorelSpace X] [Nonempty X] in
theorem permAvg_sqrt_tc (μ : Measure X) (ν : Measure (Fin N → X)) {k : ℕ} (j : ℕ)
    (hjk : j + k ≤ N) :
    permAvg N (fun σ => (1 / ((N - j).descFactorial k : ℝ)) *
        ∑ b ∈ Finset.univ.filter (fun b : Fin k → Fin (N - j) => Function.Injective b),
          Real.sqrt (2 * tcF μ ν (revealed σ j) (lbl σ j b)))
      = permAvg N (fun σ => Real.sqrt (2 * totalCorr μ ν σ j k)) := by
  classical
  set n := N - j with hn
  set I := Finset.univ.filter (fun b : Fin k → Fin n => Function.Injective b) with hI
  have hkn : k ≤ n := by omega
  have hDn : (0 : ℝ) < (n.descFactorial k : ℝ) := by exact_mod_cast Nat.descFactorial_pos.2 hkn
  have hcard : (I.card : ℝ) = (n.descFactorial k : ℝ) := by rw [hI, card_inj_tuples]
  unfold permAvg
  congr 1
  have e0 : ∀ σ : Equiv.Perm (Fin N), Real.sqrt (2 * totalCorr μ ν σ j k)
      = (fun (S : Finset (Fin N)) (t : Fin k → Fin N) => Real.sqrt (2 * tcF μ ν S t))
          (revealed σ j) (fun l => posLbl σ j (bZero N j k hjk l)) := by
    intro σ
    simp only
    rw [← tcF_eq_totalCorr μ ν σ j k hjk]
    rfl
  rw [Finset.sum_congr rfl (fun σ _ => e0 σ)]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have : ∀ b ∈ I, ∑ σ : Equiv.Perm (Fin N), Real.sqrt (2 * tcF μ ν (revealed σ j) (lbl σ j b))
      = ∑ σ : Equiv.Perm (Fin N), (fun (S : Finset (Fin N)) (t : Fin k → Fin N) =>
          Real.sqrt (2 * tcF μ ν S t)) (revealed σ j) (fun l => posLbl σ j (bZero N j k hjk l)) := by
    intro b hb
    have hbi : Function.Injective b := by simpa [hI] using hb
    exact sum_lbl_rho hjk b hbi (fun S t => Real.sqrt (2 * tcF μ ν S t))
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcard]
  rw [show ((N - j).descFactorial k : ℝ) = (n.descFactorial k : ℝ) from rfl]
  field_simp

theorem permAvg_const_add_mul (N : ℕ) (c B : ℝ) (f : Equiv.Perm (Fin N) → ℝ) :
    permAvg N (fun σ => c + B * f σ) = c + B * permAvg N f := by
  unfold permAvg
  have hF : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem per_j (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Fin N → X))
    [IsProbabilityMeasure ν] (hfin : klDiv ν (refLaw μ N) ≠ ⊤) {k : ℕ}
    (A : (Fin k → X) → ℝ) (hA : Measurable A) (B : ℝ) (hB : ∀ x, |A x| ≤ B)
    (j : ℕ) (hj : j < N) (hjk : j + k ≤ N) :
    |permAvg N (fun σ => ∫ y, ∫ x, A x ∂(Measure.pi fun _ : Fin k => meanCond ν (revealed σ j) y)
          ∂(ν.map (rst (X := X) (revealed σ j))))
        - ∫ ω, ∫ x, A x ∂(Measure.pi fun _ : Fin k => empirical ω) ∂ν|
      ≤ 2 * B * ((k : ℝ) * (k - 1) / (2 * ((N - j : ℕ) : ℝ)))
        + 2 * B * ((k : ℝ) * (k - 1) / (2 * (N : ℝ)))
        + B * permAvg N (fun σ => Real.sqrt (2 * totalCorr μ ν σ j k)) := by
  classical
  have hkN : k ≤ N := by omega
  have hN : 0 < N := by omega
  set Γ : Equiv.Perm (Fin N) → ℝ := fun σ =>
    ∫ y, ∫ x, A x ∂(Measure.pi fun _ : Fin k => meanCond ν (revealed σ j) y)
      ∂(ν.map (rst (X := X) (revealed σ j))) with hΓ
  set Ti : Equiv.Perm (Fin N) → ℝ := fun σ => (1 / ((N - j).descFactorial k : ℝ)) *
        ∑ b ∈ Finset.univ.filter (fun b : Fin k → Fin (N - j) => Function.Injective b),
          Tt ν A (lbl σ j b) with hTi
  set c : ℝ := 2 * B * ((k : ℝ) * (k - 1) / (2 * ((N - j : ℕ) : ℝ))) with hc
  set Bd : Equiv.Perm (Fin N) → ℝ := fun σ => c + B * ((1 / ((N - j).descFactorial k : ℝ)) *
        ∑ b ∈ Finset.univ.filter (fun b : Fin k → Fin (N - j) => Function.Injective b),
          Real.sqrt (2 * tcF μ ν (revealed σ j) (lbl σ j b))) with hBd
  have h1 : |permAvg N Γ - permAvg N Ti| ≤ permAvg N Bd := by
    rw [← permAvg_sub]
    exact abs_permAvg_le _ _ fun σ => per_sigma μ ν hfin A hA B hB σ j hj hjk
  have h1' : permAvg N Bd = c + B * permAvg N (fun σ => Real.sqrt (2 * totalCorr μ ν σ j k)) := by
    rw [hBd, permAvg_const_add_mul, permAvg_sqrt_tc μ ν j hjk]
  have h2 : permAvg N Ti = (1 / (N.descFactorial k : ℝ)) *
      ∑ g ∈ Finset.univ.filter (fun g : Fin k → Fin N => Function.Injective g), Tt ν A g :=
    permAvg_Tinj ν A j hjk
  have h3 := avgAll_avgInj N k hN hkN (fun g => Tt ν A g) B (abs_Tt_le ν A B hB)
  have h4 : ∫ ω, ∫ x, A x ∂(Measure.pi fun _ : Fin k => empirical ω) ∂ν
      = (1 / (N : ℝ) ^ k) * ∑ g : Fin k → Fin N, Tt ν A g := by
    rw [integral_empirical_expand ν k A hA B hB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [NNReal.coe_inv, NNReal.coe_natCast, one_div, inv_pow]
    rfl
  rw [h4]
  have h3' : |permAvg N Ti - (1 / (N : ℝ) ^ k) * ∑ g : Fin k → Fin N, Tt ν A g|
      ≤ 2 * B * ((k : ℝ) * (k - 1) / (2 * (N : ℝ))) := by
    rw [h2, abs_sub_comm]; exact h3
  rw [h1'] at h1
  calc _ ≤ |permAvg N Γ - permAvg N Ti| + |permAvg N Ti - (1 / (N : ℝ) ^ k) * ∑ g : Fin k → Fin N, Tt ν A g| :=
        abs_sub_le _ _ _
    _ ≤ _ := by linarith

end PerJ

end PartN

section PartO
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

section Sum

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] {N : ℕ}

theorem sum_sqrt_sq_le (m : ℕ) (f : ℕ → Equiv.Perm (Fin N) → ℝ) (hf : ∀ j ∈ Finset.range m, ∀ σ, 0 ≤ f j σ) :
    (∑ j ∈ Finset.range m, permAvg N (fun σ => Real.sqrt (2 * f j σ))) ^ 2
      ≤ 2 * m * ∑ j ∈ Finset.range m, permAvg N (f j) := by
  classical
  unfold permAvg
  have hF : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  set s : ℕ → Equiv.Perm (Fin N) → ℝ := fun j σ => Real.sqrt (2 * f j σ) with hs
  have e : ∑ j ∈ Finset.range m, (∑ σ, s j σ) / (N.factorial : ℝ)
      = (∑ p ∈ Finset.range m ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin N))), s p.1 p.2)
        / (N.factorial : ℝ) := by
    rw [Finset.sum_product, Finset.sum_div]
  have e2 : ∑ j ∈ Finset.range m, (∑ σ, f j σ) / (N.factorial : ℝ)
      = (∑ p ∈ Finset.range m ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin N))), f p.1 p.2)
        / (N.factorial : ℝ) := by
    rw [Finset.sum_product, Finset.sum_div]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.range m ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin N)))) (fun _ => (1 : ℝ))
    (fun p => s p.1 p.2)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_product, Finset.card_range,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one] at cs
  have hsq : ∑ p ∈ Finset.range m ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin N))), (s p.1 p.2) ^ 2
      = 2 * ∑ p ∈ Finset.range m ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin N))), f p.1 p.2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [hs]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) (hf _ (Finset.mem_product.1 hp).1 _))]
  rw [hsq] at cs
  rw [e, e2, div_pow, div_le_iff₀ (by positivity)]
  push_cast at cs
  have : 2 * (m : ℝ) * ((∑ p ∈ Finset.range m ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin N))), f p.1 p.2)
      / (N.factorial : ℝ)) * (N.factorial : ℝ) ^ 2
      = (m * (N.factorial : ℝ)) * (2 * ∑ p ∈ Finset.range m ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin N))), f p.1 p.2) := by
    field_simp
  rw [this]
  exact cs

theorem abs_avg_le {n k : ℕ} (hn : 0 < n) (F : (Fin k → Fin n) → ℝ) (B : ℝ)
    (hF : ∀ b, |F b| ≤ B) : |(1 / (n : ℝ) ^ k) * ∑ b, F b| ≤ B := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ) ^ k)]
  have h1 : |∑ b, F b| ≤ (n : ℝ) ^ k * B := by
    calc |∑ b, F b| ≤ ∑ b, |F b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b : Fin k → Fin n, B := Finset.sum_le_sum fun b _ => hF b
      _ = (n : ℝ) ^ k * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  calc 1 / (n : ℝ) ^ k * |∑ b, F b| ≤ 1 / (n : ℝ) ^ k * ((n : ℝ) ^ k * B) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = B := by field_simp

theorem abs_Gam_le (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] {k : ℕ}
    (A : (Fin k → X) → ℝ) (hA : Measurable A) (B : ℝ) (hB : ∀ x, |A x| ≤ B)
    (σ : Equiv.Perm (Fin N)) (j : ℕ) (hj : j < N) :
    |∫ y, ∫ x, A x ∂(Measure.pi fun _ : Fin k => meanCond ν (revealed σ j) y)
        ∂(ν.map (rst (X := X) (revealed σ j)))| ≤ B := by
  rw [meanCond_integral ν A hA B hB σ j]
  exact abs_avg_le (by omega) _ B (abs_Gb_le ν A B hB σ j)

omit [Nonempty X] in
theorem abs_emp_le (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν] {k : ℕ}
    (A : (Fin k → X) → ℝ) (hA : Measurable A) (B : ℝ) (hB : ∀ x, |A x| ≤ B) (hN : 0 < N) :
    |∫ ω, ∫ x, A x ∂(Measure.pi fun _ : Fin k => empirical ω) ∂ν| ≤ B := by
  have h4 : ∫ ω, ∫ x, A x ∂(Measure.pi fun _ : Fin k => empirical ω) ∂ν
      = (1 / (N : ℝ) ^ k) * ∑ g : Fin k → Fin N, Tt ν A g := by
    rw [integral_empirical_expand ν k A hA B hB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [NNReal.coe_inv, NNReal.coe_natCast, one_div, inv_pow]
    rfl
  rw [h4]
  exact abs_avg_le hN _ B (abs_Tt_le ν A B hB)

theorem tcF_nonneg (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Fin N → X))
    [IsProbabilityMeasure ν] (hfin : klDiv ν (refLaw μ N) ≠ ⊤) (S : Finset (Fin N)) {k : ℕ}
    (d : Fin N) (f : Fin k → Fin N) (hS : ∀ l, f l ∉ S) (hinj : Function.Injective f) :
    0 ≤ tcF μ ν S f := by
  let t : ℕ → Fin N := fun l => if h : l < k then f ⟨l, h⟩ else d
  have hS' : ∀ l, l < k → t l ∉ S := fun l hl => by
    have := hS ⟨l, hl⟩; simpa [t, hl] using this
  have hinj' : ∀ a b, a < k → b < k → t a = t b → a = b := fun a b ha hb hab => by
    simp only [t, ha, hb, ↓reduceDIte] at hab
    exact congrArg Fin.val (hinj hab)
  obtain ⟨_, hreal⟩ := klDiv_tuple ν μ hfin S t k hS' hinj' k le_rfl
  have e : tcR μ ν S t k = tcF μ ν S f := by
    unfold tcR tcF Bset
    have himg : (Finset.range k).image t = Finset.univ.image f := by
      ext i
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, by simp [t, ha]⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.2, by simp [t]⟩
    rw [himg, Finset.sum_range]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [t]
  rw [← e]
  unfold tcR
  rw [← hreal]
  exact ENNReal.toReal_nonneg

end Sum

end PartO

section PartP
open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal

section Final

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] {N : ℕ}

theorem totalCorr_nonneg' (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Fin N → X))
    [IsProbabilityMeasure ν] (hfin : klDiv ν (refLaw μ N) ≠ ⊤) (σ : Equiv.Perm (Fin N))
    (j k : ℕ) (hjk : j + k ≤ N) (hN : 0 < N) : 0 ≤ totalCorr μ ν σ j k := by
  rw [← tcF_eq_totalCorr μ ν σ j k hjk]
  refine tcF_nonneg μ ν hfin _ ⟨0, hN⟩ _ ?_ ?_
  · intro l hl
    simp only [revealed, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] at hl
    simp at hl
  · intro a b hab
    have := σ.injective hab
    simp only [Fin.mk.injEq] at this
    exact Fin.ext (by omega)

theorem conditional_products_and_collision_bounds {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X] (k : ℕ) (B τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure X) [IsProbabilityMeasure μ] (N M : ℕ)
      (ν : Measure (Fin N → X)) [IsProbabilityMeasure ν],
      τ ≤ (M : ℝ) / N → M ≤ N → DGPS.relativeEntropy ν (refLaw μ N) ≠ ⊤ →
      ∀ A : (Fin k → X) → ℝ, Measurable A → (∀ x, |A x| ≤ B) →
      |∑ j ∈ range (N - M), permAvg N (fun σ => ∫ y, ∫ x, A x
            ∂(Measure.pi fun _ : Fin k => meanCond ν (revealed σ j) y)
            ∂(ν.map (rst (X := X) (revealed σ j))))
          - ((N - M : ℕ) : ℝ) * ∫ ω, ∫ x, A x ∂(Measure.pi fun _ : Fin k => empirical ω) ∂ν|
        ≤ C * (1 + Real.sqrt (DGPS.relativeEntropy ν (refLaw μ N)).toReal) := by
  classical
  set K : ℝ := (k : ℝ) * (k - 1) with hK
  have hK0 : 0 ≤ K := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [hK, h]
    · have : (1 : ℝ) ≤ k := by exact_mod_cast h
      rw [hK]; nlinarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨|B| * (K / τ + K + Real.sqrt (4 * K / τ)) + 4 * k * |B| / τ, by positivity, ?_⟩
  intro μ _ N M ν _ hτM hMN hν A hA hAB
  have hfin : klDiv ν (refLaw μ N) ≠ ⊤ := by
    have : DGPS.relativeEntropy ν (refLaw μ N) = klDiv ν (refLaw μ N) :=
      DGPS.Analysis.relativeEntropy_eq_klDiv
    exact this ▸ hν
  set H : ℝ := (DGPS.relativeEntropy ν (refLaw μ N)).toReal with hH
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hsH : 0 ≤ Real.sqrt H := Real.sqrt_nonneg _
  obtain ⟨x0⟩ := ‹Nonempty X›
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hAB (fun _ => x0))
  rw [abs_of_nonneg hB0]
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hτM; linarith
    · exact h
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hMτ : τ * N ≤ M := by
    rw [le_div_iff₀ hNr] at hτM; exact hτM
  have hMpos : (0 : ℝ) < M := by nlinarith
  set E : ℝ := ∫ ω, ∫ x, A x ∂(Measure.pi fun _ : Fin k => empirical ω) ∂ν with hE
  set a : ℕ → ℝ := fun j => permAvg N (fun σ => ∫ y, ∫ x, A x
            ∂(Measure.pi fun _ : Fin k => meanCond ν (revealed σ j) y)
            ∂(ν.map (rst (X := X) (revealed σ j)))) with ha
  set m := N - M with hm
  have hmN : (m : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N M
  have hmτ : (m : ℝ) * τ ≤ M := by nlinarith
  have hred : |∑ j ∈ range m, a j - (m : ℝ) * E| ≤ ∑ j ∈ range m, |a j - E| := by
    have : ∑ j ∈ range m, a j - (m : ℝ) * E = ∑ j ∈ range m, (a j - E) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [this]; exact Finset.abs_sum_le_sum_abs _ _
  have hs1 : (1 : ℝ) ≤ 1 + Real.sqrt H := by linarith
  have hCnn : 0 ≤ B * (K / τ + K + Real.sqrt (4 * K / τ)) := by positivity
  have hR : 0 ≤ 4 * (k : ℝ) * B / τ := by positivity
  by_cases hcase : M < 2 * k
  · -- trivial regime
    have hab : ∀ j ∈ range m, |a j - E| ≤ 2 * B := by
      intro j hj
      have hjN : j < N := by have := mem_range.1 hj; omega
      have h1 : |a j| ≤ B := by
        rw [ha]
        have := abs_permAvg_le (N := N) (fun σ => ∫ y, ∫ x, A x
            ∂(Measure.pi fun _ : Fin k => meanCond ν (revealed σ j) y)
            ∂(ν.map (rst (X := X) (revealed σ j)))) (fun _ => B)
          (fun σ => abs_Gam_le ν A hA B hAB σ j hjN)
        rwa [permAvg_const] at this
      have h2 := abs_emp_le ν A hA B hAB hNpos
      calc |a j - E| ≤ |a j| + |E| := abs_sub _ _
        _ ≤ 2 * B := by linarith
    have hNk : (N : ℝ) * τ ≤ 2 * k := by
      have : (M : ℝ) < 2 * k := by exact_mod_cast hcase
      nlinarith
    have hmk : (m : ℝ) * τ ≤ 2 * k := le_trans (by nlinarith) hNk
    have : |∑ j ∈ range m, a j - (m : ℝ) * E| ≤ 4 * k * B / τ := by
      refine le_trans hred (le_trans (Finset.sum_le_sum hab) ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, le_div_iff₀ hτ]
      nlinarith
    nlinarith
  · have hcase := not_lt.1 hcase
    have hkM : k ≤ M := by omega
    have hperj : ∀ j ∈ range m, |a j - E| ≤
        B * K / M + B * K / N + B * permAvg N (fun σ => Real.sqrt (2 * totalCorr μ ν σ j k)) := by
      intro j hj
      have hjm := mem_range.1 hj
      have hjN : j < N := by omega
      have hjk : j + k ≤ N := by omega
      have := per_j μ ν hfin A hA B hAB j hjN hjk
      have hn : (M : ℝ) ≤ ((N - j : ℕ) : ℝ) := by exact_mod_cast (by omega : M ≤ N - j)
      have e1 : 2 * B * (K / (2 * ((N - j : ℕ) : ℝ))) = B * K / ((N - j : ℕ) : ℝ) := by
        field_simp
      have e2 : 2 * B * (K / (2 * (N : ℝ))) = B * K / (N : ℝ) := by field_simp
      have e3 : B * K / ((N - j : ℕ) : ℝ) ≤ B * K / M :=
        div_le_div_of_nonneg_left (by positivity) hMpos hn
      refine le_trans this ?_
      rw [hK] at e1 e2 e3 ⊢
      linarith
    have hS := sum_sqrt_sq_le (N := N) m (fun j σ => totalCorr μ ν σ j k)
      (fun j hj σ => totalCorr_nonneg' μ ν hfin σ j k (by have := mem_range.1 hj; omega) hNpos)
    obtain ⟨_, _, _, h4⟩ := conditioning_entropy_identities μ ν hν
    have hT := h4 k M hkM hMN
    have hcpos : (0 : ℝ) < (M : ℝ) - k + 2 := by
      have : (k : ℝ) ≤ M := by exact_mod_cast hkM
      linarith
    have hM2 : 2 * (k : ℝ) ≤ M := by exact_mod_cast hcase
    have hq : (m : ℝ) / ((M : ℝ) - k + 2) ≤ 2 / τ := by
      rw [div_le_div_iff₀ hcpos hτ]; nlinarith
    set S : ℝ := ∑ j ∈ range m, permAvg N (fun σ => Real.sqrt (2 * totalCorr μ ν σ j k)) with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun j hj => permAvg_nonneg _ fun σ => Real.sqrt_nonneg _
    have hTT : ∑ j ∈ range m, permAvg N (fun σ => totalCorr μ ν σ j k)
        ≤ (K / ((M : ℝ) - k + 2)) * H := hT
    have hS2 : S ^ 2 ≤ 4 * K / τ * H := by
      have h1 : S ^ 2 ≤ 2 * m * ((K / ((M : ℝ) - k + 2)) * H) :=
        le_trans hS (mul_le_mul_of_nonneg_left hTT (by positivity))
      refine le_trans h1 ?_
      have : 2 * (m : ℝ) * ((K / ((M : ℝ) - k + 2)) * H) = 2 * K * H * ((m : ℝ) / ((M : ℝ) - k + 2)) := by
        field_simp
      rw [this]
      have : 2 * K * H * ((m : ℝ) / ((M : ℝ) - k + 2)) ≤ 2 * K * H * (2 / τ) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      refine le_trans this (le_of_eq ?_)
      field_simp
      ring
    have hSle : S ≤ Real.sqrt (4 * K / τ) * Real.sqrt H := by
      rw [← Real.sqrt_mul (by positivity)]
      exact le_trans (le_abs_self S) (Real.abs_le_sqrt hS2)
    have hsum : ∑ j ∈ range m, |a j - E| ≤ m * (B * K / M) + m * (B * K / N) + B * S := by
      refine le_trans (Finset.sum_le_sum hperj) ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact le_of_eq rfl
    have hBK : 0 ≤ B * K := by positivity
    have hA1 : (m : ℝ) * (B * K / M) ≤ B * K / τ := by
      have : (m : ℝ) / M ≤ 1 / τ := by
        rw [div_le_div_iff₀ hMpos hτ]; nlinarith
      calc (m : ℝ) * (B * K / M) = B * K * ((m : ℝ) / M) := by ring
        _ ≤ B * K * (1 / τ) := mul_le_mul_of_nonneg_left this hBK
        _ = B * K / τ := by ring
    have hA2 : (m : ℝ) * (B * K / N) ≤ B * K := by
      calc (m : ℝ) * (B * K / N) ≤ N * (B * K / N) :=
            mul_le_mul_of_nonneg_right hmN (by positivity)
        _ = B * K := by field_simp
    have hA3 : B * S ≤ B * (Real.sqrt (4 * K / τ)) * Real.sqrt H := by
      calc B * S ≤ B * (Real.sqrt (4 * K / τ) * Real.sqrt H) :=
            mul_le_mul_of_nonneg_left hSle hB0
        _ = _ := by ring
    have hfinal : |∑ j ∈ range m, a j - (m : ℝ) * E|
        ≤ B * K / τ + B * K + B * Real.sqrt (4 * K / τ) * Real.sqrt H := by
      linarith
    refine le_trans hfinal ?_
    have hP : 0 ≤ B * (K / τ + K) := by positivity
    have hQ : 0 ≤ B * Real.sqrt (4 * K / τ) := by positivity
    have e : B * K / τ + B * K = B * (K / τ + K) := by ring
    have hexp : (B * (K / τ + K + Real.sqrt (4 * K / τ)) + 4 * (k : ℝ) * B / τ) * (1 + Real.sqrt H)
        = (B * (K / τ + K) + B * Real.sqrt (4 * K / τ) + 4 * (k : ℝ) * B / τ)
          + (B * (K / τ + K) + B * Real.sqrt (4 * K / τ) + 4 * (k : ℝ) * B / τ) * Real.sqrt H := by
      ring
    rw [hexp]
    have h1 := mul_nonneg hP hsH
    have h2 := mul_nonneg hR hsH
    have h3 : B * Real.sqrt (4 * K / τ) * Real.sqrt H ≤ (B * Real.sqrt (4 * K / τ)) * Real.sqrt H := le_rfl
    have h4 : (B * (K / τ + K) + B * Real.sqrt (4 * K / τ) + 4 * (k : ℝ) * B / τ) * Real.sqrt H
        = B * (K / τ + K) * Real.sqrt H + B * Real.sqrt (4 * K / τ) * Real.sqrt H
          + 4 * (k : ℝ) * B / τ * Real.sqrt H := by ring
    rw [h4]
    linarith

end Final

end PartP

end DGPS.Lipschitz
