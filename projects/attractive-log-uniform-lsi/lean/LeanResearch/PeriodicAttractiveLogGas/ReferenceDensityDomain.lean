import LeanResearch.PeriodicAttractiveLogGas.ReferenceConvolutionContinuity

/-! The exact closed convex finite-product L1 domain in source lines
2350--2391. Conditional map membership does not assert a fixed point. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.ReferenceDensityDomain

open MeshCells LabelOccupations ReferenceConvolutionContinuity

/-- Exactly the predicate defining the released AdmissibleDensity subtype. -/
def cellDomain (ν : Measure Torus) : Set (Lp ℝ 1 ν) :=
  {f | (∀ᵐ x ∂ν, Real.exp (-1) ≤ f x ∧ f x ≤ Real.exp 1) ∧ (∫ x, f x ∂ν) = 1}

abbrev Ambient {J : ℕ} (hJ : 0 < J) := (a : MeshIndex J) → Lp ℝ 1 (meshCellMeasure J hJ a)

def admissibleDomain {J : ℕ} (hJ : 0 < J) : Set (Ambient hJ) :=
  {φ | ∀ a, φ a ∈ cellDomain (meshCellMeasure J hJ a)}

theorem cellDomain_nonempty (ν : Measure Torus) [IsProbabilityMeasure ν] :
    (cellDomain ν).Nonempty := by
  obtain ⟨f⟩ := admissibleDensity_nonempty ν
  exact ⟨f.val, f.property⟩

theorem admissibleDomain_nonempty {J : ℕ} (hJ : 0 < J) :
    (admissibleDomain hJ).Nonempty := by
  classical
  choose φ hφ using fun a : MeshIndex J => cellDomain_nonempty (meshCellMeasure J hJ a)
  exact ⟨φ, hφ⟩

/-- The product of the released density subtypes has precisely the ambient
subspace topology used in the fixed-point argument. -/
def familyHomeomorph {J : ℕ} (hJ : 0 < J) :
    DensityFamily hJ ≃ₜ ↥(admissibleDomain hJ) where
  toFun φ := ⟨fun a => (φ a).val, fun a => (φ a).property⟩
  invFun φ a := ⟨φ.val a, φ.property a⟩
  left_inv φ := by funext a; rfl
  right_inv φ := by apply Subtype.ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro a
    exact ((continuous_apply a).comp continuous_subtype_val).subtype_mk _

theorem cellDomain_convex (ν : Measure Torus) [IsFiniteMeasure ν] :
    Convex ℝ (cellDomain ν) := by
  intro f hf g hg a b ha hb hab
  have hfI := (Lp.memLp f).integrable le_rfl
  have hgI := (Lp.memLp g).integrable le_rfl
  have he : (a • f + b • g : Lp ℝ 1 ν) =ᵐ[ν] fun x => a * f x + b * g x := by
    filter_upwards [Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f, Lp.coeFn_smul b g]
      with x hadd hfa hgb
    simp only [hadd, hfa, hgb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · filter_upwards [hf.1, hg.1, he] with x hfx hgx hx
    rw [hx]
    constructor
    · calc
        Real.exp (-1) = a * Real.exp (-1) + b * Real.exp (-1) := by rw [← add_mul, hab, one_mul]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hfx.1 ha) (mul_le_mul_of_nonneg_left hgx.1 hb)
    · calc
        _ ≤ a * Real.exp 1 + b * Real.exp 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hfx.2 ha) (mul_le_mul_of_nonneg_left hgx.2 hb)
        _ = Real.exp 1 := by rw [← add_mul, hab, one_mul]
  · rw [integral_congr_ae he, integral_add (hfI.const_mul a) (hgI.const_mul b),
      integral_const_mul, integral_const_mul, hf.2, hg.2, mul_one, mul_one]
    exact hab

theorem admissibleDomain_convex {J : ℕ} (hJ : 0 < J) :
    Convex ℝ (admissibleDomain hJ) := by
  intro φ hφ ψ hψ a b ha hb hab c
  exact cellDomain_convex (meshCellMeasure J hJ c) (hφ c) (hψ c) ha hb hab

theorem posPart_sub_eq_zero_iff {ν : Measure Torus} (f g : Lp ℝ 1 ν) :
    Lp.posPart (f - g) = 0 ↔ ∀ᵐ x ∂ν, f x ≤ g x := by
  constructor
  · intro h
    have hp := Lp.coeFn_posPart (f - g)
    rw [h] at hp
    filter_upwards [hp, Lp.coeFn_sub f g, Lp.coeFn_zero ℝ 1 ν] with x hx hs hz
    simp only [hs, hz, Pi.sub_apply, Pi.zero_apply] at hx
    have hm := le_max_left (f x - g x) 0
    linarith
  · intro h
    apply Lp.ext
    filter_upwards [Lp.coeFn_posPart (f - g), Lp.coeFn_sub f g,
      Lp.coeFn_zero ℝ 1 ν, h] with x hp hs hz hx
    simp only [hp, hs, hz, Pi.sub_apply, Pi.zero_apply, max_eq_right (sub_nonpos.mpr hx)]

theorem isClosed_ae_le {ν : Measure Torus} (g : Lp ℝ 1 ν) :
    IsClosed {f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, f x ≤ g x} := by
  have he : {f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, f x ≤ g x} =
      {f | Lp.posPart (f - g) = 0} := by
    ext f
    exact (posPart_sub_eq_zero_iff f g).symm
  rw [he]
  exact isClosed_eq (Lp.continuous_posPart.comp (continuous_id.sub continuous_const)) continuous_const

theorem isClosed_ae_ge {ν : Measure Torus} (g : Lp ℝ 1 ν) :
    IsClosed {f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, g x ≤ f x} := by
  have he : {f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, g x ≤ f x} =
      {f | Lp.posPart (g - f) = 0} := by
    ext f
    exact (posPart_sub_eq_zero_iff g f).symm
  rw [he]
  exact isClosed_eq (Lp.continuous_posPart.comp (continuous_const.sub continuous_id)) continuous_const

theorem cellDomain_isClosed (ν : Measure Torus) [IsFiniteMeasure ν] :
    IsClosed (cellDomain ν) := by
  have hl : IsClosed {f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, Real.exp (-1) ≤ f x} := by
    have he : {f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, Real.exp (-1) ≤ f x} =
        {f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, (Lp.const 1 ν (Real.exp (-1))) x ≤ f x} := by
      ext f
      constructor <;> intro h <;>
        filter_upwards [h, Lp.coeFn_const 1 ν (Real.exp (-1))] with x hx hc <;>
        simpa only [hc, Function.const_apply] using hx
    rw [he]
    exact isClosed_ae_ge _
  have hu : IsClosed {f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, f x ≤ Real.exp 1} := by
    have he : {f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, f x ≤ Real.exp 1} =
        {f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, f x ≤ (Lp.const 1 ν (Real.exp 1)) x} := by
      ext f
      constructor <;> intro h <;>
        filter_upwards [h, Lp.coeFn_const 1 ν (Real.exp 1)] with x hx hc <;>
        simpa only [hc, Function.const_apply] using hx
    rw [he]
    exact isClosed_ae_le _
  have hm : IsClosed {f : Lp ℝ 1 ν | (∫ x, f x ∂ν) = 1} :=
    isClosed_eq continuous_integral continuous_const
  have he : cellDomain ν =
      ({f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, Real.exp (-1) ≤ f x} ∩
       {f : Lp ℝ 1 ν | ∀ᵐ x ∂ν, f x ≤ Real.exp 1}) ∩
       {f : Lp ℝ 1 ν | (∫ x, f x ∂ν) = 1} := by
    ext f
    simp only [cellDomain, mem_inter_iff, mem_ofPred_eq, Filter.eventually_and]
  rw [he]
  exact (hl.inter hu).inter hm

theorem admissibleDomain_isClosed {J : ℕ} (hJ : 0 < J) :
    IsClosed (admissibleDomain hJ) := by
  have he : admissibleDomain hJ =
      ⋂ a, (fun φ : Ambient hJ => φ a) ⁻¹' cellDomain (meshCellMeasure J hJ a) := by
    ext φ
    simp only [admissibleDomain, mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [he]
  exact isClosed_iInter fun a => (cellDomain_isClosed _).preimage (continuous_apply a)

theorem ambient_complete {J : ℕ} (hJ : 0 < J) : CompleteSpace (Ambient hJ) := inferInstance

open ReferenceSelfTerms ReferenceDensityChange ReferencePotentialBounds

/-- Conditional scalar interface: genuine cell oscillation controls the
actual normalized exponential, with its normalizer proved finite and positive. -/
theorem referenceMapValue_bounds_of_oscillation {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ) (a : MeshIndex J)
    (hosc : ∀ x ∈ closure (meshCell J hJ a), ∀ y ∈ closure (meshCell J hJ a),
      |β * averagePotential (familyMeasures φ) η x -
        β * averagePotential (familyMeasures φ) η y| ≤ 1)
    {x : Torus} (hx : x ∈ closure (meshCell J hJ a)) :
    Real.exp (-1) ≤ referenceMapValue η β φ a x ∧ referenceMapValue η β φ a x ≤ Real.exp 1 := by
  obtain ⟨hi, hz, _⟩ := cell_exponential_normalizer hJ hN (familyMeasures φ)
    (fun a => (φ a).law_le) η hβ a
  let u := β * averagePotential (familyMeasures φ) η x
  have he : ∀ᵐ y ∂meshCellMeasure J hJ a,
      Real.exp (u - 1) ≤ Real.exp (β * averagePotential (familyMeasures φ) η y) ∧
      Real.exp (β * averagePotential (familyMeasures φ) η y) ≤ Real.exp (u + 1) := by
    filter_upwards [ae_mem_meshCell J hJ a] with y hy
    have hh := abs_le.mp (hosc x hx y (subset_closure hy))
    exact ⟨Real.exp_le_exp.mpr (by dsimp [u]; linarith),
      Real.exp_le_exp.mpr (by dsimp [u]; linarith)⟩
  have hlo : Real.exp (u - 1) ≤ cellNormalizer hJ (familyMeasures φ) η β a := by
    simpa only [cellNormalizer, integral_const, probReal_univ, one_smul] using!
      integral_mono_ae (integrable_const _) hi (he.mono fun _ h => h.1)
  have hup : cellNormalizer hJ (familyMeasures φ) η β a ≤ Real.exp (u + 1) := by
    simpa only [cellNormalizer, integral_const, probReal_univ, one_smul] using!
      integral_mono_ae hi (integrable_const _) (he.mono fun _ h => h.2)
  constructor
  · apply (le_div_iff₀ hz).mpr
    calc
      _ ≤ Real.exp (-1) * Real.exp (u + 1) :=
        mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le
      _ = Real.exp u := by rw [← Real.exp_add]; congr 1; ring
  · apply (div_le_iff₀ hz).mpr
    calc
      Real.exp u = Real.exp 1 * Real.exp (u - 1) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le

/-- This remains conditional until the source oscillation estimate is
supplied; normalization itself is an unconditional proved map property. -/
theorem referenceMap_mem_of_oscillation {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (hosc : ∀ a, ∀ x ∈ closure (meshCell J hJ a), ∀ y ∈ closure (meshCell J hJ a),
      |β * averagePotential (familyMeasures φ) η x -
        β * averagePotential (familyMeasures φ) η y| ≤ 1) :
    referenceMap hN η hβ φ ∈ admissibleDomain hJ := by
  intro a
  constructor
  · filter_upwards [(referenceMapValue_memLp hN η hβ φ a).coeFn_toLp,
      ae_mem_meshCell J hJ a] with x hx hcell
    change Real.exp (-1) ≤ (referenceMapValue_memLp hN η hβ φ a).toLp _ x ∧
      (referenceMapValue_memLp hN η hβ φ a).toLp _ x ≤ Real.exp 1
    rw [hx]
    exact referenceMapValue_bounds_of_oscillation hN η hβ φ a (hosc a) (subset_closure hcell)
  · change (∫ x, (referenceMapValue_memLp hN η hβ φ a).toLp _ x ∂meshCellMeasure J hJ a) = 1
    rw [integral_congr_ae (referenceMapValue_memLp hN η hβ φ a).coeFn_toLp]
    exact referenceMapValue_integral hN η hβ φ a

/-- The concrete continuous self-map of the ambient subtype, conditional
only here on the separately required actual cell oscillation estimate. -/
def mapOnDomain {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β)
    (hosc : ∀ φ : DensityFamily hJ, ∀ a, ∀ x ∈ closure (meshCell J hJ a),
      ∀ y ∈ closure (meshCell J hJ a),
      |β * averagePotential (familyMeasures φ) η x -
        β * averagePotential (familyMeasures φ) η y| ≤ 1) :
    ↥(admissibleDomain hJ) → ↥(admissibleDomain hJ) := fun φ =>
  ⟨referenceMap hN η hβ ((familyHomeomorph hJ).symm φ),
    referenceMap_mem_of_oscillation hN η hβ _ (hosc _)⟩

theorem continuous_mapOnDomain {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β)
    (hosc : ∀ φ : DensityFamily hJ, ∀ a, ∀ x ∈ closure (meshCell J hJ a),
      ∀ y ∈ closure (meshCell J hJ a),
      |β * averagePotential (familyMeasures φ) η x -
        β * averagePotential (familyMeasures φ) η y| ≤ 1) :
    Continuous (mapOnDomain hN η hβ hosc) :=
  ((continuous_referenceMap hN η hβ).comp (familyHomeomorph hJ).symm.continuous).subtype_mk _

end PeriodicAttractiveLogGas.ReferenceDensityDomain
