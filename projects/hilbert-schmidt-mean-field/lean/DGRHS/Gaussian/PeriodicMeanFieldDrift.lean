import DGRHS.Gaussian.PeriodicBackwardInterface
import DGRHS.Commutator.SourceBoundedC2Spatial

/-!
Packet P11e, unit 1 (part 1): the static mean-field test drift on the torus and its Lipschitz
dependence on the `C²` seminorm of the test.

Torus form of `sourceRieszStaticMeanTestDrift` / `sourceLogStaticMeanTestDrift` for an abstract periodic
force (`PeriodicForceData`): for a torus test `ψ` (differentiated through its lift) and a background
density `ρ`,
`periodicStaticMeanTestDrift F β ρ ψ = β⁻¹ ∫ Δψ dμ - (1/2) ∬ ⟪F(x-y), ∇ψ(x) - ∇ψ(y)⟫ dμ dμ`
(the symmetrized weak identity of TeX 3897-3904).  The main estimate is that this drift depends
Lipschitz-continuously on the sup norm of the Hessian of the test, uniformly in the probability density
`ρ ≤ M`; it is the torus analogue of `sourceLogStaticMeanTestDrift_sub_le`.  Topological helpers
(continuity of a function of the lift) are also collected here.
-/

noncomputable section
open MeasureTheory Laplacian Set Filter
open scoped NNReal RealInnerProductSpace ENNReal Topology Classical
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-! ### The lift is an open quotient map -/

lemma isOpenQuotientMap_periodicLift : IsOpenQuotientMap (periodicLift : E → PeriodicTorus ι) := by
  have h1 : IsOpenQuotientMap (Pi.map (fun (_ : ι) (x : ℝ) => (x : UnitAddCircle))) :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  exact h1.comp (EuclideanSpace.equiv ι ℝ).toHomeomorph.isOpenQuotientMap

/-- A torus map whose composite with the lift is continuous is continuous. -/
lemma continuous_of_continuous_periodicLift {X : Type*} [TopologicalSpace X]
    {G : PeriodicTorus ι → X} (h : Continuous (fun x : E => G (periodicLift x))) : Continuous G :=
  isOpenQuotientMap_periodicLift.continuous_comp_iff.mp h

/-- Parametrized version over `ℝ × 𝕋^d`. -/
lemma continuous_prod_of_continuous_periodicLift {X : Type*} [TopologicalSpace X]
    {G : ℝ × PeriodicTorus ι → X}
    (h : Continuous (fun p : ℝ × E => G (p.1, periodicLift p.2))) : Continuous G := by
  have hq : IsOpenQuotientMap (Prod.map (id : ℝ → ℝ) (periodicLift : E → PeriodicTorus ι)) :=
    IsOpenQuotientMap.id.prodMap isOpenQuotientMap_periodicLift
  exact hq.continuous_comp_iff.mp h


/-! ### Boundedness of periodic functions and their derivatives -/

/-- A continuous lattice-periodic function on `ℝ^d` is bounded. -/
lemma periodic_continuous_bounded {g : E → ℝ} (hg : Continuous g) (hper : IsLatticePeriodic g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |g x| ≤ B := by
  let G : PeriodicTorus ι → ℝ := fun z => g (periodicCenteredLift z)
  have hGg : ∀ x, G (periodicLift x) = g x := by
    intro x
    obtain ⟨m, hm⟩ := periodicCenteredLift_periodicLift (ι := ι) x
    simp only [G, hm]
    exact hper x m
  have hGc : Continuous G := by
    apply continuous_of_continuous_periodicLift
    have : (fun x : E => G (periodicLift x)) = g := funext hGg
    rw [this]; exact hg
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hGc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  rw [← hGg x]
  exact (hB _ (mem_univ _)).trans (le_max_left _ _)

lemma exists_value_bound {ψ : PeriodicTorus ι → ℝ} (hψ : Continuous (periodicLiftFn ψ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |periodicLiftFn ψ x| ≤ C :=
  periodic_continuous_bounded hψ (isLatticePeriodic_periodicLiftFn ψ)

lemma exists_hessian_bound {ψ : PeriodicTorus ι → ℝ} (hψ : ContDiff ℝ 2 (periodicLiftFn ψ)) :
    ∃ K : ℝ≥0, ∀ x, ‖iteratedFDeriv ℝ 2 (periodicLiftFn ψ) x‖ ≤ K := by
  have hc : Continuous (fun x => ‖iteratedFDeriv ℝ 2 (periodicLiftFn ψ) x‖) :=
    (hψ.continuous_iteratedFDeriv le_rfl).norm
  have hp : IsLatticePeriodic (fun x : E => ‖iteratedFDeriv ℝ 2 (periodicLiftFn ψ) x‖) := fun z m => by
    simp only [(isLatticePeriodic_periodicLiftFn ψ).iteratedFDeriv_add]
  obtain ⟨B, hB0, hB⟩ := periodic_continuous_bounded hc hp
  exact ⟨⟨B, hB0⟩, fun x => (le_abs_self _).trans (hB x)⟩

lemma periodic_lap_integrable {ψ : PeriodicTorus ι → ℝ} (hψ : ContDiff ℝ 2 (periodicLiftFn ψ))
    (μ : Measure (PeriodicTorus ι)) [IsFiniteMeasure μ] : Integrable (periodicLap ψ) μ := by
  obtain ⟨K, hK⟩ := exists_hessian_bound hψ
  refine (integrable_const ((Fintype.card ι : ℝ) * K)).mono' (measurable_periodicLap hψ).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  exact source_laplacian_bound_of_hessian (EuclideanSpace.basisFun ι ℝ) _ K hK _

/-! ### Linearity in the test -/

lemma periodicGrad_sub {φ ψ : PeriodicTorus ι → ℝ} (hφ : ContDiff ℝ 1 (periodicLiftFn φ))
    (hψ : ContDiff ℝ 1 (periodicLiftFn ψ)) (z : PeriodicTorus ι) :
    periodicGrad (fun w => φ w - ψ w) z = periodicGrad φ z - periodicGrad ψ z := by
  unfold periodicGrad
  have h : periodicLiftFn (fun w => φ w - ψ w) =
      fun x => periodicLiftFn φ x - periodicLiftFn ψ x := rfl
  rw [h]
  simp only [gradient, fderiv_fun_sub (hφ.differentiable (by norm_num) _) (hψ.differentiable (by norm_num) _), map_sub]

lemma periodicLap_sub {φ ψ : PeriodicTorus ι → ℝ} (hφ : ContDiff ℝ 2 (periodicLiftFn φ))
    (hψ : ContDiff ℝ 2 (periodicLiftFn ψ)) (z : PeriodicTorus ι) :
    periodicLap (fun w => φ w - ψ w) z = periodicLap φ z - periodicLap ψ z := by
  unfold periodicLap
  have h : periodicLiftFn (fun w => φ w - ψ w) =
      fun x => periodicLiftFn φ x - periodicLiftFn ψ x := rfl
  rw [h]
  exact (hφ.contDiffAt.laplacian_sub hψ.contDiffAt)

lemma periodicForcePair_sub (F : PeriodicTorus ι → E) (v w : PeriodicTorus ι → E)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicForcePair F v p - periodicForcePair F w p =
      periodicForcePair F (fun z => v z - w z) p := by
  unfold periodicForcePair
  have he : v p.1 - v p.2 - (w p.1 - w p.2) = (v p.1 - w p.1) - (v p.2 - w p.2) := by abel
  rw [← inner_sub_right, he]

/-! ### The static mean-field drift -/

/-- The static mean-field test drift of a torus test `ψ` against the density `ρ`
(the symmetrized right-hand side of `eq:dynamicMeanFieldWeakIdentity`, TeX 3897-3904). -/
def periodicStaticMeanTestDrift (F : PeriodicTorus ι → E) (β : ℝ) (ρ : PeriodicTorus ι → ℝ)
    (ψ : PeriodicTorus ι → ℝ) : ℝ :=
  β⁻¹ * (∫ z, periodicLap ψ z ∂periodicCappedDensityMeasure ρ) -
    (1 / 2 : ℝ) * ∫ p, periodicForcePair F (periodicGrad ψ) p
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)

/-- Pair integrals are bounded linearly by the Lipschitz constant of the velocity field. -/
lemma PeriodicForceData.pair_integral_bound (D : PeriodicForceData ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : PeriodicTorus ι → E} {L : ℝ≥0}, LipschitzWith L v →
      ∀ (ρ : PeriodicTorus ι → ℝ) (M : ℝ), 0 ≤ M → (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∀ [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      Integrable (periodicForcePair D.F v)
        ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ∧
      |∫ p, periodicForcePair D.F v p
        ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)| ≤ M * C * L := by
  obtain ⟨C, hC, h⟩ := D.pair_density_integrable 1
  refine ⟨C, hC, ?_⟩
  intro v L hv ρ M hM hρ hprob
  by_cases hL : L = 0
  · subst hL
    have h0 : ∀ x y, v x = v y := fun x y => by
      have := hv.dist_le_mul x y
      simp only [NNReal.coe_zero, zero_mul] at this
      exact dist_le_zero.mp this
    have hz : periodicForcePair D.F v = fun _ => 0 := by
      funext p
      simp [periodicForcePair, h0 p.1 p.2]
    rw [hz]
    exact ⟨integrable_zero _ _ _, by simp⟩
  · have hLpos : 0 < (L : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hL)
    set w : PeriodicTorus ι → E := fun x => (L : ℝ)⁻¹ • v x with hwdef
    have hw : LipschitzWith 1 w := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      have h1 := hv.dist_le_mul x y
      rw [hwdef]
      simp only [dist_smul₀, norm_inv, Real.norm_eq_abs, abs_of_pos hLpos, NNReal.coe_one, one_mul]
      calc (L : ℝ)⁻¹ * dist (v x) (v y) ≤ (L : ℝ)⁻¹ * ((L : ℝ) * dist x y) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hLpos.le)
        _ = dist x y := by field_simp
    have hrel : periodicForcePair D.F v = fun p => (L : ℝ) * periodicForcePair D.F w p := by
      funext p
      simp only [periodicForcePair, hwdef, ← smul_sub, inner_smul_right]
      field_simp
    obtain ⟨hi, hb⟩ := h hw ρ M hM hρ
    rw [hrel]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul, abs_mul, abs_of_pos hLpos]
    calc (L : ℝ) * |∫ p, periodicForcePair D.F w p
          ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)|
        ≤ (L : ℝ) * (M * C) := mul_le_mul_of_nonneg_left hb hLpos.le
      _ = M * C * L := by ring

/-- The static drift depends Lipschitz-continuously on the sup norm of the Hessian of the test,
uniformly in the probability density with `ρ ≤ M`. -/
theorem periodicStaticMeanTestDrift_sub_le (D : PeriodicForceData ι) (β M : ℝ) (hM : 0 ≤ M) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (ρ : PeriodicTorus ι → ℝ), (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      IsProbabilityMeasure (periodicCappedDensityMeasure ρ) →
      ∀ (φ ψ : PeriodicTorus ι → ℝ), ContDiff ℝ 2 (periodicLiftFn φ) →
        ContDiff ℝ 2 (periodicLiftFn ψ) → ∀ δ : ℝ, 0 ≤ δ →
        (∀ x, ‖iteratedFDeriv ℝ 2 (periodicLiftFn φ) x - iteratedFDeriv ℝ 2 (periodicLiftFn ψ) x‖ ≤ δ) →
        |periodicStaticMeanTestDrift D.F β ρ φ - periodicStaticMeanTestDrift D.F β ρ ψ| ≤ Cs * δ := by
  obtain ⟨C, hC, hpair⟩ := D.pair_integral_bound
  have hd : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  refine ⟨|β⁻¹| * (Fintype.card ι : ℝ) + (1 / 2 : ℝ) * (M * C * (Fintype.card ι : ℝ)),
    by positivity, ?_⟩
  intro ρ hρ hprob φ ψ hφ hψ δ hδ hH
  set μ := periodicCappedDensityMeasure ρ with hμ
  obtain ⟨Kφ, hKφ⟩ := exists_hessian_bound hφ
  obtain ⟨Kψ, hKψ⟩ := exists_hessian_bound hψ
  have ilφ := periodic_lap_integrable hφ μ
  have ilψ := periodic_lap_integrable hψ μ
  have ipφ := (hpair (periodicGrad_lipschitz hφ Kφ hKφ) ρ M hM hρ).1
  have ipψ := (hpair (periodicGrad_lipschitz hψ Kψ hKψ) ρ M hM hρ).1
  let q : PeriodicTorus ι → ℝ := fun w => φ w - ψ w
  have hq : ContDiff ℝ 2 (periodicLiftFn q) := hφ.sub hψ
  have hqH : ∀ x, ‖iteratedFDeriv ℝ 2 (periodicLiftFn q) x‖ ≤ δ := by
    intro x
    have he : iteratedFDeriv ℝ 2 (periodicLiftFn q) x =
        iteratedFDeriv ℝ 2 (periodicLiftFn φ) x - iteratedFDeriv ℝ 2 (periodicLiftFn ψ) x :=
      iteratedFDeriv_sub_apply hφ.contDiffAt hψ.contDiffAt
    rw [he]; exact hH x
  have hLq : ∀ z, |periodicLap q z| ≤ (Fintype.card ι : ℝ) * δ := fun z =>
    source_laplacian_bound_of_hessian (EuclideanSpace.basisFun ι ℝ) _ δ hqH _
  have hIL : |(∫ z, periodicLap φ z ∂μ) - ∫ z, periodicLap ψ z ∂μ| ≤ (Fintype.card ι : ℝ) * δ := by
    rw [← integral_sub ilφ ilψ]
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun z => periodicLap φ z - periodicLap ψ z) (C := (Fintype.card ι : ℝ) * δ)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, ← periodicLap_sub hφ hψ z]; exact hLq z)
    simpa [Real.norm_eq_abs] using h
  have hgq : periodicGrad q = fun z => periodicGrad φ z - periodicGrad ψ z :=
    funext fun z => periodicGrad_sub (hφ.of_le (by norm_num)) (hψ.of_le (by norm_num)) z
  have hker : ∀ p, periodicForcePair D.F (periodicGrad φ) p - periodicForcePair D.F (periodicGrad ψ) p =
      periodicForcePair D.F (periodicGrad q) p := fun p => by
    rw [periodicForcePair_sub, hgq]
  have hIK : |(∫ p, periodicForcePair D.F (periodicGrad φ) p ∂μ.prod μ) -
      ∫ p, periodicForcePair D.F (periodicGrad ψ) p ∂μ.prod μ| ≤ M * C * ((δ) * (Fintype.card ι : ℝ)) := by
    rw [← integral_sub ipφ ipψ]
    let Kδ : ℝ≥0 := ⟨δ, hδ⟩
    have hLip := periodicGrad_lipschitz hq Kδ hqH
    have h := (hpair hLip ρ M hM hρ).2
    have hfun : (fun p => periodicForcePair D.F (periodicGrad φ) p -
        periodicForcePair D.F (periodicGrad ψ) p) = periodicForcePair D.F (periodicGrad q) :=
      funext hker
    rw [hfun]
    have hc : (((Kδ * (Fintype.card ι : ℝ≥0) : ℝ≥0)) : ℝ) =
        δ * (Fintype.card ι : ℝ) := by
      rw [NNReal.coe_mul, NNReal.coe_natCast]; rfl
    rw [hc] at h
    exact h
  unfold periodicStaticMeanTestDrift
  rw [← hμ]
  have hsplit :
      β⁻¹ * (∫ z, periodicLap φ z ∂μ) - (1 / 2 : ℝ) * (∫ p, periodicForcePair D.F (periodicGrad φ) p ∂μ.prod μ) -
        (β⁻¹ * (∫ z, periodicLap ψ z ∂μ) - (1 / 2 : ℝ) * (∫ p, periodicForcePair D.F (periodicGrad ψ) p ∂μ.prod μ)) =
      β⁻¹ * ((∫ z, periodicLap φ z ∂μ) - ∫ z, periodicLap ψ z ∂μ) -
        (1 / 2 : ℝ) * ((∫ p, periodicForcePair D.F (periodicGrad φ) p ∂μ.prod μ) -
          ∫ p, periodicForcePair D.F (periodicGrad ψ) p ∂μ.prod μ) := by ring
  rw [hsplit]
  calc _ ≤ |β⁻¹ * ((∫ z, periodicLap φ z ∂μ) - ∫ z, periodicLap ψ z ∂μ)| +
        |(1 / 2 : ℝ) * ((∫ p, periodicForcePair D.F (periodicGrad φ) p ∂μ.prod μ) -
          ∫ p, periodicForcePair D.F (periodicGrad ψ) p ∂μ.prod μ)| := abs_sub _ _
    _ = |β⁻¹| * |(∫ z, periodicLap φ z ∂μ) - ∫ z, periodicLap ψ z ∂μ| +
        (1 / 2 : ℝ) * |(∫ p, periodicForcePair D.F (periodicGrad φ) p ∂μ.prod μ) -
          ∫ p, periodicForcePair D.F (periodicGrad ψ) p ∂μ.prod μ| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ |β⁻¹| * ((Fintype.card ι : ℝ) * δ) + (1 / 2 : ℝ) * (M * C * (δ * (Fintype.card ι : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left hIL (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hIK (by norm_num))
    _ = _ := by ring

end DGRHS.Periodic
