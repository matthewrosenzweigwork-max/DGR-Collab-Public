import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod


/-!
# FIN010: the exact finite-rank Hubbard identity

Let `D` be positive definite, `h ∈ ℝ^k`, `m` a nonzero finite measure on `M`, `U : M → ℝ`
measurable and bounded below, and `φ : M → ℝ^k` measurable and bounded.  With
`S(x) = ∑ φ(xᵢ)` the particle law is `P_N ∝ exp[-∑U(xᵢ) + h·S + SᵀDS/(2N)] dm^{⊗N}`.  Put
`ζ(w) = ∫ exp(w·φ - U) dm` and `ψ(w) = ½ (w-h)ᵀ D⁻¹ (w-h) - log ζ(w)`.

The joint density of `(w, x)` against `Leb ⊗ m^{⊗N}` is
`(N/2π)^{k/2} det(D)^{-1/2} exp(-(N/2)(w-h)ᵀD⁻¹(w-h)) exp(w·S(x) - ∑U(xᵢ))`
(`hubbardDensity`; the determinant and `(N/2π)^{k/2}` are both kept).  Integrating `w` out
(Gaussian MGF after completing the square) gives `P_N`; integrating `x` out gives
`e^{-Nψ(w)}`, whence the two marginals, and the conditional law is `q_w^{⊗N}` with
`q_w = exp(w·φ - U)/ζ(w) dm`.

The identity is the single theorem `DGPS.FiniteN.exact_finite_rank_hubbard_identity`.

## Design choices (R5 notes)

* Placement: this module is `DGPS/FiniteN/Tools/Hubbard.lean` rather than `Tools.lean`; the
  output interface name lives in `DGPS.FiniteN`, the helper declarations in
  `DGPS.FiniteN.Tools.Hubbard`.
* Laws are `Measure`s on `(Fin k → ℝ) × (Fin N → M)` (resp. its factors); normalizations are
  `ℝ≥0∞`-valued inverse masses, whose finiteness and positivity are part of the conclusion
  (`auxMass_ne_zero`, `auxMass_ne_top`, via a compactness bound on `S`).
* `η_N` is `auxLaw` with density `exp(-Nψ)` w.r.t. Lebesgue measure; the Gaussian normalizer
  relation `hubbardMass = ofReal (gaussNorm D N) * auxMass` is stated explicitly.
* The conditional law is stated as a disintegration: for every measurable `s`,
  `joint s = ∫⁻ w, q_w^{⊗N}(slice_w s) ∂η_N`.  The `fst`/`snd` marginals are stated separately.
* Hypotheses: `m` finite nonzero, `U` measurable and bounded below, `φ` measurable with a sup-norm
  bound (`HubbardHyp`); `D.PosDef`.  Nothing is weakened relative to the frozen statement.
-/

open MeasureTheory Matrix
open scoped ENNReal
open scoped MatrixOrder

namespace DGPS.FiniteN.Tools.Hubbard

variable {k : ℕ}

theorem gaussian_integral_posDef (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : Q.PosDef) :
    ∫ v : Fin k → ℝ, Real.exp (-(1/2) * (v ⬝ᵥ Q *ᵥ v)) =
      (2 * Real.pi) ^ ((k : ℝ) / 2) * Q.det ^ (-(1/2 : ℝ)) := by
  classical
  set R : Matrix (Fin k) (Fin k) ℝ := CFC.sqrt Q with hRdef
  have hRsa : R.PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hRR : R * R = Q := CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg
  have hdetQ : 0 < Q.det := hQ.det_pos
  have hdetR : R.det = Real.sqrt Q.det := by
    have := hQ.posSemidef.det_sqrt
    simpa [hRdef] using this
  have hdetRpos : 0 < R.det := by rw [hdetR]; exact Real.sqrt_pos.2 hdetQ
  have hRT : Rᵀ = R := by
    have := hRsa.isHermitian.eq
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hquad : ∀ v : Fin k → ℝ, v ⬝ᵥ Q *ᵥ v = (R *ᵥ v) ⬝ᵥ (R *ᵥ v) := by
    intro v
    rw [← hRR, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hRT]
  let T : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ) := Matrix.toLin' R
  have hT : LinearMap.det T = R.det := LinearMap.det_toLin' R
  have hTne : LinearMap.det T ≠ 0 := by rw [hT]; exact hdetRpos.ne'
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi (ι := Fin k) hTne
  set f : (Fin k → ℝ) → ℝ := fun u => Real.exp (-(1/2) * (u ⬝ᵥ u)) with hf
  have hfm : Continuous f := by
    simp only [hf, dotProduct]; fun_prop
  have h1 : ∫ v : Fin k → ℝ, Real.exp (-(1/2) * (v ⬝ᵥ Q *ᵥ v)) = ∫ v, f (T v) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp [hf, T, hquad]
  have h2 : ∫ v, f (T v) = ∫ u, f u ∂(Measure.map T volume) :=
    (integral_map (by fun_prop) hfm.aestronglyMeasurable).symm
  have h3 : ∫ u, f u = ∏ _i : Fin k, Real.sqrt (2 * Real.pi) := by
    have : ∀ u : Fin k → ℝ, f u = ∏ i, Real.exp (-(1/2) * (u i)^2) := by
      intro u
      simp only [hf, dotProduct, ← Real.exp_sum, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => by ring
    simp_rw [this]
    rw [show (volume : Measure (Fin k → ℝ)) = Measure.pi (fun _ => volume) from rfl,
      integral_fintype_prod_eq_prod (f := fun _ t => Real.exp (-(1/2) * t^2))]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := integral_gaussian (1/2 : ℝ)
    simp only [neg_mul] at this ⊢
    rw [this]
    congr 1
    field_simp
  rw [h1, h2, hmap, integral_smul_measure, h3]
  rw [hT, hdetR]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (by positivity), smul_eq_mul]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    Real.rpow_neg (by positivity)]
  rw [mul_comm]
  congr 2
  ring


/-! ### Quadratic forms and the Hubbard Gaussian -/

/-- The quadratic form `v ↦ vᵀ A v`. -/
def quadForm (A : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) : ℝ := v ⬝ᵥ A *ᵥ v

/-- The Gaussian normalizer `(N/2π)^{k/2} det(D)^{-1/2}` (the determinant and `(N/2π)^{k/2}`
are both kept). -/
noncomputable def gaussNorm (D : Matrix (Fin k) (Fin k) ℝ) (N : ℕ+) : ℝ :=
  ((N : ℝ) / (2 * Real.pi)) ^ ((k : ℝ) / 2) * D.det ^ (-(1 / 2 : ℝ))

/-- The unnormalized Gaussian weight `exp(-(N/2)(w-h)ᵀ D⁻¹ (w-h))`. -/
noncomputable def gaussWeight (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (N : ℕ+)
    (w : Fin k → ℝ) : ℝ :=
  Real.exp (-((N : ℝ) / 2) * quadForm D⁻¹ (w - h))

theorem gaussNorm_pos {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (N : ℕ+) :
    0 < gaussNorm D N := by
  unfold gaussNorm
  have := hD.det_pos
  positivity

theorem quadForm_shift {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (N : ℕ+) (h s w : Fin k → ℝ) :
    -(((N : ℝ)) / 2) * quadForm D⁻¹ (w - h) + w ⬝ᵥ s =
      -(((N : ℝ)) / 2) * quadForm D⁻¹ (w - (h + ((N : ℝ)⁻¹ • (D *ᵥ s)))) +
        (h ⬝ᵥ s + (s ⬝ᵥ D *ᵥ s) / (2 * (N : ℝ))) := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hDu : IsUnit D := hD.isUnit
  have hDi : D⁻¹ *ᵥ (D *ᵥ s) = s := by
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hDu), one_mulVec]
  have hsym : D⁻¹ᵀ = D⁻¹ := by
    have := hD.inv.isHermitian.eq
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hsymD : Dᵀ = D := by
    have := hD.isHermitian.eq
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  set t : Fin k → ℝ := (N : ℝ)⁻¹ • (D *ᵥ s) with ht
  have hPt : D⁻¹ *ᵥ t = (N : ℝ)⁻¹ • s := by rw [ht, mulVec_smul, hDi]
  have hcomm : ∀ a b : Fin k → ℝ, a ⬝ᵥ D⁻¹ *ᵥ b = b ⬝ᵥ D⁻¹ *ᵥ a := by
    intro a b
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  have hDs : s ⬝ᵥ D *ᵥ s = s ⬝ᵥ D *ᵥ s := rfl
  have e1 : quadForm D⁻¹ (w - (h + t)) =
      quadForm D⁻¹ (w - h) - 2 * ((N : ℝ)⁻¹ * ((w - h) ⬝ᵥ s)) + (N : ℝ)⁻¹ * (t ⬝ᵥ s) := by
    have hc : t ⬝ᵥ D⁻¹ *ᵥ (w - h) = (N : ℝ)⁻¹ * ((w - h) ⬝ᵥ s) := by
      rw [hcomm, hPt, dotProduct_smul, smul_eq_mul]
    have hc2 : (w - h) ⬝ᵥ D⁻¹ *ᵥ t = (N : ℝ)⁻¹ * ((w - h) ⬝ᵥ s) := by
      rw [hPt, dotProduct_smul, smul_eq_mul]
    have hc3 : t ⬝ᵥ D⁻¹ *ᵥ t = (N : ℝ)⁻¹ * (t ⬝ᵥ s) := by
      rw [hPt, dotProduct_smul, smul_eq_mul]
    have : w - (h + t) = (w - h) - t := by abel
    unfold quadForm
    rw [this]
    generalize w - h = u at hc hc2 ⊢
    rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hc, hc2, hc3]
    ring
  have e2 : t ⬝ᵥ s = (N : ℝ)⁻¹ * (s ⬝ᵥ D *ᵥ s) := by
    rw [ht, smul_dotProduct, smul_eq_mul, dotProduct_comm]
  rw [e1, e2]
  have e3 : (w - h) ⬝ᵥ s = w ⬝ᵥ s - h ⬝ᵥ s := sub_dotProduct _ _ _
  rw [e3]
  field_simp
  ring


theorem integral_gaussWeight {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (N : ℕ+)
    (h : Fin k → ℝ) :
    ∫ w, gaussWeight D h N w = (gaussNorm D N)⁻¹ := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hQ : ((N : ℝ) • D⁻¹).PosDef := hD.inv.smul hN
  have h1 : ∫ w, gaussWeight D h N w =
      ∫ v : Fin k → ℝ, Real.exp (-(1/2) * (v ⬝ᵥ ((N : ℝ) • D⁻¹) *ᵥ v)) := by
    rw [← integral_sub_right_eq_self (fun v : Fin k → ℝ => Real.exp (-(1/2) * (v ⬝ᵥ ((N : ℝ) • D⁻¹) *ᵥ v))) h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [gaussWeight, quadForm, smul_mulVec, dotProduct_smul, smul_eq_mul]
    congr 1; ring
  rw [h1, gaussian_integral_posDef _ hQ]
  have hdet : ((N : ℝ) • D⁻¹).det = (N : ℝ) ^ k * (D.det)⁻¹ := by
    rw [det_smul, Fintype.card_fin, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hdp : 0 < D.det := hD.det_pos
  unfold gaussNorm
  have hpi : 0 < 2 * Real.pi := by positivity
  have eN : ((N : ℝ) ^ k) ^ (-(1 / 2 : ℝ)) = ((N : ℝ) ^ ((k : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_neg hN.le]
    congr 1; ring
  have eD : (D.det⁻¹) ^ (-(1 / 2 : ℝ)) = D.det ^ (1 / 2 : ℝ) := by
    rw [Real.inv_rpow hdp.le, Real.rpow_neg hdp.le, inv_inv]
  have eD' : D.det ^ (-(1 / 2 : ℝ)) = (D.det ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hdp.le _
  rw [hdet, Real.mul_rpow (x := (N : ℝ) ^ k) (by positivity) (by positivity), eN, eD, Real.div_rpow hN.le hpi.le, eD']
  have hA : 0 < (N : ℝ) ^ ((k : ℝ) / 2) := by positivity
  have hB : 0 < (2 * Real.pi) ^ ((k : ℝ) / 2) := by positivity
  have hC : 0 < D.det ^ (1 / 2 : ℝ) := by positivity
  field_simp


theorem integrable_gaussWeight {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (N : ℕ+)
    (h : Fin k → ℝ) : Integrable (gaussWeight D h N) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_gaussWeight hD]
  exact (inv_pos.2 (gaussNorm_pos hD N)).ne'

theorem gaussWeight_mul_exp {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (N : ℕ+)
    (h s w : Fin k → ℝ) :
    gaussWeight D h N w * Real.exp (w ⬝ᵥ s) =
      Real.exp (h ⬝ᵥ s + (s ⬝ᵥ D *ᵥ s) / (2 * (N : ℝ))) *
        gaussWeight D (h + ((N : ℝ)⁻¹ • (D *ᵥ s))) N w := by
  unfold gaussWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [add_comm (h ⬝ᵥ s + _), ← add_assoc]
  have := quadForm_shift hD N h s w
  linarith

theorem integrable_gaussWeight_mul_exp {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (N : ℕ+)
    (h s : Fin k → ℝ) :
    Integrable fun w => gaussWeight D h N w * Real.exp (w ⬝ᵥ s) := by
  simp_rw [gaussWeight_mul_exp hD]
  exact (integrable_gaussWeight hD N _).const_mul _

theorem integral_gaussWeight_mul_exp {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (N : ℕ+)
    (h s : Fin k → ℝ) :
    ∫ w, gaussNorm D N * (gaussWeight D h N w * Real.exp (w ⬝ᵥ s)) =
      Real.exp (h ⬝ᵥ s + (s ⬝ᵥ D *ᵥ s) / (2 * (N : ℝ))) := by
  simp_rw [gaussWeight_mul_exp hD]
  rw [integral_const_mul]
  rw [integral_const_mul, integral_gaussWeight hD]
  have := (gaussNorm_pos hD N).ne'
  field_simp


/-! ### Product measures with densities -/

section Pi

variable {M : Type*} [MeasurableSpace M]

theorem lintegral_pi_prod_ofReal {ι : Type*} [Fintype ι] {μ : Measure M} [IsFiniteMeasure μ]
    (f : ι → M → ℝ) (hf : ∀ i, Integrable (f i) μ) (hf0 : ∀ i x, 0 ≤ f i x) :
    ∫⁻ x : ι → M, ∏ i, ENNReal.ofReal (f i (x i)) ∂(Measure.pi fun _ : ι => μ) =
      ∏ i, ∫⁻ y, ENNReal.ofReal (f i y) ∂μ := by
  have hint : Integrable (fun x : ι → M => ∏ i, f i (x i)) (Measure.pi fun _ : ι => μ) :=
    Integrable.fintype_prod (μ := fun _ : ι => μ) hf
  calc ∫⁻ x : ι → M, ∏ i, ENNReal.ofReal (f i (x i)) ∂(Measure.pi fun _ : ι => μ)
      = ∫⁻ x : ι → M, ENNReal.ofReal (∏ i, f i (x i)) ∂(Measure.pi fun _ : ι => μ) := by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hf0 i (x i))]
    _ = ENNReal.ofReal (∫ x : ι → M, ∏ i, f i (x i) ∂(Measure.pi fun _ : ι => μ)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => hf0 i (x i))).symm
    _ = ∏ i, ∫⁻ y, ENNReal.ofReal (f i y) ∂μ := by
        rw [integral_fintype_prod_eq_prod (μ := fun _ : ι => μ) (f := fun i y => f i y),
          ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hf0 i))]
        refine Finset.prod_congr rfl fun i _ => ?_
        exact ofReal_integral_eq_lintegral_ofReal (hf i) (Filter.Eventually.of_forall (hf0 i))

theorem pi_withDensity_ofReal {m : Measure M} [IsFiniteMeasure m] (g : M → ℝ)
    (hg : Integrable g m) (hg0 : ∀ x, 0 ≤ g x) (n : ℕ) :
    Measure.pi (fun _ : Fin n => m.withDensity fun x => ENNReal.ofReal (g x)) =
      (Measure.pi fun _ : Fin n => m).withDensity
        fun x => ENNReal.ofReal (∏ i, g (x i)) := by
  have hfin : IsFiniteMeasure (m.withDensity fun x => ENNReal.ofReal (g x)) :=
    isFiniteMeasure_withDensity_ofReal hg.hasFiniteIntegral
  refine Measure.pi_eq (μ := fun _ : Fin n => m.withDensity fun x => ENNReal.ofReal (g x)) ?_
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hpt : ∀ x : Fin n → M,
      (Set.pi Set.univ s).indicator (fun x => ENNReal.ofReal (∏ i, g (x i))) x =
        ∏ i, ENNReal.ofReal ((s i).indicator g (x i)) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx, ENNReal.ofReal_prod_of_nonneg (fun i _ => hg0 _)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [Set.indicator_of_notMem hi]; simp
  simp_rw [hpt]
  rw [lintegral_pi_prod_ofReal (μ := m) (fun i => (s i).indicator g)
    (fun i => hg.indicator (hs i)) (fun i x => Set.indicator_nonneg (fun y _ => hg0 y) x)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ s i
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]

end Pi


/-! ### Setup: the auxiliary model -/

section Setup

variable {M : Type*} [MeasurableSpace M]

/-- Standing hypotheses on the single-site data: a nonzero finite reference measure `m` (given
as an instance argument elsewhere), a measurable potential `U` bounded below and a measurable
bounded `ℝ^k`-valued field `φ` (sup-norm bound). -/
structure HubbardHyp (m : Measure M) (U : M → ℝ) (φ : M → Fin k → ℝ) : Prop where
  m_ne_zero : m ≠ 0
  U_meas : Measurable U
  U_lower : ∃ c : ℝ, ∀ x, c ≤ U x
  φ_meas : Measurable φ
  φ_bound : ∃ L : ℝ, ∀ x, ‖φ x‖ ≤ L

variable (U : M → ℝ) (φ : M → Fin k → ℝ)

/-- The single-site tilt `exp(w·φ(x) - U(x))`. -/
noncomputable def expTerm (w : Fin k → ℝ) (x : M) : ℝ := Real.exp (w ⬝ᵥ φ x - U x)

/-- The auxiliary partition function `ζ(w) = ∫ exp(w·φ - U) dm`. -/
noncomputable def auxPartition (m : Measure M) (w : Fin k → ℝ) : ℝ :=
  ∫ x, expTerm U φ w x ∂m

/-- The auxiliary potential `ψ(w) = ½ (w-h)ᵀ D⁻¹ (w-h) - log ∫ exp(w·φ - U) dm`. -/
noncomputable def auxPotential (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (m : Measure M)
    (w : Fin k → ℝ) : ℝ :=
  (1 / 2) * quadForm D⁻¹ (w - h) - Real.log (auxPartition U φ m w)

/-- The total field `S(x) = ∑ᵢ φ(xᵢ)`. -/
noncomputable def fieldSum {N : ℕ+} (x : Fin N → M) : Fin k → ℝ := ∑ i, φ (x i)

/-- The (unnormalized) particle weight `exp[-∑ U(xᵢ) + h·S + SᵀDS/(2N)]`. -/
noncomputable def particleWeight (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (N : ℕ+)
    (x : Fin N → M) : ℝ :=
  Real.exp (-(∑ i, U (x i)) + h ⬝ᵥ fieldSum φ x +
    (fieldSum φ x ⬝ᵥ D *ᵥ fieldSum φ x) / (2 * (N : ℝ)))

variable {U φ}

section Hyp

variable {m : Measure M} (hyp : HubbardHyp m U φ)
include hyp

theorem measurable_dot_field : Measurable fun p : (Fin k → ℝ) × M => p.1 ⬝ᵥ φ p.2 := by
  unfold dotProduct
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp measurable_fst).mul
    ((measurable_pi_apply i).comp (hyp.φ_meas.comp measurable_snd))

theorem measurable_expTerm : Measurable fun p : (Fin k → ℝ) × M => expTerm U φ p.1 p.2 := by
  unfold expTerm
  exact Real.measurable_exp.comp ((measurable_dot_field hyp).sub (hyp.U_meas.comp measurable_snd))

omit [MeasurableSpace M] hyp in
theorem expTerm_pos (w : Fin k → ℝ) (x : M) : 0 < expTerm U φ w x := Real.exp_pos _

theorem expTerm_le (w : Fin k → ℝ) :
    ∃ B : ℝ, ∀ x, expTerm U φ w x ≤ B := by
  obtain ⟨c, hc⟩ := hyp.U_lower
  obtain ⟨L, hL⟩ := hyp.φ_bound
  refine ⟨Real.exp ((∑ i, |w i|) * L - c), fun x => ?_⟩
  unfold expTerm
  refine Real.exp_le_exp.2 ?_
  have h1 : w ⬝ᵥ φ x ≤ (∑ i, |w i|) * L := by
    unfold dotProduct
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h2 : |φ x i| ≤ L :=
      le_trans (by simpa using norm_le_pi_norm (φ x) i : |φ x i| ≤ ‖φ x‖) (hL x)
    calc w i * φ x i ≤ |w i * φ x i| := le_abs_self _
      _ = |w i| * |φ x i| := abs_mul _ _
      _ ≤ |w i| * L := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  linarith [hc x]

theorem integrable_expTerm [IsFiniteMeasure m] (w : Fin k → ℝ) :
    Integrable (expTerm U φ w) m := by
  obtain ⟨B, hB⟩ := expTerm_le hyp w
  have hm : Measurable (expTerm U φ w) :=
    (measurable_expTerm hyp).comp (measurable_const.prodMk measurable_id)
  refine Integrable.mono' (integrable_const B) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (expTerm_pos w x)]
  exact hB x

theorem auxPartition_pos [IsFiniteMeasure m] (w : Fin k → ℝ) : 0 < auxPartition U φ m w := by
  have : NeZero m := ⟨hyp.m_ne_zero⟩
  exact integral_exp_pos (f := fun x => w ⬝ᵥ φ x - U x) (integrable_expTerm hyp w)

theorem measurable_auxPartition [IsFiniteMeasure m] : Measurable (auxPartition U φ m) := by
  unfold auxPartition
  exact ((measurable_expTerm hyp).stronglyMeasurable.integral_prod_right' (ν := m)).measurable

end Hyp

end Setup


/-! ### The joint density and its two Tonelli evaluations -/

theorem continuous_gaussWeight (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (N : ℕ+) :
    Continuous (gaussWeight D h N) := by
  unfold gaussWeight quadForm dotProduct mulVec
  fun_prop

section Joint

variable {M : Type*} [MeasurableSpace M]

/-- The exact joint density of `(w, x)` with respect to `Lebesgue ⊗ m^{⊗N}`:
`(N/2π)^{k/2} det(D)^{-1/2} exp(-(N/2)(w-h)ᵀD⁻¹(w-h)) · exp(w·S(x) - ∑ U(xᵢ))`. -/
noncomputable def hubbardDensity (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (U : M → ℝ)
    (φ : M → Fin k → ℝ) (N : ℕ+) (z : (Fin k → ℝ) × (Fin N → M)) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussNorm D N * (gaussWeight D h N z.1 *
    Real.exp (z.1 ⬝ᵥ fieldSum φ z.2 - ∑ i, U (z.2 i))))

/-- The normalized single-site density `exp(w·φ - U)/ζ(w)` of `q_w` with respect to `m`. -/
noncomputable def siteDensity (U : M → ℝ) (φ : M → Fin k → ℝ) (m : Measure M)
    (w : Fin k → ℝ) (x : M) : ℝ :=
  expTerm U φ w x / auxPartition U φ m w

/-- The one-site law `q_w ∝ exp(w·φ - U) dm`, normalized by `ζ(w)`. -/
noncomputable def siteLaw (U : M → ℝ) (φ : M → Fin k → ℝ) (m : Measure M)
    (w : Fin k → ℝ) : Measure M :=
  m.withDensity fun x => ENNReal.ofReal (siteDensity U φ m w x)

/-- The reference measure `Leb ⊗ m^{⊗N}` on `(w, x)`. -/
noncomputable def hubbardRef (k : ℕ) (m : Measure M) (N : ℕ+) :
    Measure ((Fin k → ℝ) × (Fin N → M)) :=
  (volume : Measure (Fin k → ℝ)).prod (Measure.pi fun _ : Fin N => m)

/-- The total mass of the joint density (the partition function of the Hubbard model). -/
noncomputable def hubbardMass (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (U : M → ℝ)
    (φ : M → Fin k → ℝ) (m : Measure M) (N : ℕ+) : ℝ≥0∞ :=
  ∫⁻ z, hubbardDensity D h U φ N z ∂(hubbardRef k m N)

/-- The exact normalized joint law of `(w, x)`. -/
noncomputable def hubbardJoint (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (U : M → ℝ)
    (φ : M → Fin k → ℝ) (m : Measure M) (N : ℕ+) : Measure ((Fin k → ℝ) × (Fin N → M)) :=
  (hubbardMass D h U φ m N)⁻¹ • (hubbardRef k m N).withDensity (hubbardDensity D h U φ N)

/-- The mass `∫ exp(-Nψ(w)) dw` (no Gaussian normalizer included). -/
noncomputable def auxMass (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (U : M → ℝ)
    (φ : M → Fin k → ℝ) (m : Measure M) (N : ℕ+) : ℝ≥0∞ :=
  ∫⁻ w : Fin k → ℝ, ENNReal.ofReal (Real.exp (-(N : ℝ) * auxPotential U φ D h m w))

/-- The auxiliary law `η_N(dw) ∝ e^{-Nψ(w)} dw`. -/
noncomputable def auxLaw (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (U : M → ℝ)
    (φ : M → Fin k → ℝ) (m : Measure M) (N : ℕ+) : Measure (Fin k → ℝ) :=
  (auxMass D h U φ m N)⁻¹ • (volume : Measure (Fin k → ℝ)).withDensity
    fun w => ENNReal.ofReal (Real.exp (-(N : ℝ) * auxPotential U φ D h m w))

/-- The mass of the particle weight. -/
noncomputable def particleMass (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (U : M → ℝ)
    (φ : M → Fin k → ℝ) (m : Measure M) (N : ℕ+) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (particleWeight U φ D h N x) ∂(Measure.pi fun _ : Fin N => m)

/-- The particle law `P_N ∝ exp[-∑U(xᵢ) + h·S + SᵀDS/(2N)] dm^{⊗N}`. -/
noncomputable def hubbardParticleLaw (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (U : M → ℝ)
    (φ : M → Fin k → ℝ) (m : Measure M) (N : ℕ+) : Measure (Fin N → M) :=
  (particleMass D h U φ m N)⁻¹ • (Measure.pi fun _ : Fin N => m).withDensity
    fun x => ENNReal.ofReal (particleWeight U φ D h N x)

omit [MeasurableSpace M] in
theorem exp_field_eq_prod (U : M → ℝ) (φ : M → Fin k → ℝ) {N : ℕ+} (w : Fin k → ℝ)
    (x : Fin N → M) :
    Real.exp (w ⬝ᵥ fieldSum φ x - ∑ i, U (x i)) = ∏ i, expTerm U φ w (x i) := by
  unfold expTerm fieldSum
  rw [dotProduct_sum, ← Finset.sum_sub_distrib, Real.exp_sum]

omit [MeasurableSpace M] in
/-- Integrating the field out of the joint density gives the particle weight (Gaussian MGF). -/
theorem lintegral_hubbardDensity_field {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef)
    (U : M → ℝ) (φ : M → Fin k → ℝ) (h : Fin k → ℝ) (N : ℕ+) (x : Fin N → M) :
    ∫⁻ w, hubbardDensity D h U φ N (w, x) = ENNReal.ofReal (particleWeight U φ D h N x) := by
  have h1 : ∀ w : Fin k → ℝ, hubbardDensity D h U φ N (w, x) =
      ENNReal.ofReal (Real.exp (-(∑ i, U (x i)))) *
        ENNReal.ofReal (gaussNorm D N * (gaussWeight D h N w * Real.exp (w ⬝ᵥ fieldSum φ x))) := by
    intro w
    unfold hubbardDensity
    simp only
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_gaussWeight_mul_exp hD N h _).const_mul (gaussNorm D N))
      (Filter.Eventually.of_forall fun w =>
        mul_nonneg (gaussNorm_pos hD N).le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)),
    integral_gaussWeight_mul_exp hD N h, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold particleWeight
  rw [← Real.exp_add, add_assoc]

variable {m : Measure M} {U : M → ℝ} {φ : M → Fin k → ℝ} (hyp : HubbardHyp m U φ)
include hyp

theorem measurable_fieldSum {N : ℕ+} : Measurable (fieldSum φ : (Fin N → M) → Fin k → ℝ) := by
  unfold fieldSum
  refine Finset.measurable_sum _ fun i _ => ?_
  exact hyp.φ_meas.comp (measurable_pi_apply i)

theorem measurable_hubbardDensity (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (N : ℕ+) :
    Measurable (hubbardDensity D h U φ N) := by
  unfold hubbardDensity
  refine ENNReal.measurable_ofReal.comp (measurable_const.mul
    (((continuous_gaussWeight D h N).measurable.comp measurable_fst).mul
      (Real.measurable_exp.comp ?_)))
  refine Measurable.sub ?_ (Finset.measurable_sum _ fun i _ => hyp.U_meas.comp
    ((measurable_pi_apply i).comp measurable_snd))
  unfold dotProduct
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp measurable_fst).mul
    (((measurable_pi_apply i).comp (measurable_fieldSum hyp)).comp measurable_snd)

variable [IsFiniteMeasure m]

/-- Integrating the particles out of the joint density. -/
theorem lintegral_hubbardDensity_particles {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef)
    (h : Fin k → ℝ) (N : ℕ+) (w : Fin k → ℝ) :
    ∫⁻ x, hubbardDensity D h U φ N (w, x) ∂(Measure.pi fun _ : Fin N => m) =
      ENNReal.ofReal (gaussNorm D N * gaussWeight D h N w * auxPartition U φ m w ^ (N : ℕ)) := by
  have hnn : 0 ≤ gaussNorm D N * gaussWeight D h N w :=
    mul_nonneg (gaussNorm_pos hD N).le (Real.exp_pos _).le
  have h1 : ∀ x : Fin N → M, hubbardDensity D h U φ N (w, x) =
      ENNReal.ofReal (gaussNorm D N * gaussWeight D h N w) *
        ∏ i, ENNReal.ofReal (expTerm U φ w (x i)) := by
    intro x
    unfold hubbardDensity
    simp only
    rw [exp_field_eq_prod, ← mul_assoc, ENNReal.ofReal_mul hnn,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (expTerm_pos w (x i)).le)]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_pi_prod_ofReal (μ := m) (fun _ : Fin N => expTerm U φ w)
      (fun _ => integrable_expTerm hyp w) (fun _ x => (expTerm_pos w x).le)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_expTerm hyp w)
      (Filter.Eventually.of_forall fun x => (expTerm_pos w x).le)]
  have e : ∫ x, expTerm U φ w x ∂m = auxPartition U φ m w := rfl
  rw [e, ← ENNReal.ofReal_pow (auxPartition_pos hyp w).le, ← ENNReal.ofReal_mul hnn]

theorem gaussWeight_mul_pow_eq {D : Matrix (Fin k) (Fin k) ℝ} (h : Fin k → ℝ) (N : ℕ+)
    (w : Fin k → ℝ) :
    gaussWeight D h N w * auxPartition U φ m w ^ (N : ℕ) =
      Real.exp (-(N : ℝ) * auxPotential U φ D h m w) := by
  have hz := auxPartition_pos hyp (m := m) w
  unfold auxPotential gaussWeight
  have : -(N : ℝ) * (1 / 2 * quadForm D⁻¹ (w - h) - Real.log (auxPartition U φ m w)) =
      -((N : ℝ) / 2) * quadForm D⁻¹ (w - h) + (N : ℕ) * Real.log (auxPartition U φ m w) := by
    ring
  rw [this, Real.exp_add, Real.exp_nat_mul, Real.exp_log hz]

variable {D : Matrix (Fin k) (Fin k) ℝ}

theorem hubbardMass_eq_aux (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    hubbardMass D h U φ m N = ENNReal.ofReal (gaussNorm D N) * auxMass D h U φ m N := by
  unfold hubbardMass auxMass hubbardRef
  rw [lintegral_prod _ (measurable_hubbardDensity hyp D h N).aemeasurable]
  have key : ∀ w : Fin k → ℝ,
      ∫⁻ x, hubbardDensity D h U φ N (w, x) ∂(Measure.pi fun _ : Fin N => m) =
        ENNReal.ofReal (gaussNorm D N) *
          ENNReal.ofReal (Real.exp (-(N : ℝ) * auxPotential U φ D h m w)) := by
    intro w
    rw [lintegral_hubbardDensity_particles hyp hD h N w, mul_assoc,
      gaussWeight_mul_pow_eq hyp h N w, ENNReal.ofReal_mul (gaussNorm_pos hD N).le]
  simp_rw [key]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

omit [IsFiniteMeasure m] in
theorem measurable_particleWeight (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (N : ℕ+) :
    Measurable (particleWeight U φ D h N : (Fin N → M) → ℝ) := by
  have hg : Continuous fun s : Fin k → ℝ => h ⬝ᵥ s + (s ⬝ᵥ D *ᵥ s) / (2 * (N : ℝ)) := by
    unfold dotProduct mulVec; fun_prop
  have : (particleWeight U φ D h N : (Fin N → M) → ℝ) = fun x =>
      Real.exp (-(∑ i, U (x i)) + (fun s : Fin k → ℝ => h ⬝ᵥ s + (s ⬝ᵥ D *ᵥ s) / (2 * (N : ℝ)))
        (fieldSum φ x)) := by
    funext x; unfold particleWeight; rw [add_assoc]
  rw [this]
  refine Real.measurable_exp.comp (Measurable.add ?_ (hg.measurable.comp (measurable_fieldSum hyp)))
  exact (Finset.measurable_sum _ fun i _ => hyp.U_meas.comp (measurable_pi_apply i)).neg

omit [IsFiniteMeasure m] in
theorem particleWeight_le (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (N : ℕ+) :
    ∃ B : ℝ, ∀ x : Fin N → M, particleWeight U φ D h N x ≤ B := by
  obtain ⟨c, hc⟩ := hyp.U_lower
  obtain ⟨L, hL⟩ := hyp.φ_bound
  have hg : Continuous fun s : Fin k → ℝ => h ⬝ᵥ s + (s ⬝ᵥ D *ᵥ s) / (2 * (N : ℝ)) := by
    unfold dotProduct mulVec; fun_prop
  obtain ⟨G, hG⟩ := (isCompact_closedBall (0 : Fin k → ℝ) ((N : ℝ) * L)).bddAbove_image
    hg.continuousOn
  refine ⟨Real.exp (-((N : ℝ) * c) + G), fun x => ?_⟩
  unfold particleWeight
  refine Real.exp_le_exp.2 ?_
  have hmem : fieldSum φ x ∈ Metric.closedBall (0 : Fin k → ℝ) ((N : ℝ) * L) := by
    rw [mem_closedBall_zero_iff]
    unfold fieldSum
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hL (x i)).trans ?_)
    simp
  have hS := hG ⟨fieldSum φ x, hmem, rfl⟩
  have hU : (N : ℝ) * c ≤ ∑ i, U (x i) := by
    have := Finset.sum_le_sum (s := Finset.univ) fun i _ => hc (x i)
    simpa using this
  simp only at hS
  linarith

theorem particleMass_ne_top (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (N : ℕ+) :
    particleMass D h U φ m N ≠ ∞ := by
  obtain ⟨B, hB⟩ := particleWeight_le hyp D h N
  refine ne_top_of_le_ne_top (b := ∫⁻ _x, ENNReal.ofReal B ∂(Measure.pi fun _ : Fin N => m)) ?_ ?_
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hB x)

theorem particleMass_ne_zero (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (N : ℕ+) :
    particleMass D h U φ m N ≠ 0 := by
  have hmu : m Set.univ ≠ 0 := Measure.measure_univ_ne_zero.2 hyp.m_ne_zero
  have hpi : (Measure.pi fun _ : Fin N => m) Set.univ ≠ 0 := by
    rw [Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hmu
  intro h0
  unfold particleMass at h0
  have hmeas : Measurable fun x : Fin N → M => ENNReal.ofReal (particleWeight U φ D h N x) :=
    ENNReal.measurable_ofReal.comp (measurable_particleWeight hyp D h N)
  rw [lintegral_eq_zero_iff hmeas] at h0
  have hfalse : ∀ᵐ x ∂(Measure.pi fun _ : Fin N => m), False := by
    filter_upwards [h0] with x hx
    have : (ENNReal.ofReal (particleWeight U φ D h N x)) = 0 := hx
    rw [ENNReal.ofReal_eq_zero] at this
    exact absurd this (not_le.2 (Real.exp_pos _))
  have hbot : MeasureTheory.ae (Measure.pi fun _ : Fin N => m) = ⊥ :=
    Filter.eventually_false_iff_eq_bot.1 hfalse
  have hz : (Measure.pi fun _ : Fin N => m) = 0 := ae_eq_bot.1 hbot
  exact hpi (by simp [hz])

theorem hubbardMass_eq_particleMass (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    hubbardMass D h U φ m N = particleMass D h U φ m N := by
  unfold hubbardMass particleMass hubbardRef
  rw [lintegral_prod_symm _ (measurable_hubbardDensity hyp D h N).aemeasurable]
  exact lintegral_congr fun x => lintegral_hubbardDensity_field hD U φ h N x

theorem hubbardMass_ne_top (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    hubbardMass D h U φ m N ≠ ∞ := by
  rw [hubbardMass_eq_particleMass hyp hD]; exact particleMass_ne_top hyp D h N

theorem hubbardMass_ne_zero (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    hubbardMass D h U φ m N ≠ 0 := by
  rw [hubbardMass_eq_particleMass hyp hD]; exact particleMass_ne_zero hyp D h N

theorem auxMass_ne_top (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    auxMass D h U φ m N ≠ ∞ := by
  intro h0
  have e := hubbardMass_eq_aux hyp hD h N
  rw [h0, ENNReal.mul_top (ENNReal.ofReal_pos.2 (gaussNorm_pos hD N)).ne'] at e
  exact hubbardMass_ne_top hyp hD h N e

theorem auxMass_ne_zero (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    auxMass D h U φ m N ≠ 0 := by
  intro h0
  have e := hubbardMass_eq_aux hyp hD h N
  rw [h0, mul_zero] at e
  exact hubbardMass_ne_zero hyp hD h N e

theorem isProbabilityMeasure_hubbardJoint (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    IsProbabilityMeasure (hubbardJoint D h U φ m N) := by
  refine ⟨?_⟩
  unfold hubbardJoint
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (hubbardMass_ne_zero hyp hD h N) (hubbardMass_ne_top hyp hD h N)

theorem isProbabilityMeasure_siteLaw (w : Fin k → ℝ) :
    IsProbabilityMeasure (siteLaw U φ m w) := by
  refine ⟨?_⟩
  have hz := auxPartition_pos hyp (m := m) w
  unfold siteLaw siteDensity
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_expTerm hyp w).div_const _)
      (Filter.Eventually.of_forall fun x => div_nonneg (expTerm_pos w x).le hz.le)]
  rw [integral_div]
  change ENNReal.ofReal (auxPartition U φ m w / auxPartition U φ m w) = 1
  rw [div_self hz.ne', ENNReal.ofReal_one]

theorem hubbardDensity_eq (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) (w : Fin k → ℝ)
    (x : Fin N → M) :
    hubbardDensity D h U φ N (w, x) =
      ENNReal.ofReal (gaussNorm D N) *
        ENNReal.ofReal (Real.exp (-(N : ℝ) * auxPotential U φ D h m w)) *
          ENNReal.ofReal (∏ i, siteDensity U φ m w (x i)) := by
  have hz := auxPartition_pos hyp (m := m) w
  have hP : ∏ i, expTerm U φ w (x i) =
      auxPartition U φ m w ^ (N : ℕ) * ∏ i, siteDensity U φ m w (x i) := by
    unfold siteDensity
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  have h1 : 0 ≤ gaussNorm D N := (gaussNorm_pos hD N).le
  have h2 : 0 ≤ gaussNorm D N * (gaussWeight D h N w * auxPartition U φ m w ^ (N : ℕ)) :=
    mul_nonneg h1 (mul_nonneg (Real.exp_pos _).le (pow_nonneg hz.le _))
  unfold hubbardDensity
  simp only
  rw [exp_field_eq_prod, hP, ← gaussWeight_mul_pow_eq hyp h N w, ← ENNReal.ofReal_mul h1,
    ← ENNReal.ofReal_mul h2]
  congr 1
  ring

/-- The density of the product law `q_w^{⊗N}` against `m^{⊗N}`, jointly in `(w, x)`. -/
noncomputable def kernelDensity (U : M → ℝ) (φ : M → Fin k → ℝ) (m : Measure M) {N : ℕ+}
    (z : (Fin k → ℝ) × (Fin N → M)) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ i, siteDensity U φ m z.1 (z.2 i))

theorem measurable_kernelDensity {N : ℕ+} :
    Measurable (kernelDensity U φ m : (Fin k → ℝ) × (Fin N → M) → ℝ≥0∞) := by
  unfold kernelDensity siteDensity
  refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ => ?_)
  exact ((measurable_expTerm hyp).comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).div
    ((measurable_auxPartition hyp).comp measurable_fst)

/-- The disintegration kernel `w ↦ q_w^{⊗N}(slice)` as an iterated integral. -/
noncomputable def kernelFn (U : M → ℝ) (φ : M → Fin k → ℝ) (m : Measure M) {N : ℕ+}
    (s : Set ((Fin k → ℝ) × (Fin N → M))) (w : Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, s.indicator (kernelDensity U φ m) (w, x) ∂(Measure.pi fun _ : Fin N => m)

theorem measurable_kernelFn {N : ℕ+} {s : Set ((Fin k → ℝ) × (Fin N → M))}
    (hs : MeasurableSet s) : Measurable (kernelFn U φ m s) :=
  Measurable.lintegral_prod_right' ((measurable_kernelDensity hyp).indicator hs)

theorem pi_siteLaw_slice {N : ℕ+} {s : Set ((Fin k → ℝ) × (Fin N → M))}
    (hs : MeasurableSet s) (w : Fin k → ℝ) :
    (Measure.pi fun _ : Fin N => siteLaw U φ m w) (Prod.mk w ⁻¹' s) = kernelFn U φ m s w := by
  have hz := auxPartition_pos hyp (m := m) w
  have hsl : MeasurableSet (Prod.mk w ⁻¹' s) := measurable_prodMk_left hs
  unfold siteLaw kernelFn
  rw [pi_withDensity_ofReal (m := m) (siteDensity U φ m w)
      ((integrable_expTerm hyp w).div_const _)
      (fun x => div_nonneg (expTerm_pos w x).le hz.le) N,
    withDensity_apply _ hsl, ← lintegral_indicator hsl]
  refine lintegral_congr fun x => ?_
  by_cases hx : (w, x) ∈ s
  · rw [Set.indicator_of_mem (show x ∈ Prod.mk w ⁻¹' s from hx), Set.indicator_of_mem hx]
    rfl
  · rw [Set.indicator_of_notMem (show x ∉ Prod.mk w ⁻¹' s from hx), Set.indicator_of_notMem hx]

theorem measurable_auxPotential (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) :
    Measurable (auxPotential U φ D h m) := by
  unfold auxPotential
  have hq : Continuous (quadForm D⁻¹ : (Fin k → ℝ) → ℝ) := by
    unfold quadForm dotProduct mulVec; fun_prop
  exact (measurable_const.mul (hq.measurable.comp (measurable_id.sub measurable_const))).sub
    (Real.measurable_log.comp (measurable_auxPartition hyp))

theorem measurable_auxDensity (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (N : ℕ+) :
    Measurable fun w => ENNReal.ofReal (Real.exp (-(N : ℝ) * auxPotential U φ D h m w)) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (measurable_auxPotential hyp D h)))

theorem hubbardJoint_apply (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+)
    {s : Set ((Fin k → ℝ) × (Fin N → M))} (hs : MeasurableSet s) :
    hubbardJoint D h U φ m N s =
      ∫⁻ w, (Measure.pi fun _ : Fin N => siteLaw U φ m w) (Prod.mk w ⁻¹' s)
        ∂(auxLaw D h U φ m N) := by
  have hρm := measurable_auxDensity hyp (m := m) D h N
  have hκ := measurable_kernelFn hyp hs
  have hinner : ∀ w : Fin k → ℝ,
      ∫⁻ x, s.indicator (hubbardDensity D h U φ N) (w, x) ∂(Measure.pi fun _ : Fin N => m) =
        ENNReal.ofReal (gaussNorm D N) *
          (ENNReal.ofReal (Real.exp (-(N : ℝ) * auxPotential U φ D h m w)) *
            kernelFn U φ m s w) := by
    intro w
    unfold kernelFn
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    by_cases hx : (w, x) ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hubbardDensity_eq hyp hD h N w x,
        mul_assoc]
      rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, mul_zero]
  have final : ∀ a B X : ℝ≥0∞, a ≠ 0 → a ≠ ∞ → (a⁻¹ * B⁻¹) * (a * X) = B⁻¹ * X := by
    intro a B X ha0 haT
    calc (a⁻¹ * B⁻¹) * (a * X) = (a⁻¹ * a) * (B⁻¹ * X) := by ring
      _ = B⁻¹ * X := by rw [ENNReal.inv_mul_cancel ha0 haT, one_mul]
  have ha0 : ENNReal.ofReal (gaussNorm D N) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (gaussNorm_pos hD N)).ne'
  unfold hubbardJoint auxLaw
  simp_rw [pi_siteLaw_slice hyp hs]
  rw [Measure.smul_apply, withDensity_apply _ hs, ← lintegral_indicator hs, smul_eq_mul]
  unfold hubbardRef
  rw [lintegral_prod _ ((measurable_hubbardDensity hyp D h N).indicator hs).aemeasurable]
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ hρm hκ, hubbardMass_eq_aux hyp hD h N,
    ENNReal.mul_inv (Or.inr (auxMass_ne_top hyp hD h N)) (Or.inl ENNReal.ofReal_ne_top),
    smul_eq_mul]
  simp only [Pi.mul_apply]
  exact final _ _ _ ha0 ENNReal.ofReal_ne_top

theorem hubbardJoint_map_fst (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    (hubbardJoint D h U φ m N).map Prod.fst = auxLaw D h U φ m N := by
  refine Measure.ext fun t ht => ?_
  rw [Measure.map_apply measurable_fst ht, hubbardJoint_apply hyp hD h N (measurable_fst ht)]
  have key : ∀ w : Fin k → ℝ,
      (Measure.pi fun _ : Fin N => siteLaw U φ m w) (Prod.mk w ⁻¹' (Prod.fst ⁻¹' t)) =
        t.indicator 1 w := by
    intro w
    have := isProbabilityMeasure_siteLaw hyp (m := m) w
    by_cases hw : w ∈ t
    · have : Prod.mk w ⁻¹' (Prod.fst ⁻¹' t) = (Set.univ : Set (Fin N → M)) := by
        ext x; simp [hw]
      rw [this, measure_univ, Set.indicator_of_mem hw]; rfl
    · have : Prod.mk w ⁻¹' (Prod.fst ⁻¹' t) = (∅ : Set (Fin N → M)) := by
        ext x; simp [hw]
      rw [this, measure_empty, Set.indicator_of_notMem hw]
  simp_rw [key]
  exact lintegral_indicator_one ht

theorem hubbardJoint_map_snd (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    (hubbardJoint D h U φ m N).map Prod.snd = hubbardParticleLaw D h U φ m N := by
  refine Measure.ext fun t ht => ?_
  rw [Measure.map_apply measurable_snd ht]
  unfold hubbardJoint hubbardParticleLaw
  rw [Measure.smul_apply, Measure.smul_apply, withDensity_apply _ (measurable_snd ht),
    withDensity_apply _ ht, ← lintegral_indicator (measurable_snd ht), ← lintegral_indicator ht,
    hubbardMass_eq_particleMass hyp hD h N, smul_eq_mul, smul_eq_mul]
  congr 1
  unfold hubbardRef
  rw [lintegral_prod_symm _
    ((measurable_hubbardDensity hyp D h N).indicator (measurable_snd ht)).aemeasurable]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ t
  · have : ∀ w : Fin k → ℝ, (Prod.snd ⁻¹' t).indicator (hubbardDensity D h U φ N) (w, x) =
        hubbardDensity D h U φ N (w, x) := fun w =>
      Set.indicator_of_mem (show (w, x) ∈ Prod.snd ⁻¹' t from hx) _
    simp_rw [this]
    rw [lintegral_hubbardDensity_field hD U φ h N x, Set.indicator_of_mem hx]
  · have : ∀ w : Fin k → ℝ, (Prod.snd ⁻¹' t).indicator (hubbardDensity D h U φ N) (w, x) = 0 :=
      fun w => Set.indicator_of_notMem (show (w, x) ∉ Prod.snd ⁻¹' t from hx) _
    simp_rw [this]
    rw [Set.indicator_of_notMem hx]
    simp

end Joint

end DGPS.FiniteN.Tools.Hubbard

namespace DGPS.FiniteN

open Tools.Hubbard

/-- **Exact finite-rank Hubbard identity.**  The normalized joint law of `(w, x)` has
`w`-marginal `η_N ∝ e^{-Nψ(w)} dw`, `x`-marginal the particle law `P_N`, and conditional law of
`x` given `w` equal to `q_w^{⊗N}`; the Gaussian normalizer `(N/2π)^{k/2} det(D)^{-1/2}` is
kept in the mass relation. -/
theorem exact_finite_rank_hubbard_identity {M : Type*} [MeasurableSpace M] {k : ℕ}
    {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ} {φ : M → Fin k → ℝ}
    (hyp : HubbardHyp m U φ) {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef)
    (h : Fin k → ℝ) (N : ℕ+) :
    (hubbardMass D h U φ m N = ENNReal.ofReal (gaussNorm D N) * auxMass D h U φ m N ∧
      hubbardMass D h U φ m N = particleMass D h U φ m N ∧
      auxMass D h U φ m N ≠ 0 ∧ auxMass D h U φ m N ≠ ∞) ∧
    IsProbabilityMeasure (hubbardJoint D h U φ m N) ∧
    (hubbardJoint D h U φ m N).map Prod.fst = auxLaw D h U φ m N ∧
    (hubbardJoint D h U φ m N).map Prod.snd = hubbardParticleLaw D h U φ m N ∧
    (∀ w, IsProbabilityMeasure (siteLaw U φ m w)) ∧
    ∀ s : Set ((Fin k → ℝ) × (Fin N → M)), MeasurableSet s →
      hubbardJoint D h U φ m N s =
        ∫⁻ w, (Measure.pi fun _ : Fin N => siteLaw U φ m w) (Prod.mk w ⁻¹' s)
          ∂(auxLaw D h U φ m N) :=
  ⟨⟨hubbardMass_eq_aux hyp hD h N, hubbardMass_eq_particleMass hyp hD h N,
      auxMass_ne_zero hyp hD h N, auxMass_ne_top hyp hD h N⟩,
    isProbabilityMeasure_hubbardJoint hyp hD h N, hubbardJoint_map_fst hyp hD h N,
    hubbardJoint_map_snd hyp hD h N, isProbabilityMeasure_siteLaw hyp,
    fun _ hs => hubbardJoint_apply hyp hD h N hs⟩

end DGPS.FiniteN
