import DGPS.Lipschitz.EquilibriumDissipation
import DGPS.Lipschitz.T01PerturbationDissipation

/-!
# Absolute-domain Euler scores for actual equilibrium tilts

The same constructed absolute density represents `(1+h) μ` and has score
`sqrt(ρ) ∇(log(1+h)+Th)`. The Lipschitz constants here construct the domain only;
they are not substituted for the exact gradient in the dissipation.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace DGPS.Lipschitz

variable {d : ℕ}

private theorem t01_abs_log_sub_log_le {a b c : ℝ} (hc : 0 < c)
    (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / c := by
  have ha0 : 0 < a := hc.trans_le ha
  have hb0 : 0 < b := hc.trans_le hb
  have h1 : Real.log a - Real.log b ≤ |a - b| / c := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos ha0 hb0)).trans ?_
    have e : a / b - 1 = (a - b) / b := by field_simp
    rw [e]
    exact (div_le_div_of_nonneg_right (le_abs_self _) hb0.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hc hb)
  have h2 : Real.log b - Real.log a ≤ |a - b| / c := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hb0 ha0)).trans ?_
    have e : b / a - 1 = (b - a) / a := by field_simp
    rw [e]
    calc (b - a) / a ≤ |b - a| / a :=
          div_le_div_of_nonneg_right (le_abs_self _) ha0.le
      _ = |a - b| / a := by rw [abs_sub_comm]
      _ ≤ |a - b| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc ha
  rw [abs_le]
  constructor <;> linarith

/-- An actual positive continuous Lipschitz tilt has an absolute-admissible square root
and its exact Euler score, for every realization of the weak drift. -/
theorem exists_t01_tilt_score (A : InteractionData d) (hA : LipschitzData A)
    (μ : ProbabilityMeasure (Torus d))
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    (h : C(Torus d, ℝ)) {Lh : ℝ} (hLip : TorusLipschitzWith Lh (fun x => h x))
    (hpos : ∀ x, 0 < 1 + h x) (h0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) :
    ∃ ρ : AbsoluteDensity d,
      (densityMeasure ρ : Measure (Torus d)) =
        perturb (μ : Measure (Torus d)) (fun x => 1 + h x) ∧
      ∀ drift : AbsoluteDrift A, ∀ᵐ x ∂haar d,
        scalarScore A drift ρ x = ρ.sqrt x •
          smoothGrad (fun y => Real.log (1 + h y) +
            centeredOperatorC A (μ : Measure (Torus d)) h y) x := by
  obtain ⟨m, hm, hmx⟩ := exists_lower_of_mem_posSet hpos
  have hlog : TorusLipschitzWith (|Lh| / m) (fun x => Real.log (1 + h x)) := by
    intro x y
    calc |Real.log (1 + h x) - Real.log (1 + h y)|
        ≤ |(1 + h x) - (1 + h y)| / m := t01_abs_log_sub_log_le hm (hmx x) (hmx y)
      _ = |h x - h y| / m := by congr 2; ring
      _ ≤ (|Lh| * torusDist x y) / m :=
        div_le_div_of_nonneg_right (lip034_lipschitz_abs hLip x y) hm.le
      _ = (|Lh| / m) * torusDist x y := by ring
  obtain ⟨LT, hT⟩ := lip034_centeredOperatorC_lipschitz (μ := μ) hA h
  let E : C(Torus d, ℝ) := nemLog h + centeredOperatorC A (μ : Measure (Torus d)) h
  have hE : ∀ x, E x = Real.log (1 + h x) +
      centeredOperatorC A (μ : Measure (Torus d)) h x := by
    intro x
    simp only [E, ContinuousMap.add_apply, nemLog_apply hpos]
  have hELip : TorusLipschitzWith (|Lh| / m + |LT|) (fun x => E x) := by
    simpa only [hE] using lip034_lipschitz_add hlog (lip034_lipschitz_abs hT)
  obtain ⟨ρ, hρ, hs, -⟩ := lip034_dissipation_core_with_score hA
    (φ := fun _ : Fin 1 => E) hmin
    (Lφ := fun _ => |Lh| / m + |LT|)
    (fun _ => ⟨by positivity, hELip⟩) hpos h0
    (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ))) 0 (by
      intro x
      change Real.log (1 + h x) + centeredOperatorC A (μ : Measure (Torus d)) h x =
        0 + ∑ _i : Fin 1, (1 : ℝ) * E x
      simpa only [Fin.sum_univ_one, one_mul, zero_add] using (hE x).symm)
  refine ⟨ρ, hρ, ?_⟩
  intro drift
  have heFun : (fun y => ∑ i : Fin 1,
      (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)) : Par 1) i * E y) =
      (fun y => Real.log (1 + h y) + centeredOperatorC A (μ : Measure (Torus d)) h y) := by
    funext y
    change (∑ _i : Fin 1, (1 : ℝ) * E y) = _
    simpa only [Fin.sum_univ_one, one_mul] using hE y
  simpa only [heFun] using hs drift

/-- The differential identity driving the sharp tilt dissipation limit. It is an a.e.
identity, since only Lipschitz regularity of the perturbation is required. -/
theorem ae_t01_tilt_euler_gradient (A : InteractionData d) (hA : LipschitzData A)
    (μ : ProbabilityMeasure (Torus d)) (h g : C(Torus d, ℝ))
    {Lh : ℝ} (hLip : TorusLipschitzWith Lh (fun x => h x))
    (hsum : ∀ x, h x + centeredOperatorC A (μ : Measure (Torus d)) h x = g x)
    (t : ℝ) (hpos : ∀ x, 0 < 1 + t * h x) :
    ∀ᵐ x ∂haar d,
      smoothGrad (fun y => Real.log (1 + t * h y) +
        t * centeredOperatorC A (μ : Measure (Torus d)) h y) x =
      t • ((1 + t * h x)⁻¹ • (smoothGrad (fun y => g y) x +
        (t * h x) • smoothGrad (fun y => centeredOperatorC A (μ : Measure (Torus d)) h y) x)) := by
  obtain ⟨LT, hT⟩ := lip034_centeredOperatorC_lipschitz (μ := μ) hA h
  filter_upwards [ae_differentiableAt_secT (abs_nonneg Lh) (lip034_lipschitz_abs hLip),
    ae_differentiableAt_secT (abs_nonneg LT) (lip034_lipschitz_abs hT)] with x hx hy
  have hlog := ((hx.hasFDerivAt.const_mul t).const_add 1).log (by
    simpa only [Function.comp_apply, SharpLSI.liftT_secT] using (hpos x).ne')
  have hE := hlog.add (hy.hasFDerivAt.const_mul t)
  have hg : (fun y => g y) ∘ torusLift =
      ((fun y => h y) ∘ torusLift) +
        ((fun y => centeredOperatorC A (μ : Measure (Torus d)) h y) ∘ torusLift) := by
    funext z
    exact (hsum (torusLift z)).symm
  ext j
  simp only [smoothGrad_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  unfold coordPartial
  rw [show ((fun y => Real.log (1 + t * h y) +
      t * centeredOperatorC A (μ : Measure (Torus d)) h y) ∘ torusLift) =
      (fun z => Real.log (1 + t * (h ∘ torusLift) z)) +
        (fun z => t * ((fun y => centeredOperatorC A (μ : Measure (Torus d)) h y) ∘ torusLift) z)
      from rfl, hE.fderiv, hg, fderiv_add hx hy]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Function.comp_apply, SharpLSI.liftT_secT]
  field_simp [(hpos x).ne']
  <;> ring

end DGPS.Lipschitz
