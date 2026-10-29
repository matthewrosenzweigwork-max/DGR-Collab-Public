import SharpSymmetricLSI.Paper.LemmaA2_9

/-!
# R25 (A.9), part 10: smoothing the potential

For a continuous `Q` on the torus with `D²Q ≥ -K` in the sense of distributions (every direction),
the mollifications `Qₙ = φₙ ⋆ Q` are smooth with `D²Qₙ ≥ -K` pointwise (`semiconvex_mollL`), and
`ρₙ = e^{-Qₙ}/Zₙ` are good densities with smooth lifts, uniform bounds, `-log ρₙ = Qₙ + log Zₙ`,
and `ρₙ → e^{-Q}/∫e^{-Q}` pointwise (`rhoN_*`). Mollification preserves Euclidean Lipschitz
bounds on lifts (`mollL_sub_le`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

section conv

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem secondDirDeriv_convR {F ψ : (ι → ℝ) → ℝ} (hF : LocallyIntegrable F volume)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (v y : ι → ℝ) :
    secondDirDeriv (convR F ψ) v y = convR F (secondDirDeriv ψ v) y := by
  set ψv : (ι → ℝ) → ℝ := fun z => fderiv ℝ ψ z v
  have hψv : ContDiff ℝ ∞ ψv := (hψ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hψvc : HasCompactSupport ψv := hψc.fderiv_apply (𝕜 := ℝ) v
  have e : (fun z => fderiv ℝ (convR F ψ) z v) = convR F ψv :=
    funext fun z => (hasFDerivAt_convR_dir hF hψ hψc z v).2
  unfold secondDirDeriv
  rw [e, (hasFDerivAt_convR_dir hF hψv hψvc y v).2]

/-- **Mollification preserves semiconvexity, pointwise.** -/
theorem semiconvex_mollL {Q : UnitAddTorus ι → ℝ} (hQ : LocallyIntegrable (Q ∘ liftT) volume)
    {K : ℝ} (hK : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∀ ξ : ι → ℝ, -K * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤ ∫ x, Q (liftT x) * secondDirDeriv φ ξ x)
    (n : ℕ) (y v : ι → ℝ) : -K * ∑ i, v i ^ 2 ≤ secondDirDeriv (mollL n (Q ∘ liftT)) v y := by
  set ψ := phiSeq (ι := ι) n
  have hψ : ContDiff ℝ ∞ ψ := contDiff_phiSeq n
  have hψc : HasCompactSupport ψ := hasCompactSupport_phiSeq n
  rw [mollL_eq_convR, secondDirDeriv_convR hQ hψ hψc, convR_apply]
  have hφ : ContDiff ℝ ∞ (fun t => ψ (y - t)) := hψ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun t => ψ (y - t)) := hψc.comp_homeomorph (Homeomorph.subLeft y)
  have h := hK (fun t => ψ (y - t)) hφ hφc (fun t => phiSeq_nonneg n _) v
  have hint : ∫ t, ψ (y - t) = 1 := by
    rw [integral_sub_left_eq_self (fun t => ψ t) volume y]; exact integral_phiSeq n
  rw [hint, mul_one] at h
  simp_rw [secondDirDeriv_comp_sub hψ y] at h
  simpa [Function.comp] using h

theorem abs_mollL_le {F : (ι → ℝ) → ℝ} {B : ℝ} (hB : ∀ x, |F x| ≤ B) (n : ℕ) (x : ι → ℝ) :
    |mollL n F x| ≤ B := by
  rw [mollL_apply']
  calc |∫ s, phiSeq n s * F (x - s)| ≤ ∫ s, |phiSeq n s * F (x - s)| := abs_integral_le_integral_abs
    _ ≤ ∫ s, phiSeq n s * B := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (((contDiff_phiSeq n).continuous.integrable_of_hasCompactSupport
            (hasCompactSupport_phiSeq n)).mul_const B) (Eventually.of_forall fun s => ?_)
        show |phiSeq n s * F (x - s)| ≤ phiSeq n s * B
        rw [abs_mul, abs_of_nonneg (phiSeq_nonneg n s)]
        exact mul_le_mul_of_nonneg_left (hB _) (phiSeq_nonneg n s)
    _ = B := by rw [integral_mul_const, integral_phiSeq, one_mul]

/-- **Mollification preserves Euclidean Lipschitz bounds.** -/
theorem mollL_sub_le {F : (ι → ℝ) → ℝ} (hFc : Continuous F) {L : ℝ}
    (hF : ∀ x y, F x - F y ≤ L * dE x y) {B : ℝ} (hB : ∀ x, |F x| ≤ B) (n : ℕ) (x y : ι → ℝ) :
    mollL n F x - mollL n F y ≤ L * dE x y := by
  have hφi : Integrable (phiSeq (ι := ι) n) :=
    (contDiff_phiSeq n).continuous.integrable_of_hasCompactSupport (hasCompactSupport_phiSeq n)
  have hi : ∀ z, Integrable fun s => phiSeq n s * F (z - s) := fun z =>
    hφi.mul_bdd (c := B) (hFc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hB _)
  rw [mollL_apply', mollL_apply', ← integral_sub (hi x) (hi y)]
  calc ∫ s, (phiSeq n s * F (x - s) - phiSeq n s * F (y - s)) ≤ ∫ s, phiSeq n s * (L * dE x y) := by
        refine integral_mono ((hi x).sub (hi y)) (hφi.mul_const _) fun s => ?_
        rw [← mul_sub]
        refine mul_le_mul_of_nonneg_left ?_ (phiSeq_nonneg n s)
        have := hF (x - s) (y - s)
        rwa [dE_sub_sub] at this
    _ = L * dE x y := by rw [integral_mul_const, integral_phiSeq, one_mul]

end conv

section dens

variable {d : ℕ}

/-- The mollified potential. -/
noncomputable def QN (Q : Torus d → ℝ) (n : ℕ) : Torus d → ℝ := moll n Q

/-- Its normalization. -/
noncomputable def ZN (Q : Torus d → ℝ) (n : ℕ) : ℝ := ∫ y, Real.exp (-QN Q n y)

/-- The smoothed density `e^{-Qₙ}/Zₙ`. -/
noncomputable def rhoN (Q : Torus d → ℝ) (n : ℕ) (y : Torus d) : ℝ := Real.exp (-QN Q n y) / ZN Q n

variable {Q : Torus d → ℝ} (hQc : Continuous Q) {B : ℝ} (hB : ∀ y, |Q y| ≤ B)
include hQc hB

theorem abs_QN_le (n : ℕ) (y : Torus d) : |QN Q n y| ≤ B := by
  have h := abs_mollL_le (F := Q ∘ liftT) (fun x => hB _) n (secT y)
  rw [← moll_comp_liftT] at h
  simpa [QN, liftT_secT] using h

theorem contDiff_QN (n : ℕ) : ContDiff ℝ ∞ (QN Q n ∘ liftT) :=
  moll_comp_liftT_contDiff n (hQc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem continuous_QN (n : ℕ) : Continuous (QN Q n) :=
  continuous_of_liftT' (contDiff_QN hQc hB n).continuous

theorem ZN_bounds (n : ℕ) : Real.exp (-B) ≤ ZN Q n ∧ ZN Q n ≤ Real.exp B := by
  have hc : Continuous fun y => Real.exp (-QN Q n y) := (continuous_QN hQc hB n).neg.rexp
  have hi : Integrable fun y => Real.exp (-QN Q n y) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  constructor
  · have : ∫ _y : Torus d, Real.exp (-B) ≤ ZN Q n := integral_mono (integrable_const _) hi
      fun y => Real.exp_le_exp.mpr (by linarith [le_abs_self (QN Q n y), abs_QN_le hQc hB n y])
    simpa using this
  · have : ZN Q n ≤ ∫ _y : Torus d, Real.exp B := integral_mono hi (integrable_const _)
      fun y => Real.exp_le_exp.mpr (by linarith [neg_abs_le (QN Q n y), abs_QN_le hQc hB n y])
    simpa using this

theorem ZN_pos (n : ℕ) : 0 < ZN Q n := (Real.exp_pos _).trans_le (ZN_bounds hQc hB n).1

theorem rhoN_bounds (n : ℕ) (y : Torus d) :
    Real.exp (-(2 * B)) ≤ rhoN Q n y ∧ rhoN Q n y ≤ Real.exp (2 * B) := by
  have hZ := ZN_bounds hQc hB n
  have hZp := ZN_pos hQc hB n
  have hq := abs_QN_le hQc hB n y
  rw [abs_le] at hq
  constructor
  · rw [rhoN, le_div_iff₀ hZp]
    calc Real.exp (-(2 * B)) * ZN Q n ≤ Real.exp (-(2 * B)) * Real.exp B :=
          mul_le_mul_of_nonneg_left hZ.2 (Real.exp_pos _).le
      _ = Real.exp (-B) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-QN Q n y) := Real.exp_le_exp.mpr (by linarith)
  · rw [rhoN, div_le_iff₀ hZp]
    calc Real.exp (-QN Q n y) ≤ Real.exp B := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (2 * B) * Real.exp (-B) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (2 * B) * ZN Q n := mul_le_mul_of_nonneg_left hZ.1 (Real.exp_pos _).le

theorem goodDens_rhoN (n : ℕ) : GoodDens (rhoN Q n) (Real.exp (-(2 * B))) (Real.exp (2 * B)) where
  meas := ((continuous_QN hQc hB n).neg.rexp.div_const _).measurable
  pos := Real.exp_pos _
  lower y := (rhoN_bounds hQc hB n y).1
  upper y := (rhoN_bounds hQc hB n y).2
  one := by
    simp only [rhoN]
    rw [integral_div]
    exact div_self (ZN_pos hQc hB n).ne'

theorem contDiff_rhoN (n : ℕ) : ContDiff ℝ ∞ (rhoN Q n ∘ liftT) := by
  have : rhoN Q n ∘ liftT = fun x => Real.exp (-(QN Q n ∘ liftT) x) / ZN Q n := rfl
  rw [this]
  exact ((contDiff_QN hQc hB n).neg.exp).div_const _

theorem negLog_rhoN (n : ℕ) :
    (fun z => -Real.log (rhoN Q n (liftT z))) = fun z => (QN Q n ∘ liftT) z + Real.log (ZN Q n) := by
  funext z
  simp only [rhoN, Function.comp]
  rw [Real.log_div (Real.exp_ne_zero _) (ZN_pos hQc hB n).ne', Real.log_exp]
  ring

theorem tendsto_QN (y : Torus d) : Tendsto (fun n => QN Q n y) atTop (𝓝 (Q y)) := by
  have h := tendsto_mollL_apply hQc (secT y)
  rw [liftT_secT] at h
  refine h.congr fun n => ?_
  simp only [QN]
  rw [← moll_comp_liftT]; simp [Function.comp, liftT_secT]

theorem tendsto_ZN : Tendsto (fun n => ZN Q n) atTop (𝓝 (∫ y, Real.exp (-Q y))) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp B)
    (fun n => (continuous_QN hQc hB n).neg.rexp.aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (QN Q n y), abs_QN_le hQc hB n y])
  · exact (Real.continuous_exp.tendsto _).comp (tendsto_QN hQc hB y).neg

theorem tendsto_rhoN (hZ : ∫ y, Real.exp (-Q y) = 1) (y : Torus d) :
    Tendsto (fun n => rhoN Q n y) atTop (𝓝 (Real.exp (-Q y))) := by
  have h := ((Real.continuous_exp.tendsto _).comp (tendsto_QN hQc hB y).neg).div
    (tendsto_ZN hQc hB) (by rw [hZ]; exact one_ne_zero)
  rw [hZ, div_one] at h
  exact h

end dens

end SharpLSI
