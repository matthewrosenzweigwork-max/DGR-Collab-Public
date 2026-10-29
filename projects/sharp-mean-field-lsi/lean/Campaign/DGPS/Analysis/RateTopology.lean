import DGPS.Model.ScalarRate
import DGPS.Model.SpeciesRate
import DGPS.Model.Drift
import DGPS.Foundations.SobolevEmbedding
import DGPS.Foundations.SmoothingLp

/-!
# Rate-defined ambient subspaces for each topology (SEM001)

`K` is the class of continuous symmetric zero-diagonal `W` on `𝕋²` (encoded as `Torus 2`, the pair
`(x, y)` being `pairPt x y`) lying in `W^{1,1}(𝕋²)`, with `V = 0`.

* `weakGradient_convolution_core`: for continuous `ρ` the function `x ↦ ∫ W(x,y) ρ(y) dy` has the
  `L¹` weak gradient `x ↦ ∫ ∂ₓW(x,y) ρ(y) dy` (Fubini against tensor test functions
  `φ(x) ψₙ(y)` with `ψₙ = moll n ρ → ρ` uniformly).
* `exists_cont_density`: in one dimension `H¹ ⊆ C^{0,1/2}`, so an absolute density `ρ = u²` has a
  bounded continuous representative; hence `exists_force`: every absolute-admissible `ρ` has an
  `L¹` weak force, giving the canonical provider `RoughKernelClass.drift`. Barycenters of species
  families are absolute densities, so the finite-species force is the same provider.
* `scalarRate_eq_of_providers`, `speciesRate_eq_of_providers`: the extended rates do not depend
  on the provider.
* `K_α`, `K_p` carry the topology induced by an injective embedding into a normed space
  (`holderEmbed`: `ℓ^∞ × ℓ^∞`, `sobolevEmbed`: `L^p × L^p`); injectivity for `W^{1,p}` is the fact
  that continuous functions equal a.e. are equal.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Analysis.RateTopology

/-- First and second coordinate of `Torus 2` as points of `Torus 1`. -/
def q1 (p : Torus 2) : Torus 1 := fun _ => p 0
def q2 (p : Torus 2) : Torus 1 := fun _ => p 1

def pairPt (x y : Torus 1) : Torus 2 := fun i => if i = 0 then x 0 else y 0

theorem q1_pairPt (x y : Torus 1) : q1 (pairPt x y) = x := by
  funext i; simp [q1, pairPt, Subsingleton.elim i 0]

theorem q2_pairPt (x y : Torus 1) : q2 (pairPt x y) = y := by
  funext i; simp [q2, pairPt, Subsingleton.elim i 0]

theorem pairPt_q (p : Torus 2) : pairPt (q1 p) (q2 p) = p := by
  funext i; fin_cases i <;> simp [pairPt, q1, q2]

theorem measurable_q1 : Measurable q1 := measurable_pi_iff.mpr fun _ => measurable_pi_apply 0
theorem measurable_q2 : Measurable q2 := measurable_pi_iff.mpr fun _ => measurable_pi_apply 1
theorem measurable_pairPt : Measurable (fun z : Torus 1 × Torus 1 => pairPt z.1 z.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · simp only [pairPt]; exact (measurable_pi_apply (0 : Fin 1)).comp measurable_fst
  · simp only [pairPt]; exact (measurable_pi_apply (0 : Fin 1)).comp measurable_snd

theorem measurePreserving_q : MeasurePreserving (fun p : Torus 2 => (q1 p, q2 p))
    (haar 2) ((haar 1).prod (haar 1)) := by
  set μ : Measure (AddCircle (1:ℝ)) := AddCircle.haarAddCircle with hμ
  have h2 : haar 2 = Measure.pi fun _ : Fin 2 => μ := haar_eq_pi_haarAddCircle 2
  have h1 : haar 1 = Measure.pi fun _ : Fin 1 => μ := haar_eq_pi_haarAddCircle 1
  have A := measurePreserving_piFinTwo (fun _ : Fin 2 => μ)
  have D := (measurePreserving_funUnique μ (Fin 1)).symm
  have E := D.prod D
  have F := E.comp A
  rw [h2, h1]
  have hf : (fun p : Fin 2 → AddCircle (1:ℝ) => (q1 p, q2 p)) =
      (Prod.map (MeasurableEquiv.funUnique (Fin 1) (AddCircle (1:ℝ))).symm
        (MeasurableEquiv.funUnique (Fin 1) (AddCircle (1:ℝ))).symm) ∘
      (MeasurableEquiv.piFinTwo fun _ : Fin 2 => AddCircle (1:ℝ)) := by
    funext p
    simp [MeasurableEquiv.piFinTwo, MeasurableEquiv.funUnique]
    refine ⟨?_, ?_⟩ <;> funext i <;> simp [q1, q2, Subsingleton.elim i 0]
  rw [hf]; exact F

/-- `Torus 2 ≃ᵐ Torus 1 × Torus 1`. -/
def pairEquiv : Torus 2 ≃ᵐ Torus 1 × Torus 1 where
  toFun p := (q1 p, q2 p)
  invFun z := pairPt z.1 z.2
  left_inv p := pairPt_q p
  right_inv z := by ext <;> simp [q1_pairPt, q2_pairPt]
  measurable_toFun := measurable_q1.prodMk measurable_q2
  measurable_invFun := measurable_pairPt

theorem integral_torus2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Torus 2 → E) :
    ∫ z, F (pairPt z.1 z.2) ∂(haar 1).prod (haar 1) = ∫ p, F p ∂haar 2 := by
  have h := measurePreserving_q.integral_comp' (f := pairEquiv) (g := fun z => F (pairPt z.1 z.2))
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp [pairEquiv, pairPt_q]

theorem integrable_torus2 {E : Type*} [NormedAddCommGroup E] (F : Torus 2 → E) :
    Integrable (fun z : Torus 1 × Torus 1 => F (pairPt z.1 z.2)) ((haar 1).prod (haar 1)) ↔
      Integrable F (haar 2) := by
  have h := measurePreserving_q.integrable_comp_emb (f := pairEquiv) pairEquiv.measurableEmbedding
    (g := fun z : Torus 1 × Torus 1 => F (pairPt z.1 z.2))
  rw [← h]
  refine integrable_congr (Eventually.of_forall fun p => ?_)
  simp [pairEquiv, pairPt_q]

/-- Coordinate projections of `ℝ²` to `ℝ¹`. -/
noncomputable def pr (k : Fin 2) : (Fin 2 → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj k

theorem q1_lift (v : Fin 2 → ℝ) : q1 (torusLift v) = torusLift (pr 0 v) := by
  funext i; simp [q1, torusLift, SharpLSI.liftT, pr]

theorem q2_lift (v : Fin 2 → ℝ) : q2 (torusLift v) = torusLift (pr 1 v) := by
  funext i; simp [q2, torusLift, SharpLSI.liftT, pr]

theorem tensor_aux {φ ψ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) (hψ : IsSmoothPeriodic ψ) :
    IsSmoothPeriodic (fun p : Torus 2 => φ (q1 p) * ψ (q2 p)) ∧
    ∀ p, coordPartial 0 (fun p : Torus 2 => φ (q1 p) * ψ (q2 p)) p =
      coordPartial 0 φ (q1 p) * ψ (q2 p) := by
  have hG : ((fun p : Torus 2 => φ (q1 p) * ψ (q2 p)) ∘ torusLift)
      = fun v => (φ ∘ torusLift) (pr 0 v) * (ψ ∘ torusLift) (pr 1 v) := by
    funext v; simp [q1_lift, q2_lift]
  refine ⟨?_, ?_⟩
  · unfold IsSmoothPeriodic
    rw [hG]
    exact (hφ.comp (pr 0).contDiff).mul (hψ.comp (pr 1).contDiff)
  · intro x
    obtain ⟨v, rfl⟩ : ∃ v : Fin 2 → ℝ, x = torusLift v :=
      ⟨SharpLSI.secT x, (SharpLSI.liftT_secT x).symm⟩
    have h1 := (hφ.differentiable (by simp) (pr 0 v)).hasFDerivAt.comp v (pr 0).hasFDerivAt
    have h2 := (hψ.differentiable (by simp) (pr 1 v)).hasFDerivAt.comp v (pr 1).hasFDerivAt
    have H := h1.mul h2
    have e1 := congrFun (coordPartial_comp_torusLift (d := 2) 0
      (fun p : Torus 2 => φ (q1 p) * ψ (q2 p))) v
    have e2 := congrFun (coordPartial_comp_torusLift (d := 1) 0 φ) (pr 0 v)
    replace e1 : coordPartial 0 (fun p : Torus 2 => φ (q1 p) * ψ (q2 p)) (torusLift v) = _ := e1
    replace e2 : coordPartial 0 φ (torusLift (pr 0 v)) = _ := e2
    have H' : HasFDerivAt (fun v => (φ ∘ torusLift) (pr 0 v) * (ψ ∘ torusLift) (pr 1 v)) _ v := H
    rw [e1, hG, H'.fderiv, q1_lift, q2_lift, e2]
    have p0 : pr 0 (Pi.single 0 1) = Pi.single 0 1 := by
      funext i; rw [Subsingleton.elim i 0]; simp [pr]
    have p1 : pr 1 (Pi.single 0 1) = 0 := by
      funext i; simp [pr]
    simp [p0, p1, mul_comm]


theorem identity_smooth {W : Torus 1 → Torus 1 → ℝ} {G : Torus 2 → Tangent 2}
    (hG : IsWeakGradientLp 1 (fun p : Torus 2 => W (q1 p) (q2 p)) G)
    {φ ψ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) (hψ : IsSmoothPeriodic ψ) :
    ∫ z : Torus 1 × Torus 1, W z.1 z.2 * (coordPartial 0 φ z.1 * ψ z.2)
        ∂(haar 1).prod (haar 1) =
      -∫ z : Torus 1 × Torus 1, G (pairPt z.1 z.2) 0 * (φ z.1 * ψ z.2)
        ∂(haar 1).prod (haar 1) := by
  obtain ⟨hs, hd⟩ := tensor_aux hφ hψ
  have h := hG.ibp _ hs 0
  have e1 := integral_torus2 (fun p : Torus 2 =>
    W (q1 p) (q2 p) * coordPartial 0 (fun p : Torus 2 => φ (q1 p) * ψ (q2 p)) p)
  have e2 := integral_torus2 (fun p : Torus 2 => G p 0 * (fun p : Torus 2 => φ (q1 p) * ψ (q2 p)) p)
  simp only [hd, q1_pairPt, q2_pairPt] at e1 e2
  simp only [hd] at h
  rw [e1, e2]
  exact h


theorem abs_integral_mul_le {μ : Measure (Torus 1 × Torus 1)} {f : Torus 1 × Torus 1 → ℝ}
    (hf : Integrable f μ) {h : Torus 1 → ℝ} {δ : ℝ} (hh : ∀ y, |h y| ≤ δ)
    :
    |∫ z, f z * h z.2 ∂μ| ≤ δ * ∫ z, |f z| ∂μ := by
  have := norm_integral_le_of_norm_le (μ := μ) (f := fun z => f z * h z.2)
    (g := fun z => δ * |f z|) (hf.abs.const_mul δ) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hh z.2) (abs_nonneg _))
  rwa [integral_const_mul, Real.norm_eq_abs] at this

theorem approx_eq {μ : Measure (Torus 1 × Torus 1)} [IsFiniteMeasure μ]
    {f1 f2 : Torus 1 × Torus 1 → ℝ}
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    {ρ : Torus 1 → ℝ} (hρ : Continuous ρ)
    (H : ∀ δ > 0, ∃ ψ : Torus 1 → ℝ, Continuous ψ ∧
      (∫ z, f1 z * ψ z.2 ∂μ = -∫ z, f2 z * ψ z.2 ∂μ) ∧ ∀ y, |ψ y - ρ y| ≤ δ) :
    ∫ z, f1 z * ρ z.2 ∂μ = -∫ z, f2 z * ρ z.2 ∂μ := by
  have hint : ∀ (f : Torus 1 × Torus 1 → ℝ), Integrable f μ → ∀ g : Torus 1 → ℝ, Continuous g →
      Integrable (fun z : Torus 1 × Torus 1 => f z * g z.2) μ := by
    intro f hf g hg
    obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hg.continuousOn
    refine hf.mul_bdd (c := C) ?_ (Eventually.of_forall fun z => ?_)
    · exact (hg.comp continuous_snd).aestronglyMeasurable
    · simpa using hC z.2 (Set.mem_univ _)
  set S := ∫ z, |f1 z| ∂μ + ∫ z, |f2 z| ∂μ with hS
  have hS0 : 0 ≤ S := add_nonneg (integral_nonneg fun _ => abs_nonneg _)
    (integral_nonneg fun _ => abs_nonneg _)
  set D := ∫ z, f1 z * ρ z.2 ∂μ + ∫ z, f2 z * ρ z.2 ∂μ with hD
  have hle : ∀ δ > 0, |D| ≤ δ * S := by
    intro δ hδ
    obtain ⟨ψ, hψc, hψ, hψρ⟩ := H δ hδ
    have hdc : Continuous fun y => ψ y - ρ y := hψc.sub hρ
    have a1 : ∫ z, f1 z * (ψ z.2 - ρ z.2) ∂μ = ∫ z, f1 z * ψ z.2 ∂μ - ∫ z, f1 z * ρ z.2 ∂μ := by
      rw [← integral_sub (hint f1 h1 ψ hψc) (hint f1 h1 ρ hρ)]
      exact integral_congr_ae (Eventually.of_forall fun z => by simp only; ring)
    have a2 : ∫ z, f2 z * (ψ z.2 - ρ z.2) ∂μ = ∫ z, f2 z * ψ z.2 ∂μ - ∫ z, f2 z * ρ z.2 ∂μ := by
      rw [← integral_sub (hint f2 h2 ψ hψc) (hint f2 h2 ρ hρ)]
      exact integral_congr_ae (Eventually.of_forall fun z => by simp only; ring)
    have b1 := abs_integral_mul_le h1 (h := fun y => ψ y - ρ y) hψρ 
    have b2 := abs_integral_mul_le h2 (h := fun y => ψ y - ρ y) hψρ 
    have : D = -(∫ z, f1 z * (ψ z.2 - ρ z.2) ∂μ + ∫ z, f2 z * (ψ z.2 - ρ z.2) ∂μ) := by
      rw [a1, a2, hD]; linarith
    rw [this, abs_neg]
    refine (abs_add_le _ _).trans ?_
    rw [hS]; linarith
  have : D = 0 := by
    by_contra hne
    have hpos : 0 < |D| := abs_pos.mpr hne
    have := hle (|D| / (2 * (S + 1))) (by positivity)
    have h3 : |D| / (2 * (S + 1)) * S < |D| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  linarith


theorem continuous_single1 : Continuous (fun t : ℝ => (EuclideanSpace.single 0 t : Tangent 1)) :=
  (by
    have : (fun t : ℝ => (EuclideanSpace.single (0 : Fin 1) t : Tangent 1)) =
        fun t => t • (EuclideanSpace.single (0 : Fin 1) (1:ℝ) : Tangent 1) := by
      funext t; ext i; simp [PiLp.single_apply]
    rw [this]; exact continuous_id.smul continuous_const)

theorem integrable_G {G : Torus 2 → Tangent 2} {W : Torus 1 → Torus 1 → ℝ}
    (hG : IsWeakGradientLp 1 (fun p : Torus 2 => W (q1 p) (q2 p)) G) :
    Integrable (fun z : Torus 1 × Torus 1 => G (pairPt z.1 z.2) 0) ((haar 1).prod (haar 1)) := by
  rw [integrable_torus2 (fun p => G p 0)]
  exact (memLp_coord_of_memLp hG.memLp_grad 0).integrable le_rfl

theorem identity_cont {W : Torus 1 → Torus 1 → ℝ} {G : Torus 2 → Tangent 2}
    (hWc : Continuous fun p : Torus 1 × Torus 1 => W p.1 p.2)
    (hG : IsWeakGradientLp 1 (fun p : Torus 2 => W (q1 p) (q2 p)) G)
    {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) {ρ : Torus 1 → ℝ} (hρ : Continuous ρ) :
    ∫ z : Torus 1 × Torus 1, W z.1 z.2 * (coordPartial 0 φ z.1 * ρ z.2)
        ∂(haar 1).prod (haar 1) =
      -∫ z : Torus 1 × Torus 1, G (pairPt z.1 z.2) 0 * (φ z.1 * ρ z.2)
        ∂(haar 1).prod (haar 1) := by
  have hf1 : Integrable (fun z : Torus 1 × Torus 1 => W z.1 z.2 * coordPartial 0 φ z.1)
      ((haar 1).prod (haar 1)) :=
    (hWc.mul ((hφ.continuous_coordPartial 0).comp continuous_fst)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨Kφ, hKφ⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn
    hφ.continuous_torus.continuousOn
  have hf2 : Integrable (fun z : Torus 1 × Torus 1 => G (pairPt z.1 z.2) 0 * φ z.1)
      ((haar 1).prod (haar 1)) :=
    (integrable_G hG).mul_bdd (c := Kφ) (hφ.continuous_torus.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa using hKφ z.1 (Set.mem_univ _))
  have := approx_eq hf1 hf2 hρ (fun δ hδ => by
    have hρi : Integrable ρ (haar 1) :=
      hρ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    obtain ⟨n, hn⟩ := (SharpLSI.moll_uniform_of_continuous hρ hδ).exists
    refine ⟨SharpLSI.moll n ρ, (isSmoothPeriodic_moll n hρi).continuous_torus, ?_, fun y => ?_⟩
    · have := identity_smooth hG hφ (isSmoothPeriodic_moll n hρi)
      simpa only [mul_assoc] using this
    · simpa [Real.dist_eq] using hn y)
  simpa only [mul_assoc] using this


theorem weakGradient_convolution_core {W : Torus 1 → Torus 1 → ℝ} {G : Torus 2 → Tangent 2}
    (hWc : Continuous fun p : Torus 1 × Torus 1 => W p.1 p.2)
    (hG : IsWeakGradientLp 1 (fun p : Torus 2 => W (q1 p) (q2 p)) G)
    {ρ : Torus 1 → ℝ} (hρ : Continuous ρ) :
    IsWeakGradientLp 1 (fun x => ∫ y, W x y * ρ y ∂haar 1)
      (fun x => (EuclideanSpace.single 0 (∫ y, G (pairPt x y) 0 * ρ y ∂haar 1) : Tangent 1)) := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus 1 × Torus 1)).exists_bound_of_continuousOn
    hWc.continuousOn
  obtain ⟨Mρ, hMρ⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn
    hρ.continuousOn
  have hρi : Integrable ρ (haar 1) :=
    hρ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hBi := integrable_G hG
  have hBρ : Integrable (fun z : Torus 1 × Torus 1 => G (pairPt z.1 z.2) 0 * ρ z.2)
      ((haar 1).prod (haar 1)) :=
    hBi.mul_bdd (c := Mρ) (hρ.comp continuous_snd).aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa using hMρ z.2 (Set.mem_univ _))
  have hu_meas : AEStronglyMeasurable (fun x => ∫ y, W x y * ρ y ∂haar 1) (haar 1) := by
    have : AEStronglyMeasurable (fun p : Torus 1 × Torus 1 => W p.1 p.2 * ρ p.2)
        ((haar 1).prod (haar 1)) := (hWc.mul (hρ.comp continuous_snd)).aestronglyMeasurable
    exact this.integral_prod_right'
  have hu : MemLp (fun x => ∫ y, W x y * ρ y ∂haar 1) 1 (haar 1) := by
    have : MemLp (fun x => ∫ y, W x y * ρ y ∂haar 1) ∞ (haar 1) := by
      refine memLp_top_of_bound hu_meas (C * Mρ) (Eventually.of_forall fun x => ?_)
      have h := norm_integral_le_of_norm_le_const (μ := haar 1) (f := fun y => W x y * ρ y)
        (C := C * Mρ) (Eventually.of_forall fun y => by
          rw [norm_mul]
          have h1 : ‖W x y‖ ≤ C := by simpa using hC (x, y) (Set.mem_univ _)
          have h2 : ‖ρ y‖ ≤ Mρ := by simpa using hMρ y (Set.mem_univ _)
          exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))
      simpa using h
    exact this.mono_exponent le_top
  have hc : Integrable (fun x => ∫ y, G (pairPt x y) 0 * ρ y ∂haar 1) (haar 1) :=
    hBρ.integral_prod_left
  have hg : MemLp (fun x => (EuclideanSpace.single 0 (∫ y, G (pairPt x y) 0 * ρ y ∂haar 1) :
      Tangent 1)) 1 (haar 1) := by
    rw [memLp_one_iff_integrable]
    refine Integrable.mono' hc.norm ?_ (Eventually.of_forall fun x => by simp)
    exact ((continuous_single1).comp_aestronglyMeasurable hc.aestronglyMeasurable)
  refine ⟨hu, hg, fun φ hφ j => ?_⟩
  rw [Subsingleton.elim j 0]
  have key := identity_cont hWc hG hφ hρ
  obtain ⟨Kφ, hKφ⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn
    hφ.continuous_torus.continuousOn
  have hF1 : Integrable (fun z : Torus 1 × Torus 1 => W z.1 z.2 * (coordPartial 0 φ z.1 * ρ z.2))
      ((haar 1).prod (haar 1)) :=
    (hWc.mul (((hφ.continuous_coordPartial 0).comp continuous_fst).mul
      (hρ.comp continuous_snd))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hF2 : Integrable (fun z : Torus 1 × Torus 1 => G (pairPt z.1 z.2) 0 * (φ z.1 * ρ z.2))
      ((haar 1).prod (haar 1)) := by
    refine (hBi.mul_bdd (c := Kφ * Mρ)
      ((hφ.continuous_torus.comp continuous_fst).mul
        (hρ.comp continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_))
    rw [norm_mul]
    have h1 : ‖φ z.1‖ ≤ Kφ := by simpa using hKφ z.1 (Set.mem_univ _)
    have h2 : ‖ρ z.2‖ ≤ Mρ := by simpa using hMρ z.2 (Set.mem_univ _)
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  rw [integral_prod _ hF1, integral_prod _ hF2] at key
  have l1 : ∫ x, (∫ y, W x y * ρ y ∂haar 1) * coordPartial 0 φ x ∂haar 1 =
      ∫ x, ∫ y, W x y * (coordPartial 0 φ x * ρ y) ∂haar 1 ∂haar 1 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)
  have l2 : ∫ x, (EuclideanSpace.single 0 (∫ y, G (pairPt x y) 0 * ρ y ∂haar 1) : Tangent 1) 0 *
      φ x ∂haar 1 = ∫ x, ∫ y, G (pairPt x y) 0 * (φ x * ρ y) ∂haar 1 ∂haar 1 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [PiLp.single_apply, ite_true]
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)
  rw [l1, l2]
  exact key


theorem weakGradientLp_congr {d : ℕ} {p : ℝ≥0∞} {u : Torus d → ℝ} {g g' : Torus d → Tangent d}
    (h : IsWeakGradientLp p u g) (hae : g =ᵐ[haar d] g') : IsWeakGradientLp p u g' := by
  refine ⟨h.memLp, h.memLp_grad.ae_eq hae, fun φ hφ j => ?_⟩
  rw [h.ibp φ hφ j]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

theorem continuous_pairPt : Continuous (fun z : Torus 1 × Torus 1 => pairPt z.1 z.2) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [pairPt]; exact (continuous_apply (0 : Fin 1)).comp continuous_fst
  · simp only [pairPt]; exact (continuous_apply (0 : Fin 1)).comp continuous_snd

/-- The rough kernel class `K`: continuous symmetric zero-diagonal `W` on `𝕋²` (encoded as
`Torus 2`) lying in `W^{1,1}(𝕋²)`. -/
structure RoughKernelClass where
  W : Torus 2 → ℝ
  continuous : Continuous W
  symm : ∀ x y : Torus 1, W (pairPt x y) = W (pairPt y x)
  diag : ∀ x : Torus 1, W (pairPt x x) = 0
  sobolev : ∃ G : Torus 2 → Tangent 2, IsWeakGradientLp 1 W G

/-- The kernel as a function of two points of the circle. -/
def RoughKernelClass.kernel (K : RoughKernelClass) (x y : Torus 1) : ℝ := K.W (pairPt x y)

theorem RoughKernelClass.continuous_kernel (K : RoughKernelClass) :
    Continuous (fun z : Torus 1 × Torus 1 => K.kernel z.1 z.2) :=
  K.continuous.comp continuous_pairPt

/-- The interaction data (with `V = 0`) of a rough kernel. -/
def RoughKernelClass.toInteraction (K : RoughKernelClass) : InteractionData 1 where
  V := fun _ => 0
  W := K.kernel
  V_continuous := continuous_const
  W_continuous := K.continuous_kernel
  W_symm := K.symm
  W_diag := K.diag

theorem RoughKernelClass.kernel_q (K : RoughKernelClass) :
    (fun p : Torus 2 => K.kernel (q1 p) (q2 p)) = K.W := by
  funext p; simp [RoughKernelClass.kernel, pairPt_q]

/-- A continuous representative of the density of an absolute-admissible density on the circle. -/
theorem exists_cont_density (ρ : AbsoluteDensity 1) :
    ∃ r : Torus 1 → ℝ, Continuous r ∧ (fun y => ρ.density y) =ᵐ[haar 1] r := by
  obtain ⟨g, hg⟩ := ρ.sqrt_mem
  obtain ⟨w, hwc, hwae, -⟩ := sobolev_embedding_dim_one hg
  refine ⟨fun y => w y ^ 2, hwc.pow 2, ?_⟩
  filter_upwards [hwae] with y hy
  simp [AbsoluteDensity.density, hy]

theorem interactionPotential_eq_cont (K : RoughKernelClass) (ρ : AbsoluteDensity 1)
    {r : Torus 1 → ℝ} (hr : (fun y => ρ.density y) =ᵐ[haar 1] r) (x : Torus 1) :
    interactionPotential K.toInteraction ρ x = ∫ y, K.kernel x y * r y ∂haar 1 := by
  rw [interactionPotential_eq]
  simp only [RoughKernelClass.toInteraction, zero_add]
  refine integral_congr_ae ?_
  filter_upwards [hr] with y hy
  rw [hy, mul_comm]

/-- Force existence: for every `W ∈ K` and every absolute-admissible `ρ` the weak force is an
`L¹` function, a measurable weak gradient of the interaction potential. -/
theorem exists_force (K : RoughKernelClass) (ρ : AbsoluteDensity 1) :
    ∃ g : Torus 1 → Tangent 1, Measurable g ∧
      IsWeakGradientLp 1 (interactionPotential K.toInteraction ρ) g := by
  obtain ⟨G, hG⟩ := K.sobolev
  obtain ⟨r, hrc, hr⟩ := exists_cont_density ρ
  have hG' : IsWeakGradientLp 1 (fun p : Torus 2 => K.kernel (q1 p) (q2 p)) G := by
    rw [K.kernel_q]; exact hG
  have core := weakGradient_convolution_core K.continuous_kernel hG' hrc
  have hpot : interactionPotential K.toInteraction ρ = fun x => ∫ y, K.kernel x y * r y ∂haar 1 := by
    funext x; exact interactionPotential_eq_cont K ρ hr x
  rw [hpot]
  have hm := core.memLp_grad.aestronglyMeasurable
  refine ⟨hm.mk _, hm.stronglyMeasurable_mk.measurable, ?_⟩
  exact weakGradientLp_congr core hm.ae_eq_mk

/-- The canonical weak-drift provider of a rough kernel. -/
noncomputable def RoughKernelClass.drift (K : RoughKernelClass) : AbsoluteDrift K.toInteraction where
  force := fun ρ => Classical.choose (exists_force K ρ)
  measurable_force := fun ρ => (Classical.choose_spec (exists_force K ρ)).1
  weak_gradient := fun ρ => (Classical.choose_spec (exists_force K ρ)).2


/-! ### Canonicity of the rates -/

theorem scalarRate_eq_of_providers {A : InteractionData 1} (b b' : AbsoluteDrift A) :
    scalarRate A b = scalarRate A b' := by
  unfold scalarRate
  refine iInf_congr fun ρ => ?_
  unfold scalarQuotient scalarDissipation
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [absoluteDrift_unique b b' ρ.1] with x hx
  simp only [scalarScore, hx]

theorem speciesRate_eq_of_providers {A : InteractionData 1} (b b' : AbsoluteDrift A) :
    speciesRate A b = speciesRate A b' := by
  unfold speciesRate
  refine iInf_congr fun F => ?_
  unfold speciesQuotient speciesDissipation
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [absoluteDrift_unique b b' (barycenter F.1)] with x hx
  simp only [hx]

/-! ### The subclasses `K_α` and `K_p` -/

@[ext] theorem RoughKernelClass.ext' {K K' : RoughKernelClass} (h : K.W = K'.W) : K = K' := by
  cases K; cases K'; simp only at h; subst h; rfl

/-- `K_α = {W ∈ K : W ∈ C^α}`. -/
def HolderKernel (α : ℝ≥0) : Type := {K : RoughKernelClass // ∃ C : ℝ≥0, HolderWith C α K.W}

/-- `K_p = {W ∈ K : W ∈ W^{1,p}}`. -/
def SobolevKernel (p : ℝ≥0∞) : Type := {K : RoughKernelClass // ∃ G, IsWeakGradientLp p K.W G}

/-- The Hölder quotient of a function on `𝕋²`. -/
noncomputable def holderQuotient (α : ℝ≥0) (f : Torus 2 → ℝ) (z : Torus 2 × Torus 2) : ℝ :=
  (f z.1 - f z.2) / dist z.1 z.2 ^ (α : ℝ)

theorem holderQuotient_bound {α : ℝ≥0} {f : Torus 2 → ℝ} {C : ℝ≥0} (h : HolderWith C α f)
    (z : Torus 2 × Torus 2) : ‖holderQuotient α f z‖ ≤ C := by
  unfold holderQuotient
  by_cases hz : z.1 = z.2
  · simp [hz]
  · have hd : 0 < dist z.1 z.2 := dist_pos.mpr hz
    have hpos : 0 < dist z.1 z.2 ^ (α : ℝ) := Real.rpow_pos_of_pos hd _
    rw [norm_div, Real.norm_of_nonneg hpos.le, div_le_iff₀ hpos]
    simpa [Real.dist_eq] using h.dist_le z.1 z.2

/-- The `C^α` norm embedding `W ↦ (W, [W]_α-quotient)` into a sup-normed product (`ℓ^∞ × ℓ^∞`). -/
noncomputable def holderEmbed (α : ℝ≥0) (K : HolderKernel α) :
    lp (fun _ : Torus 2 => ℝ) ∞ × lp (fun _ : Torus 2 × Torus 2 => ℝ) ∞ :=
  (⟨K.1.W, memℓp_infty (by
      obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus 2)).exists_bound_of_continuousOn
        K.1.continuous.continuousOn
      exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x (Set.mem_univ _)⟩)⟩,
   ⟨holderQuotient α K.1.W, memℓp_infty (by
      obtain ⟨C, hC⟩ := K.2
      exact ⟨C, by rintro _ ⟨z, rfl⟩; exact holderQuotient_bound hC z⟩)⟩)

/-- The `C^α` norm topology on `K_α` (subspace of the ambient class `K`). -/
noncomputable abbrev holderTopology (α : ℝ≥0) : TopologicalSpace (HolderKernel α) :=
  TopologicalSpace.induced (holderEmbed α) inferInstance

theorem holderEmbed_injective (α : ℝ≥0) : Function.Injective (holderEmbed α) := by
  intro K K' h
  have h1 : K.1.W = K'.1.W := congrArg (fun z => (z.1 : Torus 2 → ℝ)) h
  exact Subtype.ext (RoughKernelClass.ext' h1)

theorem holderEmbed_isEmbedding (α : ℝ≥0) :
    @Topology.IsEmbedding _ _ (holderTopology α) _ (holderEmbed α) :=
  @Topology.IsEmbedding.mk _ _ (holderTopology α) _ _
    (@Topology.IsInducing.mk _ _ (holderTopology α) _ _ rfl) (holderEmbed_injective α)

/-- The `W^{1,p}` norm embedding `W ↦ (W, ∇W)` into `L^p × L^p`. -/
noncomputable def sobolevEmbed (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : SobolevKernel p) :
    Lp ℝ p (haar 2) × Lp (Tangent 2) p (haar 2) :=
  ((Classical.choose_spec K.2).memLp.toLp K.1.W,
   (Classical.choose_spec K.2).memLp_grad.toLp (Classical.choose K.2))

/-- The `W^{1,p}` norm topology on `K_p` (subspace of the ambient class `K`). -/
noncomputable abbrev sobolevTopology (p : ℝ≥0∞) [Fact (1 ≤ p)] : TopologicalSpace (SobolevKernel p) :=
  TopologicalSpace.induced (sobolevEmbed p) inferInstance

/-- Continuous functions equal a.e. are equal: the `W^{1,p}` norm is a norm on `K_p`. -/
theorem sobolevEmbed_injective (p : ℝ≥0∞) [Fact (1 ≤ p)] : Function.Injective (sobolevEmbed p) := by
  intro K K' h
  have h1 := congrArg (fun z => (z.1 : Lp ℝ p (haar 2))) h
  simp only [sobolevEmbed] at h1
  have hae : K.1.W =ᵐ[haar 2] K'.1.W :=
    (MemLp.coeFn_toLp _).symm.trans ((Lp.ext_iff.mp h1).trans (MemLp.coeFn_toLp _))
  have hW : K.1.W = K'.1.W :=
    (Continuous.ae_eq_iff_eq (haar 2) K.1.continuous K'.1.continuous).mp hae
  exact Subtype.ext (RoughKernelClass.ext' hW)

theorem sobolevEmbed_isEmbedding (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    @Topology.IsEmbedding _ _ (sobolevTopology p) _ (sobolevEmbed p) :=
  @Topology.IsEmbedding.mk _ _ (sobolevTopology p) _ _
    (@Topology.IsInducing.mk _ _ (sobolevTopology p) _ _ rfl) (sobolevEmbed_injective p)


/-- Explicit formula for the force of the canonical provider. -/
theorem drift_force_formula (K : RoughKernelClass) (ρ : AbsoluteDensity 1) :
    ∃ (G : Torus 2 → Tangent 2) (r : Torus 1 → ℝ), IsWeakGradientLp 1 K.W G ∧ Continuous r ∧
      (fun y => ρ.density y) =ᵐ[haar 1] r ∧
      K.drift.force ρ =ᵐ[haar 1]
        fun x => (EuclideanSpace.single 0 (∫ y, G (pairPt x y) 0 * r y ∂haar 1) : Tangent 1) := by
  obtain ⟨G, hG⟩ := K.sobolev
  obtain ⟨r, hrc, hr⟩ := exists_cont_density ρ
  have hG' : IsWeakGradientLp 1 (fun p : Torus 2 => K.kernel (q1 p) (q2 p)) G := by
    rw [K.kernel_q]; exact hG
  have core := weakGradient_convolution_core K.continuous_kernel hG' hrc
  have hpot : interactionPotential K.toInteraction ρ = fun x => ∫ y, K.kernel x y * r y ∂haar 1 := by
    funext x; exact interactionPotential_eq_cont K ρ hr x
  rw [← hpot] at core
  exact ⟨G, r, hG, hrc, hr, K.drift.ae_eq_of_isWeakGradient ρ core⟩

/-- `W^{1,p} ⊆ W^{1,1}` on the torus (probability measure), so the `W^{1,p}` condition on a
continuous symmetric zero-diagonal kernel already places it in `K`. -/
theorem mem_K_of_sobolev {p : ℝ≥0∞} (hp : 1 ≤ p) {W : Torus 2 → ℝ} (hc : Continuous W)
    (hs : ∀ x y : Torus 1, W (pairPt x y) = W (pairPt y x)) (hd : ∀ x : Torus 1, W (pairPt x x) = 0)
    {G : Torus 2 → Tangent 2} (hG : IsWeakGradientLp p W G) :
    ∃ K : RoughKernelClass, K.W = W ∧ ∃ G', IsWeakGradientLp p K.W G' :=
  ⟨⟨W, hc, hs, hd, ⟨G, hG.memLp.mono_exponent hp, hG.memLp_grad.mono_exponent hp, hG.ibp⟩⟩, rfl,
    G, hG⟩

/-- Step 1 of the proof decomposition: `L¹` bound of the force integral. -/
theorem integral_norm_convolution_le {B : Torus 1 → Torus 1 → ℝ} {ρ : Torus 1 → ℝ} {M : ℝ}
    (hB : Integrable (fun p : Torus 1 × Torus 1 => B p.1 p.2) ((haar 1).prod (haar 1)))
    (hM : ∀ y, |ρ y| ≤ M) :
    ∫ x, |∫ y, B x y * ρ y ∂haar 1| ∂haar 1 ≤
      M * ∫ p, |B p.1 p.2| ∂(haar 1).prod (haar 1) := by
  have hint : Integrable (fun p : Torus 1 × Torus 1 => |B p.1 p.2|) ((haar 1).prod (haar 1)) :=
    hB.abs
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Classical.arbitrary _))
  have hslice : ∀ᵐ x ∂haar 1, Integrable (fun y => |B x y|) (haar 1) := hint.prod_right_ae
  have h1 : ∀ᵐ x ∂haar 1, |∫ y, B x y * ρ y ∂haar 1| ≤ M * ∫ y, |B x y| ∂haar 1 := by
    filter_upwards [hslice] with x hx
    have h2 : |∫ y, B x y * ρ y ∂haar 1| ≤ ∫ y, |B x y * ρ y| ∂haar 1 := by
      simpa using norm_integral_le_integral_norm (μ := haar 1) (fun y => B x y * ρ y)
    refine h2.trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
      (hx.const_mul M) (Filter.Eventually.of_forall fun y => ?_)
    show |B x y * ρ y| ≤ M * |B x y|
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM y) (abs_nonneg _)
  have hs : Integrable (fun x => ∫ y, |B x y| ∂haar 1) (haar 1) := hint.integral_prod_left
  calc ∫ x, |∫ y, B x y * ρ y ∂haar 1| ∂haar 1
      ≤ ∫ x, M * ∫ y, |B x y| ∂haar 1 ∂haar 1 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
          (hs.const_mul M) h1
    _ = M * ∫ p, |B p.1 p.2| ∂(haar 1).prod (haar 1) := by
        rw [integral_const_mul, integral_prod _ hint]

/-- SEM001. -/
theorem rate_defined_ambient_subspaces_for_each_topology :
    (∀ (K : RoughKernelClass) (ρ : AbsoluteDensity 1),
      Integrable (K.drift.force ρ) (haar 1) ∧
      IsWeakGradientLp 1 (interactionPotential K.toInteraction ρ) (K.drift.force ρ) ∧
      ∃ (G : Torus 2 → Tangent 2) (r : Torus 1 → ℝ), IsWeakGradientLp 1 K.W G ∧ Continuous r ∧
        (fun y => ρ.density y) =ᵐ[haar 1] r ∧
        K.drift.force ρ =ᵐ[haar 1]
          fun x => (EuclideanSpace.single 0 (∫ y, G (pairPt x y) 0 * r y ∂haar 1) : Tangent 1)) ∧
    (∀ (K : RoughKernelClass) (b b' : AbsoluteDrift K.toInteraction),
      scalarRate K.toInteraction b = scalarRate K.toInteraction b' ∧
      speciesRate K.toInteraction b = speciesRate K.toInteraction b') ∧
    (∀ α : ℝ≥0, 0 < α → α < 1 → Function.Injective (holderEmbed α) ∧
      @Topology.IsEmbedding _ _ (holderTopology α) _ (holderEmbed α)) ∧
    (∀ (p : ℝ≥0∞) (hp : 1 ≤ p), p < 2 →
      haveI : Fact (1 ≤ p) := ⟨hp⟩
      Function.Injective (sobolevEmbed p) ∧
      @Topology.IsEmbedding _ _ (sobolevTopology p) _ (sobolevEmbed p)) ∧
    (∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (W : Torus 2 → ℝ), Continuous W →
      (∀ x y : Torus 1, W (pairPt x y) = W (pairPt y x)) → (∀ x : Torus 1, W (pairPt x x) = 0) →
      (∃ G, IsWeakGradientLp p W G) → ∃ K : RoughKernelClass, K.W = W) := by
  refine ⟨fun K ρ => ⟨K.drift.integrable_force ρ, K.drift.weak_gradient ρ,
      drift_force_formula K ρ⟩, fun K b b' => ⟨scalarRate_eq_of_providers b b',
      speciesRate_eq_of_providers b b'⟩, fun α _ _ => ⟨holderEmbed_injective α,
      holderEmbed_isEmbedding α⟩, fun p hp _ => ⟨@sobolevEmbed_injective p ⟨hp⟩,
      @sobolevEmbed_isEmbedding p ⟨hp⟩⟩, fun p hp W hc hs hd ⟨G, hG⟩ => ?_⟩
  obtain ⟨K, hK, -⟩ := mem_K_of_sobolev hp hc hs hd hG
  exact ⟨K, hK⟩

end DGPS.Analysis.RateTopology
