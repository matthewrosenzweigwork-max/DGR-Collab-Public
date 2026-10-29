import DGPS.Examples.RoughBoundary.SemicontinuitySequenceSEM011
import DGPS.Examples.RoughBoundary.SemicontinuityPositiveRatesSEM012
import DGPS.Examples.RoughBoundary.SmallAmplitude
import DGPS.Examples.RoughBoundary.KernelConvergence
import Mathlib.Topology.Semicontinuity.Defs

/-!
# SEM014: upper semicontinuity countersequence

With `ε₀` and `L₀` from SEM012 and `e₀ = min ε₀ 1`, the primary kernels `W_{ε_j}` for
`ε_j = e₀ / (j + 1)` converge to `W₀` in every fixed Hölder and subcritical Sobolev topology.
Both rates equal `a0 = 4π²` along the sequence and vanish at `W₀`. Hence neither rate function is
upper semicontinuous at `W₀` in any of these topologies.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal NNReal

namespace DGPS.Examples.RoughBoundary.Semicontinuity

open DGPS.Analysis.RateTopology

lemma torusDist_nonneg_SEM014 (x y : Torus 1) : 0 ≤ DGPS.torusDist x y :=
  dist_nonneg.trans (DGPS.torusDist_comparison x y).1

lemma dist_le_torusDist_SEM014 (x y : Torus 1) : dist x y ≤ DGPS.torusDist x y :=
  (DGPS.torusDist_comparison x y).1

lemma dist_pairPt_le_SEM014 (x y x' y' : Torus 1) :
    dist (pairPt x y) (pairPt x' y') ≤ max (dist x x') (dist y y') := by
  refine (dist_pi_le_iff (le_trans dist_nonneg (le_max_left _ _))).2 fun i => ?_
  fin_cases i
  · simpa [pairPt] using (dist_le_pi_dist x x' 0).trans (le_max_left _ _)
  · simpa [pairPt] using (dist_le_pi_dist y y' 0).trans (le_max_right _ _)

lemma dist_pairPt_le_torus_SEM014 (x y x' y' : Torus 1) :
    dist (pairPt x y) (pairPt x' y') ≤
      max (DGPS.torusDist x x') (DGPS.torusDist y y') :=
  (dist_pairPt_le_SEM014 x y x' y').trans
    (max_le_max (dist_le_torusDist_SEM014 x x') (dist_le_torusDist_SEM014 y y'))

/-- The difference `W_{L,ε} - W_{L,0}` as a kernel on `𝕋 × 𝕋`. -/
noncomputable def diffKernel_SEM014 (L ε : ℝ) : Torus 1 → Torus 1 → ℝ :=
  fun x y => Model.modelW L ε x y - Model.modelW L 0 x y

lemma pair_eq_SEM014 (L ε : ℝ) (x y : Torus 1) :
    diffKernel_SEM014 L ε x y = Model.Wtor L ε (pairPt x y) - Model.Wtor L 0 (pairPt x y) := by
  simp only [diffKernel_SEM014, Model.Wtor, q1_pairPt, q2_pairPt]

lemma seminorm_nonneg_SEM014 (α : ℝ) (D : Torus 1 → Torus 1 → ℝ) :
    0 ≤ prodHolderSeminorm α D :=
  Real.iSup_nonneg fun _ => div_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (le_max_of_le_left (torusDist_nonneg_SEM014 _ _)) _)

lemma quot_le_SEM014 {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K) {D : Torus 1 → Torus 1 → ℝ}
    (hD : ∀ x y x' y' : Torus 1, |D x y - D x' y'| ≤
      K * (max (DGPS.torusDist x x') (DGPS.torusDist y y')) ^ α)
    (p : (Torus 1 × Torus 1) × (Torus 1 × Torus 1)) :
    |D p.1.1 p.1.2 - D p.2.1 p.2.2| /
      (max (DGPS.torusDist p.1.1 p.2.1) (DGPS.torusDist p.1.2 p.2.2)) ^ α ≤ K := by
  by_cases hm : max (DGPS.torusDist p.1.1 p.2.1) (DGPS.torusDist p.1.2 p.2.2) = 0
  · rw [hm, Real.zero_rpow hα.ne', div_zero]
    exact hK
  · have hm0 : 0 ≤ max (DGPS.torusDist p.1.1 p.2.1) (DGPS.torusDist p.1.2 p.2.2) :=
      le_max_of_le_left (torusDist_nonneg_SEM014 _ _)
    have hpos : 0 < max (DGPS.torusDist p.1.1 p.2.1) (DGPS.torusDist p.1.2 p.2.2) ^ α :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne hm0 (Ne.symm hm)) _
    rw [div_le_iff₀ hpos]
    exact hD _ _ _ _

lemma pair_le_SEM014 {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K) {D : Torus 1 → Torus 1 → ℝ}
    (hD : ∀ x y x' y' : Torus 1, |D x y - D x' y'| ≤
      K * (max (DGPS.torusDist x x') (DGPS.torusDist y y')) ^ α)
    (x y x' y' : Torus 1) :
    |D x y - D x' y'| ≤
      prodHolderSeminorm α D * (max (DGPS.torusDist x x') (DGPS.torusDist y y')) ^ α := by
  have hb : BddAbove (Set.range fun p : (Torus 1 × Torus 1) × (Torus 1 × Torus 1) =>
      |D p.1.1 p.1.2 - D p.2.1 p.2.2| /
        (max (DGPS.torusDist p.1.1 p.2.1) (DGPS.torusDist p.1.2 p.2.2)) ^ α) :=
    ⟨K, by rintro _ ⟨p, rfl⟩; exact quot_le_SEM014 hα hK hD p⟩
  by_cases hm : max (DGPS.torusDist x x') (DGPS.torusDist y y') = 0
  · have h0 := hD x y x' y'
    rw [hm, Real.zero_rpow hα.ne', mul_zero] at h0 ⊢
    exact h0
  · have hm0 : 0 ≤ max (DGPS.torusDist x x') (DGPS.torusDist y y') :=
      le_max_of_le_left (torusDist_nonneg_SEM014 _ _)
    have hpos : 0 < max (DGPS.torusDist x x') (DGPS.torusDist y y') ^ α :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne hm0 (Ne.symm hm)) _
    have hq : |D x y - D x' y'| /
        (max (DGPS.torusDist x x') (DGPS.torusDist y y')) ^ α ≤ prodHolderSeminorm α D :=
      le_ciSup hb ((x, y), (x', y'))
    rw [div_le_iff₀ hpos] at hq
    exact hq

lemma abs_le_prodSupNorm_SEM014 {D : Torus 1 → Torus 1 → ℝ}
    (hc : Continuous (fun q : Torus 1 × Torus 1 => D q.1 q.2)) (x y : Torus 1) :
    |D x y| ≤ prodSupNorm D := by
  have hb : BddAbove (Set.range fun z : Torus 1 × Torus 1 => |D z.1 z.2|) :=
    (isCompact_range (continuous_abs.comp hc)).bddAbove
  unfold prodSupNorm
  exact le_ciSup hb (x, y)

lemma torus2_holder_diff_SEM014 {f g : Torus 2 → ℝ} {C1 C2 r : ℝ≥0}
    (hf : HolderWith C1 r f) (hg : HolderWith C2 r g) (z z' : Torus 2) :
    |(f z - g z) - (f z' - g z')| ≤ ((C1 : ℝ) + C2) * dist z z' ^ (r : ℝ) := by
  have h1 := hf.dist_le z z'
  have h2 := hg.dist_le z z'
  rw [Real.dist_eq] at h1 h2
  have e : (f z - g z) - (f z' - g z') = (f z - f z') - (g z - g z') := by ring
  rw [e, add_mul]
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

lemma holder_bound_SEM014 {L : ℝ} (hL : 0 < L) {α : ℝ} (h0 : 0 < α) {ε C K : ℝ}
    (hC0 : 0 ≤ C) (hCε : prodHolderNorm α (diffKernel_SEM014 L ε) ≤ C * |ε|) (hK0 : 0 ≤ K)
    (hK : ∀ z z' : Torus 2, |(Model.Wtor L ε z - Model.Wtor L 0 z) -
      (Model.Wtor L ε z' - Model.Wtor L 0 z')| ≤ K * dist z z' ^ α) :
    (∀ z : Torus 2, |Model.Wtor L ε z - Model.Wtor L 0 z| ≤ C * |ε|) ∧
      (∀ z z' : Torus 2, |(Model.Wtor L ε z - Model.Wtor L 0 z) -
        (Model.Wtor L ε z' - Model.Wtor L 0 z')| ≤
          C * |ε| * Real.sqrt 2 ^ α * dist z z' ^ α) := by
  have hcont : Continuous (fun q : Torus 1 × Torus 1 => diffKernel_SEM014 L ε q.1 q.2) :=
    (Model.continuous_modelW hL ε).sub (Model.continuous_modelW hL 0)
  have hD : ∀ x y x' y' : Torus 1,
      |diffKernel_SEM014 L ε x y - diffKernel_SEM014 L ε x' y'| ≤
        K * (max (DGPS.torusDist x x') (DGPS.torusDist y y')) ^ α := by
    intro x y x' y'
    rw [pair_eq_SEM014, pair_eq_SEM014]
    exact (hK _ _).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (dist_pairPt_le_torus_SEM014 x y x' y') h0.le) hK0)
  have hS : prodHolderSeminorm α (diffKernel_SEM014 L ε) ≤ C * |ε| :=
    (le_add_of_nonneg_left (prodSupNorm_nonneg (diffKernel_SEM014 L ε))).trans hCε
  have hsup : ∀ x y, |diffKernel_SEM014 L ε x y| ≤ C * |ε| := fun x y =>
    (abs_le_prodSupNorm_SEM014 hcont x y).trans
      ((le_add_of_nonneg_right (seminorm_nonneg_SEM014 α (diffKernel_SEM014 L ε))).trans hCε)
  have hpair : ∀ x y x' y' : Torus 1,
      |(Model.Wtor L ε (pairPt x y) - Model.Wtor L 0 (pairPt x y)) -
        (Model.Wtor L ε (pairPt x' y') - Model.Wtor L 0 (pairPt x' y'))| ≤
        C * |ε| * Real.sqrt (DGPS.torusDist x x' ^ 2 + DGPS.torusDist y y' ^ 2) ^ α := by
    intro x y x' y'
    rw [← pair_eq_SEM014 L ε x y, ← pair_eq_SEM014 L ε x' y']
    have hm0 : 0 ≤ max (DGPS.torusDist x x') (DGPS.torusDist y y') :=
      le_max_of_le_left (torusDist_nonneg_SEM014 _ _)
    have hms : max (DGPS.torusDist x x') (DGPS.torusDist y y') ≤
        Real.sqrt (DGPS.torusDist x x' ^ 2 + DGPS.torusDist y y' ^ 2) :=
      max_le ((le_abs_self _).trans (Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))))
        ((le_abs_self _).trans (Real.abs_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))))
    refine (pair_le_SEM014 h0 hK0 hD x y x' y').trans ?_
    refine (mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg hm0 _)).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm0 hms h0.le)
      (mul_nonneg hC0 (abs_nonneg _))
  refine ⟨fun z => hsup (q1 z) (q2 z), fun z z' => ?_⟩
  exact abs_sub_le_of_pair_bound_SEM011
    (D := fun w : Torus 2 => Model.Wtor L ε w - Model.Wtor L 0 w) (M := C * |ε|) (α := α)
    (mul_nonneg hC0 (abs_nonneg _)) h0.le hpair z z'

lemma holder_diff_SEM014 {L : ℝ} (hL : 0 < L) {αN : ℝ≥0} (h0 : 0 < (αN : ℝ))
    (h1 : (αN : ℝ) < 1) {C : ℝ} (hC0 : 0 ≤ C) (ε : ℝ)
    (hCε : prodHolderNorm (αN : ℝ) (diffKernel_SEM014 L ε) ≤ C * |ε|) :
    (∀ z : Torus 2, |Model.Wtor L ε z - Model.Wtor L 0 z| ≤ C * |ε|) ∧
      (∀ z z' : Torus 2, |(Model.Wtor L ε z - Model.Wtor L 0 z) -
        (Model.Wtor L ε z' - Model.Wtor L 0 z')| ≤
          C * |ε| * Real.sqrt 2 ^ (αN : ℝ) * dist z z' ^ (αN : ℝ)) := by
  obtain ⟨K1, hf⟩ := primary_holder_SEM011 hL ε h0 h1
  obtain ⟨K2, hg⟩ := primary_holder_SEM011 hL 0 h0 h1
  exact holder_bound_SEM014 hL h0 hC0 hCε (K := (K1 : ℝ) + K2) (by positivity)
    (fun z z' => torus2_holder_diff_SEM014 hf hg z z')

lemma tendsto_holder_seq_SEM014 {L : ℝ} (hL : 0 < L) {αN : ℝ≥0} (h0 : 0 < (αN : ℝ))
    (h1 : (αN : ℝ) < 1) (e : ℕ → ℝ) (hε : ∀ j, |e j| ≤ 1) (he : Tendsto e atTop (𝓝 0)) :
    @Tendsto ℕ (HolderKernel αN)
      (fun j => ⟨primaryKernel_SEM011 hL (e j), primary_holder_SEM011 hL (e j) h0 h1⟩)
      atTop (@nhds _ (holderTopology αN)
        ⟨primaryKernel_SEM011 hL 0, primary_holder_SEM011 hL 0 h0 h1⟩) := by
  obtain ⟨C, hC0, hC⟩ :=
    (strong_small_amplitude_convergence_at_every_fixed_exponent hL).2.1 (αN : ℝ) h0 h1
  have hsq : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h3 := Real.sqrt_nonneg 2
    nlinarith
  have hw : (1 : ℝ) ≤ Real.sqrt 2 ^ (αN : ℝ) := Real.one_le_rpow hsq (NNReal.coe_nonneg αN)
  have hc : Tendsto (fun j => C * |e j| * Real.sqrt 2 ^ (αN : ℝ)) atTop (𝓝 0) := by
    have h := ((he.abs).const_mul C).mul_const (Real.sqrt 2 ^ (αN : ℝ))
    rwa [show C * |(0 : ℝ)| * Real.sqrt 2 ^ (αN : ℝ) = 0 by simp] at h
  refine tendsto_holderKernel_SEM011 _ _ (fun j => C * |e j| * Real.sqrt 2 ^ (αN : ℝ)) hc ?_ ?_
  · intro j z
    exact ((holder_diff_SEM014 hL h0 h1 hC0 (e j) (hC (e j) (hε j))).1 z).trans
      (le_mul_of_one_le_right (mul_nonneg hC0 (abs_nonneg _)) hw)
  · intro j z z'
    exact (holder_diff_SEM014 hL h0 h1 hC0 (e j) (hC (e j) (hε j))).2 z z'

lemma tendsto_sobolev_seq_SEM014 {L : ℝ} (hL : 0 < L) {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp⟩
    @Tendsto ℕ (SobolevKernel (ENNReal.ofReal p))
      (fun j => ⟨primaryKernel_SEM011 hL (e j), primary_sobolev_SEM011 hL (e j) hp hp2⟩)
      atTop (@nhds _ (sobolevTopology (ENNReal.ofReal p))
        ⟨primaryKernel_SEM011 hL 0, primary_sobolev_SEM011 hL 0 hp hp2⟩) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  obtain ⟨C, hCt, hC⟩ :=
    (strong_small_amplitude_convergence_at_every_fixed_exponent hL).2.2 p hp hp2
  have hlim : Tendsto (fun j => C * ENNReal.ofReal |e j|) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal he.abs) (a := C) (Or.inr hCt)
    rwa [show C * ENNReal.ofReal |(0 : ℝ)| = 0 by simp] at h
  have hlim2 : Tendsto (fun j => C * ENNReal.ofReal |e j| + C * ENNReal.ofReal |e j|)
      atTop (𝓝 0) := by
    have h := hlim.add hlim
    rwa [add_zero] at h
  refine tendsto_sobolevKernel_SEM011 hp' _ _ (fun j => Model.gradW L (e j)) (Model.gradW L 0)
    (fun j => Model.isWeakGradientLp_Wtor hL (e j) hp hp2)
    (Model.isWeakGradientLp_Wtor hL 0 hp hp2) ?_ ?_
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) ?_
    intro j
    exact (hC (e j)).1
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim2
      (fun _ => bot_le) ?_
    intro j
    have hF : AEStronglyMeasurable (fun z => Model.gradW L (e j) z - Model.gradW L 0 z)
        (DGPS.haar 2) :=
      ((Model.memLp_gradW hL (e j) hp hp2).aestronglyMeasurable).sub
        (Model.memLp_gradW hL 0 hp hp2).aestronglyMeasurable
    refine (eLpNorm_tangent_le_SEM011 hp' hF).trans (add_le_add ?_ ?_)
    · have e0 : (fun z => (Model.gradW L (e j) z - Model.gradW L 0 z) 0) = fun z =>
          prodGradX (Feature.Ufeat L (e j)) (Feature.Uprime L (e j)) (q1 z) (q2 z) -
            prodGradX (Feature.Ufeat L 0) (Feature.Uprime L 0) (q1 z) (q2 z) := by
        funext z
        simp [Model.gradW, Model.gradPair, prodGradX]
      exact (le_of_eq (congrArg (fun f => eLpNorm f (ENNReal.ofReal p) (DGPS.haar 2)) e0)).trans
        (hC (e j)).2.1
    · have e1 : (fun z => (Model.gradW L (e j) z - Model.gradW L 0 z) 1) = fun z =>
          prodGradY (Feature.Ufeat L (e j)) (Feature.Uprime L (e j)) (q1 z) (q2 z) -
            prodGradY (Feature.Ufeat L 0) (Feature.Uprime L 0) (q1 z) (q2 z) := by
        funext z
        simp [Model.gradW, Model.gradPair, prodGradY]
      exact (le_of_eq (congrArg (fun f => eLpNorm f (ENNReal.ofReal p) (DGPS.haar 2)) e1)).trans
        (hC (e j)).2.2

lemma not_usc_SEM014 {X : Type*} [TopologicalSpace X] {f : X → ℝ≥0∞} {xs : ℕ → X} {x : X}
    {a : ℝ≥0∞} (ht : Tendsto xs atTop (𝓝 x)) (hz : ∀ j, f (xs j) = a) (hlt : f x < a) :
    ¬ UpperSemicontinuousAt f x := by
  intro hu
  have he : ∀ᶠ j in atTop, f (xs j) < a := ht.eventually (hu a hlt)
  obtain ⟨j, hj1, hj2⟩ := (he.and (Eventually.of_forall hz)).exists
  rw [hj2] at hj1
  exact lt_irrefl _ hj1

lemma not_usc_zero_SEM014 {X : Type*} [TopologicalSpace X] {f : X → ℝ≥0∞} {xs : ℕ → X}
    {x : X} (ht : Tendsto xs atTop (𝓝 x)) (hz : ∀ j, f (xs j) = ENNReal.ofReal (4 * π ^ 2))
    (hx : f x = 0) : ¬ UpperSemicontinuousAt f x :=
  not_usc_SEM014 ht hz (by rw [hx]; exact positive_a0_SEM011)

lemma kernel_rates_of_model_SEM014 {L : ℝ} (hL : 0 < L) (ε : ℝ) {a : ℝ≥0∞}
    (hs : ∀ b : AbsoluteDrift (Model.modelData hL ε),
      scalarRate (Model.modelData hL ε) b = a ∧ speciesRate (Model.modelData hL ε) b = a) :
    scalarKernelRate_SEM011 (primaryKernel_SEM011 hL ε) = a ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL ε) = a := by
  have h := toInteraction_primaryKernel_SEM011 hL ε
  let b : AbsoluteDrift (Model.modelData hL ε) := h ▸ (primaryKernel_SEM011 hL ε).drift
  exact ⟨(scalarRate_congr_SEM011 h _ b).trans (hs b).1,
    (speciesRate_congr_SEM011 h _ b).trans (hs b).2⟩

lemma eps_seq_SEM014 {ε₀ : ℝ} (hε₀ : 0 < ε₀) (j : ℕ) :
    0 < min ε₀ 1 / ((j : ℝ) + 1) ∧ min ε₀ 1 / ((j : ℝ) + 1) ≤ ε₀ ∧
      min ε₀ 1 / ((j : ℝ) + 1) ≤ 1 := by
  have hm : 0 < min ε₀ 1 := lt_min hε₀ one_pos
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    linarith
  have hd : min ε₀ 1 / ((j : ℝ) + 1) ≤ min ε₀ 1 := div_le_self hm.le hj
  exact ⟨div_pos hm (by linarith), hd.trans (min_le_left _ _), hd.trans (min_le_right _ _)⟩

lemma tendsto_eps_seq_SEM014 (ε₀ : ℝ) :
    Tendsto (fun j : ℕ => min ε₀ 1 / ((j : ℝ) + 1)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (min ε₀ 1)
  rw [mul_zero] at h
  exact Tendsto.congr (fun j => by ring) h

lemma holder_part_SEM014 {L : ℝ} (hL : 0 < L) {e : ℕ → ℝ} (hε : ∀ j, |e j| ≤ 1)
    (he : Tendsto e atTop (𝓝 0))
    (hA : ∀ j, scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (e j)) =
        ENNReal.ofReal (4 * π ^ 2) ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (e j)) = ENNReal.ofReal (4 * π ^ 2))
    (hA0 : scalarKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0 ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0)
    (α : ℝ≥0) (h0 : 0 < (α : ℝ)) (h1 : (α : ℝ) < 1) :
    @Tendsto ℕ (HolderKernel α)
        (fun j => ⟨primaryKernel_SEM011 hL (e j), primary_holder_SEM011 hL (e j) h0 h1⟩)
        atTop (@nhds _ (holderTopology α)
          ⟨primaryKernel_SEM011 hL 0, primary_holder_SEM011 hL 0 h0 h1⟩) ∧
      (haveI := holderTopology α
       ¬ UpperSemicontinuousAt (fun K : HolderKernel α => scalarKernelRate_SEM011 K.1)
          ⟨primaryKernel_SEM011 hL 0, primary_holder_SEM011 hL 0 h0 h1⟩ ∧
       ¬ UpperSemicontinuousAt (fun K : HolderKernel α => speciesKernelRate_SEM011 K.1)
          ⟨primaryKernel_SEM011 hL 0, primary_holder_SEM011 hL 0 h0 h1⟩) := by
  have hT := tendsto_holder_seq_SEM014 hL h0 h1 e hε he
  exact ⟨hT,
    @not_usc_zero_SEM014 (HolderKernel α) (holderTopology α)
      (fun K : HolderKernel α => scalarKernelRate_SEM011 K.1) _ _ hT
      (fun j => (hA j).1) hA0.1,
    @not_usc_zero_SEM014 (HolderKernel α) (holderTopology α)
      (fun K : HolderKernel α => speciesKernelRate_SEM011 K.1) _ _ hT
      (fun j => (hA j).2) hA0.2⟩

lemma sobolev_part_SEM014 {L : ℝ} (hL : 0 < L) {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hA : ∀ j, scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (e j)) =
        ENNReal.ofReal (4 * π ^ 2) ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (e j)) = ENNReal.ofReal (4 * π ^ 2))
    (hA0 : scalarKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0 ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0) :
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp⟩
    @Tendsto ℕ (SobolevKernel (ENNReal.ofReal p))
        (fun j => ⟨primaryKernel_SEM011 hL (e j), primary_sobolev_SEM011 hL (e j) hp hp2⟩)
        atTop (@nhds _ (sobolevTopology (ENNReal.ofReal p))
          ⟨primaryKernel_SEM011 hL 0, primary_sobolev_SEM011 hL 0 hp hp2⟩) ∧
      (haveI := sobolevTopology (ENNReal.ofReal p)
       ¬ UpperSemicontinuousAt
          (fun K : SobolevKernel (ENNReal.ofReal p) => scalarKernelRate_SEM011 K.1)
          ⟨primaryKernel_SEM011 hL 0, primary_sobolev_SEM011 hL 0 hp hp2⟩ ∧
       ¬ UpperSemicontinuousAt
          (fun K : SobolevKernel (ENNReal.ofReal p) => speciesKernelRate_SEM011 K.1)
          ⟨primaryKernel_SEM011 hL 0, primary_sobolev_SEM011 hL 0 hp hp2⟩) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨hp'⟩
  have hS := tendsto_sobolev_seq_SEM014 hL hp hp2 e he
  exact ⟨hS,
    @not_usc_zero_SEM014 (SobolevKernel (ENNReal.ofReal p)) (sobolevTopology (ENNReal.ofReal p))
      (fun K : SobolevKernel (ENNReal.ofReal p) => scalarKernelRate_SEM011 K.1) _ _ hS
      (fun j => (hA j).1) hA0.1,
    @not_usc_zero_SEM014 (SobolevKernel (ENNReal.ofReal p)) (sobolevTopology (ENNReal.ofReal p))
      (fun K : SobolevKernel (ENNReal.ofReal p) => speciesKernelRate_SEM011 K.1) _ _ hS
      (fun j => (hA j).2) hA0.2⟩

/-- **SEM014.** Upper semicontinuity countersequence. There are `e₀ > 0` and `L > 0` such that,
with `ε_j = e₀ / (j + 1)`: both rates of `W_{L,ε_j}` equal `a0 = 4π²`; both rates of `W_{L,0}`
vanish; `W_{L,ε_j} → W_{L,0}` in every fixed strict Hölder topology `K_α` and every fixed
subcritical Sobolev topology `K_p`; and in each of these topologies neither rate function is upper
semicontinuous at `W_{L,0}`. -/
theorem upper_semicontinuity_countersequence :
    ∃ (e0 L : ℝ) (hL : 0 < L), 0 < e0 ∧
      (∀ j : ℕ,
        scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (e0 / ((j : ℝ) + 1))) =
            ENNReal.ofReal (4 * π ^ 2) ∧
          speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (e0 / ((j : ℝ) + 1))) =
            ENNReal.ofReal (4 * π ^ 2)) ∧
      scalarKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0 ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0 ∧
      (∀ (α : ℝ≥0) (h0 : 0 < (α : ℝ)) (h1 : (α : ℝ) < 1),
        @Tendsto ℕ (HolderKernel α)
            (fun j => ⟨primaryKernel_SEM011 hL (e0 / ((j : ℝ) + 1)),
              primary_holder_SEM011 hL (e0 / ((j : ℝ) + 1)) h0 h1⟩)
            atTop (@nhds _ (holderTopology α)
              ⟨primaryKernel_SEM011 hL 0, primary_holder_SEM011 hL 0 h0 h1⟩) ∧
          (haveI := holderTopology α
           ¬ UpperSemicontinuousAt (fun K : HolderKernel α => scalarKernelRate_SEM011 K.1)
              ⟨primaryKernel_SEM011 hL 0, primary_holder_SEM011 hL 0 h0 h1⟩ ∧
           ¬ UpperSemicontinuousAt (fun K : HolderKernel α => speciesKernelRate_SEM011 K.1)
              ⟨primaryKernel_SEM011 hL 0, primary_holder_SEM011 hL 0 h0 h1⟩)) ∧
      (∀ (p : ℝ) (hp : 1 ≤ p) (hp2 : p < 2),
        haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp⟩
        @Tendsto ℕ (SobolevKernel (ENNReal.ofReal p))
            (fun j => ⟨primaryKernel_SEM011 hL (e0 / ((j : ℝ) + 1)),
              primary_sobolev_SEM011 hL (e0 / ((j : ℝ) + 1)) hp hp2⟩)
            atTop (@nhds _ (sobolevTopology (ENNReal.ofReal p))
              ⟨primaryKernel_SEM011 hL 0, primary_sobolev_SEM011 hL 0 hp hp2⟩) ∧
          (haveI := sobolevTopology (ENNReal.ofReal p)
           ¬ UpperSemicontinuousAt
              (fun K : SobolevKernel (ENNReal.ofReal p) => scalarKernelRate_SEM011 K.1)
              ⟨primaryKernel_SEM011 hL 0, primary_sobolev_SEM011 hL 0 hp hp2⟩ ∧
           ¬ UpperSemicontinuousAt
              (fun K : SobolevKernel (ENNReal.ofReal p) => speciesKernelRate_SEM011 K.1)
              ⟨primaryKernel_SEM011 hL 0, primary_sobolev_SEM011 hL 0 hp hp2⟩)) := by
  obtain ⟨ε₀, L₀, hε₀, hL₀, -, hmain⟩ := every_small_nonzero_amplitude_has_exact_positive_rates
  have hLpos : 0 < L₀ := by linarith
  have hm := hmain L₀ le_rfl hLpos
  have hrate : ∀ j : ℕ,
      scalarKernelRate_SEM011 (primaryKernel_SEM011 hLpos (min ε₀ 1 / ((j : ℝ) + 1))) =
          ENNReal.ofReal (4 * π ^ 2) ∧
        speciesKernelRate_SEM011 (primaryKernel_SEM011 hLpos (min ε₀ 1 / ((j : ℝ) + 1))) =
          ENNReal.ofReal (4 * π ^ 2) := by
    intro j
    obtain ⟨hpos, hle, -⟩ := eps_seq_SEM014 hε₀ j
    exact kernel_rates_of_model_SEM014 hLpos _
      ((hm.1 _ (abs_pos_of_pos hpos) (by rw [abs_of_pos hpos]; exact hle)).2.2)
  have hr0 := kernel_rates_of_model_SEM014 hLpos 0 hm.2
  have hε1 : ∀ j : ℕ, |min ε₀ 1 / ((j : ℝ) + 1)| ≤ 1 := by
    intro j
    obtain ⟨hpos, -, hle1⟩ := eps_seq_SEM014 hε₀ j
    rw [abs_of_pos hpos]
    exact hle1
  have he := tendsto_eps_seq_SEM014 ε₀
  exact ⟨min ε₀ 1, L₀, hLpos, lt_min hε₀ one_pos, hrate, hr0.1, hr0.2,
    fun α h0 h1 => holder_part_SEM014 hLpos hε1 he hrate hr0 α h0 h1,
    fun p hp hp2 => sobolev_part_SEM014 hLpos hp hp2 he hrate hr0⟩

end DGPS.Examples.RoughBoundary.Semicontinuity
