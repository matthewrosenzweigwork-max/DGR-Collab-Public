import DGPS.Examples.RoughBoundary.NonlinearSpeciesRate
import DGPS.Examples.RoughBoundary.SemicontinuityZeroRate
import DGPS.Examples.RoughBoundary.KernelConvergence
import DGPS.Analysis.PeriodicMollificationHolder

open MeasureTheory Set Filter Topology
open scoped Real ENNReal NNReal ContDiff

namespace DGPS.Examples.RoughBoundary.Semicontinuity

open DGPS.Examples.RoughBoundary.Spikes (pt)
open DGPS.Examples.RoughBoundary.Feature (Aprim Qdens Q2 Qtor Jrot)
open DGPS (IsSmoothPeriodic coordPartial torusLift)
open DGPS.Analysis.PeriodicMollification (TorusHolderBdd torusHolderSeminorm torusSupNorm
  torusHolderNorm mollify abs_mollify_sub_le torusHolderSeminorm_nonneg torusSupNorm_nonneg)

lemma contDiff_aprim_SEM011 (L : ℝ) : ContDiff ℝ ∞ (Aprim L) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (Feature.hasDerivAt_aprim L s).differentiableAt, ?_⟩
  have : deriv (Aprim L) = Qdens L := funext fun s => (Feature.hasDerivAt_aprim L s).deriv
  rw [this]
  exact Feature.contDiff_qdens L

lemma contDiff_pt_comp_SEM011 {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) :
    ContDiff ℝ ∞ (fun t : ℝ => f (pt t)) := by
  have h2 : ContDiff ℝ ∞ (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    contDiff_pi.2 fun _ => contDiff_id
  exact hf.comp h2

lemma contDiff_thetaF_SEM011 (L η : ℝ) {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) :
    ContDiff ℝ ∞ (thetaF L η f) := by
  unfold thetaF
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => Aprim L (2 * x)) :=
    (contDiff_aprim_SEM011 L).comp (contDiff_const.mul contDiff_id)
  have h2 : ContDiff ℝ ∞ (fun x : ℝ => f (pt (6 * x))) :=
    (contDiff_pt_comp_SEM011 hf).comp (contDiff_const.mul contDiff_id)
  exact (h1.sub contDiff_const).add (contDiff_const.mul h2)

lemma contDiff_UrealF_coord_SEM011 (L η : ℝ) {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) (j : Fin 2) :
    ContDiff ℝ ∞ (fun t : ℝ => UrealF L η f t j) := by
  have h := (contDiff_const (c := 2 * π)).mul (contDiff_thetaF_SEM011 L η hf)
  fin_cases j
  · have e : (fun t : ℝ => UrealF L η f t 0) = fun t => Real.cos (2 * π * thetaF L η f t) := by
      funext t; simp [UrealF]
    exact (show ContDiff ℝ ∞ (fun t : ℝ => UrealF L η f t 0) from e ▸ Real.contDiff_cos.comp h)
  · have e : (fun t : ℝ => UrealF L η f t 1) = fun t => Real.sin (2 * π * thetaF L η f t) := by
      funext t; simp [UrealF]
    exact (show ContDiff ℝ ∞ (fun t : ℝ => UrealF L η f t 1) from e ▸ Real.contDiff_sin.comp h)

lemma isSmoothPeriodic_UfeatF_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {f : Torus 1 → ℝ}
    (hf : IsSmoothPeriodic f) (j : Fin 2) :
    IsSmoothPeriodic (fun y => UfeatF L η f y j) := by
  have h : ((fun y => UfeatF L η f y j) ∘ torusLift) = fun v : Fin 1 → ℝ => UrealF L η f (v 0) j := by
    funext v
    have : (torusLift v : Torus 1) = pt (v 0) := by
      unfold pt; congr 1; funext i; rw [Subsingleton.elim i 0]
    simp only [Function.comp_apply, this, UfeatF_pt hL]
  unfold IsSmoothPeriodic
  rw [h]
  exact (contDiff_UrealF_coord_SEM011 L η hf j).comp (contDiff_apply ℝ ℝ 0)


lemma Q2_pt_SEM011 (L t : ℝ) : Q2 L (pt t) = Qdens L (2 * t) := by
  unfold Q2
  rw [Feature.zsmul_pt]
  simpa using Feature.Qtor_pt L (2 * t)

lemma hasDerivAt_thetaF_SEM011 (L η : ℝ) {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) (t : ℝ) :
    HasDerivAt (thetaF L η f) (dthetaTF L η (coordPartial 0 f) (pt t)) t := by
  have h1 : HasDerivAt (fun x : ℝ => Aprim L (2 * x)) (Qdens L (2 * t) * 2) t := by
    have := (Feature.hasDerivAt_aprim L (2 * t)).comp t ((hasDerivAt_id t).const_mul (2 : ℝ))
    convert this using 1
    · rfl
    · simp
  have h2 : HasDerivAt (fun x : ℝ => f (pt (6 * x))) (coordPartial 0 f (pt (6 * t)) * 6) t := by
    have := (hasDerivAt_smooth_one hf (6 * t)).comp t ((hasDerivAt_id t).const_mul (6 : ℝ))
    convert this using 1
    · rfl
    · simp [pt]
  have h3 := ((h1.sub_const (1 / 6)).add (h2.const_mul η))
  have e : dthetaTF L η (coordPartial 0 f) (pt t) =
      Qdens L (2 * t) * 2 + η * (coordPartial 0 f (pt (6 * t)) * 6) := by
    unfold dthetaTF
    rw [Q2_pt_SEM011, Feature.zsmul_pt]
    push_cast
    ring
  rw [e]
  exact h3

lemma hasDerivAt_UrealF_coord_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {f : Torus 1 → ℝ}
    (hf : IsSmoothPeriodic f) (j : Fin 2) (t : ℝ) :
    HasDerivAt (fun s => UrealF L η f s j)
      (UprimeF L η f (coordPartial 0 f) (pt t) j) t := by
  have h := (hasDerivAt_thetaF_SEM011 L η hf t).const_mul (2 * π)
  have hU : UfeatF L η f (pt t) = UrealF L η f t := UfeatF_pt hL η f t
  fin_cases j
  · have := h.cos
    have e : UprimeF L η f (coordPartial 0 f) (pt t) 0 =
        -Real.sin (2 * π * thetaF L η f t) * (2 * π * dthetaTF L η (coordPartial 0 f) (pt t)) := by
      unfold UprimeF
      simp [Jrot, hU, UrealF]
      ring
    show HasDerivAt (fun s => UrealF L η f s 0) (UprimeF L η f (coordPartial 0 f) (pt t) 0) t
    rw [e]
    exact this
  · have := h.sin
    have e : UprimeF L η f (coordPartial 0 f) (pt t) 1 =
        Real.cos (2 * π * thetaF L η f t) * (2 * π * dthetaTF L η (coordPartial 0 f) (pt t)) := by
      unfold UprimeF
      simp [Jrot, hU, UrealF]
      ring
    show HasDerivAt (fun s => UrealF L η f s 1) (UprimeF L η f (coordPartial 0 f) (pt t) 1) t
    rw [e]
    exact this

lemma coordPartial_UfeatF_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {f : Torus 1 → ℝ}
    (hf : IsSmoothPeriodic f) (j : Fin 2) (y : Torus 1) :
    coordPartial 0 (fun y => UfeatF L η f y j) y = UprimeF L η f (coordPartial 0 f) y j := by
  have hs := isSmoothPeriodic_UfeatF_SEM011 hL η hf j
  obtain ⟨t, rfl⟩ : ∃ t, y = pt t := ⟨SharpLSI.secT y 0, (Feature.pt_secT y).symm⟩
  have h1 := hasDerivAt_smooth_one hs t
  have e : (fun s : ℝ => UfeatF L η f (torusLift fun _ => s) j) = fun s => UrealF L η f s j := by
    funext s
    exact congrArg (fun v => v j) (UfeatF_pt hL η f s)
  rw [e] at h1
  exact h1.unique (hasDerivAt_UrealF_coord_SEM011 hL η hf j t)


/-! ### Smooth product kernels on the two-torus -/

open DGPS.Analysis.RateTopology (q1 q2 pairPt pr q1_lift q2_lift)

lemma isSmoothPeriodic_prodKernel_SEM011 {U : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hs : ∀ j : Fin 2, IsSmoothPeriodic fun y => U y j) :
    IsSmoothPeriodic (fun p : Torus 2 => prodKernel U (q1 p) (q2 p)) := by
  have h : ((fun p : Torus 2 => prodKernel U (q1 p) (q2 p)) ∘ torusLift) =
      fun v : Fin 2 → ℝ => Model.kappa * (1 -
        (((fun y => U y 0) ∘ torusLift) (pr 0 v) * ((fun y => U y 0) ∘ torusLift) (pr 1 v) +
         ((fun y => U y 1) ∘ torusLift) (pr 0 v) * ((fun y => U y 1) ∘ torusLift) (pr 1 v))) := by
    funext v
    simp only [Function.comp_apply, prodKernel, q1_lift, q2_lift, Model.inner_two]
  unfold IsSmoothPeriodic
  rw [h]
  have a : ∀ (j : Fin 2) (k : Fin 2), ContDiff ℝ ∞
      (fun v : Fin 2 → ℝ => ((fun y => U y j) ∘ torusLift) (pr k v)) :=
    fun j k => (hs j).comp (pr k).contDiff
  exact contDiff_const.mul (contDiff_const.sub (((a 0 0).mul (a 0 1)).add ((a 1 0).mul (a 1 1))))

lemma isSmoothPeriodic_kernel_const_SEM011 {U : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hs : ∀ j : Fin 2, IsSmoothPeriodic fun y => U y j) (c : EuclideanSpace ℝ (Fin 2)) :
    IsSmoothPeriodic (fun x => Model.kappa * (1 - inner ℝ (U x) c)) := by
  have h : ((fun x => Model.kappa * (1 - inner ℝ (U x) c)) ∘ torusLift) =
      fun v : Fin 1 → ℝ => Model.kappa * (1 -
        (((fun y => U y 0) ∘ torusLift) v * c 0 + ((fun y => U y 1) ∘ torusLift) v * c 1)) := by
    funext v
    simp only [Function.comp_apply, Model.inner_two]
  unfold IsSmoothPeriodic
  rw [h]
  exact contDiff_const.mul (contDiff_const.sub (((ContDiff.mul (hs 0) contDiff_const)).add
    (ContDiff.mul (hs 1) contDiff_const)))

lemma coordPartial_kernel_const_SEM011 {U U' : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hs : ∀ j : Fin 2, IsSmoothPeriodic fun y => U y j)
    (hd : ∀ (j : Fin 2) (y : Torus 1), coordPartial 0 (fun y => U y j) y = U' y j)
    (c : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) :
    coordPartial 0 (fun x => Model.kappa * (1 - inner ℝ (U x) c)) x =
      -(Model.kappa * inner ℝ (U' x) c) := by
  obtain ⟨t, rfl⟩ : ∃ t, x = pt t := ⟨SharpLSI.secT x 0, (Feature.pt_secT x).symm⟩
  have hF := hasDerivAt_smooth_one (isSmoothPeriodic_kernel_const_SEM011 hs c) t
  have h0 := hasDerivAt_smooth_one (hs 0) t
  have h1 := hasDerivAt_smooth_one (hs 1) t
  have H := (((h0.mul_const (c 0)).add (h1.mul_const (c 1))).const_sub 1).const_mul Model.kappa
  have e : (fun s : ℝ => Model.kappa * (1 - inner ℝ (U (torusLift fun _ => s)) c)) =
      fun s => Model.kappa * (1 - (U (torusLift fun _ => s) 0 * c 0 +
        U (torusLift fun _ => s) 1 * c 1)) := by
    funext s; rw [Model.inner_two]
  have e2 := hF.unique (by
    rw [e]
    exact H)
  rw [show pt t = torusLift fun _ => t from rfl, e2, hd 0, hd 1, Model.inner_two]
  ring


/-! ### Gradients of smooth product kernels -/

open DGPS.Analysis.RateTopology (pairPt_q q1_pairPt q2_pairPt)

lemma coordPartial_prodKernel_x_SEM011 {U U' : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hs : ∀ j : Fin 2, IsSmoothPeriodic fun y => U y j)
    (hd : ∀ (j : Fin 2) (y : Torus 1), coordPartial 0 (fun y => U y j) y = U' y j)
    (x y : Torus 1) :
    coordPartial 0 (fun p : Torus 2 => prodKernel U (q1 p) (q2 p)) (pairPt x y) =
      prodGradX U U' x y := by
  obtain ⟨-, h⟩ := Model.sect1 (isSmoothPeriodic_prodKernel_SEM011 hs) y
  rw [← h x]
  have e : (fun x' => (fun p : Torus 2 => prodKernel U (q1 p) (q2 p)) (pairPt x' y)) =
      fun x' => Model.kappa * (1 - inner ℝ (U x') (U y)) := by
    funext x'; simp [prodKernel, q1_pairPt, q2_pairPt]
  rw [e, coordPartial_kernel_const_SEM011 hs hd (U y) x]
  rfl

lemma coordPartial_prodKernel_y_SEM011 {U U' : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hs : ∀ j : Fin 2, IsSmoothPeriodic fun y => U y j)
    (hd : ∀ (j : Fin 2) (y : Torus 1), coordPartial 0 (fun y => U y j) y = U' y j)
    (x y : Torus 1) :
    coordPartial 1 (fun p : Torus 2 => prodKernel U (q1 p) (q2 p)) (pairPt x y) =
      prodGradY U U' x y := by
  obtain ⟨-, h⟩ := Model.sect2 (isSmoothPeriodic_prodKernel_SEM011 hs) x
  rw [← h y]
  have e : (fun y' => (fun p : Torus 2 => prodKernel U (q1 p) (q2 p)) (pairPt x y')) =
      fun y' => Model.kappa * (1 - inner ℝ (U y') (U x)) := by
    funext y'; simp [prodKernel, q1_pairPt, q2_pairPt, real_inner_comm]
  rw [e, coordPartial_kernel_const_SEM011 hs hd (U x) y, prodGradY, real_inner_comm]

/-- The explicit gradient field of the product kernel. -/
noncomputable def prodGrad_SEM011 (U U' : Torus 1 → EuclideanSpace ℝ (Fin 2)) (p : Torus 2) : Tangent 2 :=
  !₂[prodGradX U U' (q1 p) (q2 p), prodGradY U U' (q1 p) (q2 p)]

lemma smoothGrad_prodKernel_SEM011 {U U' : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hs : ∀ j : Fin 2, IsSmoothPeriodic fun y => U y j)
    (hd : ∀ (j : Fin 2) (y : Torus 1), coordPartial 0 (fun y => U y j) y = U' y j) :
    smoothGrad (fun p : Torus 2 => prodKernel U (q1 p) (q2 p)) = prodGrad_SEM011 U U' := by
  funext p
  have hp : pairPt (q1 p) (q2 p) = p := pairPt_q p
  ext j
  fin_cases j
  · simp only [smoothGrad_apply, prodGrad_SEM011]
    have := coordPartial_prodKernel_x_SEM011 hs hd (q1 p) (q2 p)
    rw [hp] at this
    simpa using this
  · simp only [smoothGrad_apply, prodGrad_SEM011]
    have := coordPartial_prodKernel_y_SEM011 hs hd (q1 p) (q2 p)
    rw [hp] at this
    simpa using this

lemma isWeakGradientLp_of_smooth_SEM011 (p : ℝ≥0∞) {φ : Torus 2 → ℝ} (hφ : IsSmoothPeriodic φ) :
    IsWeakGradientLp p φ (smoothGrad φ) where
  memLp := hφ.memLp_top.mono_exponent le_top
  memLp_grad := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      hφ.continuous_smoothGrad.continuousOn
    exact (memLp_top_of_bound hφ.continuous_smoothGrad.aestronglyMeasurable C
      (Eventually.of_forall fun x => hC x (mem_univ x))).mono_exponent le_top
  ibp ψ hψ j := integral_mul_coordPartial_of_smooth hφ hψ j

lemma isWeakGradientLp_prodKernel_SEM011 (p : ℝ≥0∞) {U U' : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hs : ∀ j : Fin 2, IsSmoothPeriodic fun y => U y j)
    (hd : ∀ (j : Fin 2) (y : Torus 1), coordPartial 0 (fun y => U y j) y = U' y j) :
    IsWeakGradientLp p (fun p : Torus 2 => prodKernel U (q1 p) (q2 p)) (prodGrad_SEM011 U U') := by
  rw [← smoothGrad_prodKernel_SEM011 hs hd]
  exact isWeakGradientLp_of_smooth_SEM011 p (isSmoothPeriodic_prodKernel_SEM011 hs)


/-! ### Rough kernels attached to unit-norm features and rate transport -/

open DGPS.Examples.RoughBoundary.Landscape (RoughLandscapeCertificate)
open DGPS.Analysis.RateTopology (RoughKernelClass scalarRate_eq_of_providers
  speciesRate_eq_of_providers)

lemma interactionData_ext_SEM011 {A B : InteractionData 1} (hV : A.V = B.V) (hW : A.W = B.W) :
    A = B := by
  cases A; cases B
  simp only at hV hW
  subst hV; subst hW
  rfl

/-- The rough kernel `κ (1 - ⟪U x, U y⟫)` of a continuous unit-norm feature with `W^{1,1}`
regularity. -/
noncomputable def kernelOfFeature_SEM011 (U : Torus 1 → EuclideanSpace ℝ (Fin 2)) (hc : Continuous U)
    (hn : ∀ y, ‖U y‖ = 1)
    (hsob : ∃ G, IsWeakGradientLp 1 (fun p : Torus 2 => prodKernel U (q1 p) (q2 p)) G) :
    RoughKernelClass where
  W := fun p => prodKernel U (q1 p) (q2 p)
  continuous := continuous_const.mul (continuous_const.sub
    ((hc.comp Model.continuous_q1).inner (hc.comp Model.continuous_q2)))
  symm := fun x y => by
    simp only [prodKernel, q1_pairPt, q2_pairPt, real_inner_comm]
  diag := fun x => by
    simp only [prodKernel, q1_pairPt, q2_pairPt, real_inner_self_eq_norm_sq, hn]
    norm_num
  sobolev := hsob

lemma kernelOfFeature_W_SEM011 (U : Torus 1 → EuclideanSpace ℝ (Fin 2)) (hc : Continuous U)
    (hn : ∀ y, ‖U y‖ = 1) (hsob) :
    (kernelOfFeature_SEM011 U hc hn hsob).W = fun p => prodKernel U (q1 p) (q2 p) := rfl

lemma kernelOfFeature_kernel_SEM011 (U : Torus 1 → EuclideanSpace ℝ (Fin 2)) (hc : Continuous U)
    (hn : ∀ y, ‖U y‖ = 1) (hsob) (x y : Torus 1) :
    (kernelOfFeature_SEM011 U hc hn hsob).kernel x y = prodKernel U x y := by
  simp [RoughKernelClass.kernel, kernelOfFeature_SEM011, q1_pairPt, q2_pairPt]

lemma toInteraction_of_kernel_SEM011 (K : RoughKernelClass) (A : InteractionData 1)
    (hV : A.V = fun _ => 0) (hW : ∀ x y, K.kernel x y = A.W x y) : K.toInteraction = A :=
  interactionData_ext_SEM011 hV.symm (funext fun x => funext fun y => hW x y)

lemma scalarRate_congr_SEM011 {A A' : InteractionData 1} (h : A = A') (b : AbsoluteDrift A)
    (b' : AbsoluteDrift A') : scalarRate A b = scalarRate A' b' := by
  subst h; exact scalarRate_eq_of_providers b b'

lemma speciesRate_congr_SEM011 {A A' : InteractionData 1} (h : A = A') (b : AbsoluteDrift A)
    (b' : AbsoluteDrift A') : speciesRate A b = speciesRate A' b' := by
  subst h; exact speciesRate_eq_of_providers b b'

lemma toInteraction_kernelOfFeature_SEM011 (U : Torus 1 → EuclideanSpace ℝ (Fin 2)) (hc : Continuous U)
    (hn : ∀ y, ‖U y‖ = 1) (hsob) :
    (kernelOfFeature_SEM011 U hc hn hsob).toInteraction = featureData hc hn :=
  toInteraction_of_kernel_SEM011 _ _ rfl fun x y => kernelOfFeature_kernel_SEM011 U hc hn hsob x y

/-- The smooth rough kernel of a smooth profile `f`. -/
noncomputable def smoothKernel_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {f : Torus 1 → ℝ}
    (hf : IsSmoothPeriodic f) : RoughKernelClass :=
  kernelOfFeature_SEM011 (UfeatF L η f)
    (continuous_of_smoothCoords (isSmoothPeriodic_UfeatF_SEM011 hL η hf)) (norm_UfeatF L η f)
    ⟨_, isWeakGradientLp_prodKernel_SEM011 1 (isSmoothPeriodic_UfeatF_SEM011 hL η hf)
      (coordPartial_UfeatF_SEM011 hL η hf)⟩

lemma smoothKernel_W_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) :
    (smoothKernel_SEM011 hL η hf).W = fun p => prodKernel (UfeatF L η f) (q1 p) (q2 p) := rfl

/-- Both rates of a smooth-profile kernel vanish, for every provider. -/
theorem smoothKernel_rates_zero_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {f : Torus 1 → ℝ}
    (hf : IsSmoothPeriodic f) (hU : RoughLandscapeCertificate (UfeatF L η f))
    (b : AbsoluteDrift (smoothKernel_SEM011 hL η hf).toInteraction) :
    scalarRate (smoothKernel_SEM011 hL η hf).toInteraction b = 0 ∧
      speciesRate (smoothKernel_SEM011 hL η hf).toInteraction b = 0 := by
  have hs := isSmoothPeriodic_UfeatF_SEM011 hL η hf
  have hn := norm_UfeatF L η f
  obtain ⟨-, t, -, hcrit, hpos⟩ := haar_and_well_of_certificate hU
  have h := toInteraction_kernelOfFeature_SEM011 (UfeatF L η f) (continuous_of_smoothCoords hs) hn
    ⟨_, isWeakGradientLp_prodKernel_SEM011 1 hs (coordPartial_UfeatF_SEM011 hL η hf)⟩
  have b' : AbsoluteDrift (featureData (continuous_of_smoothCoords hs) hn) := h ▸ b
  obtain ⟨-, -, -, hr1, hr2, -⟩ :=
    smooth_positive_gap_gibbs_competitor_forces_both_rates_zero hs hn hU hcrit hpos b'
  exact ⟨(scalarRate_congr_SEM011 h b b').trans hr1, (speciesRate_congr_SEM011 h b b').trans hr2⟩

/-- The primary rough kernel `W = κ (1 - ⟪U_{L,ε}(x), U_{L,ε}(y)⟫)`. -/
noncomputable def primaryKernel_SEM011 {L : ℝ} (hL : 0 < L) (ε : ℝ) : RoughKernelClass :=
  kernelOfFeature_SEM011 (Feature.Ufeat L ε) (Feature.continuous_Ufeat hL ε) (Feature.norm_Ufeat L ε)
    ⟨Model.gradW L ε, by
      have h := Model.isWeakGradientLp_Wtor hL ε (p := 1) le_rfl one_lt_two
      rw [ENNReal.ofReal_one] at h
      exact h⟩

lemma primaryKernel_W_SEM011 {L : ℝ} (hL : 0 < L) (ε : ℝ) : (primaryKernel_SEM011 hL ε).W = Model.Wtor L ε := rfl

lemma toInteraction_primaryKernel_SEM011 {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    (primaryKernel_SEM011 hL ε).toInteraction = Model.modelData hL ε :=
  toInteraction_of_kernel_SEM011 _ _ rfl fun x y => kernelOfFeature_kernel_SEM011 _ _ _ _ x y


/-! ### Hölder regularity on the two-torus from pair bounds -/

lemma dist_q1_le_SEM011 (z z' : Torus 2) : dist (q1 z) (q1 z') ≤ dist z z' := by
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  exact dist_le_pi_dist z z' 0

lemma dist_q2_le_SEM011 (z z' : Torus 2) : dist (q2 z) (q2 z') ≤ dist z z' := by
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  exact dist_le_pi_dist z z' 1

lemma torusDist_le_dist_one_SEM011 (x y : Torus 1) : DGPS.torusDist x y ≤ dist x y := by
  simpa using (DGPS.torusDist_comparison x y).2

lemma abs_sub_le_of_pair_bound_SEM011 {D : Torus 2 → ℝ} {M α : ℝ} (hM : 0 ≤ M) (hα : 0 ≤ α)
    (h : ∀ x y x' y' : Torus 1, |D (pairPt x y) - D (pairPt x' y')| ≤
      M * Real.sqrt (DGPS.torusDist x x' ^ 2 + DGPS.torusDist y y' ^ 2) ^ α) (z z' : Torus 2) :
    |D z - D z'| ≤ M * Real.sqrt 2 ^ α * dist z z' ^ α := by
  have h1 := h (q1 z) (q2 z) (q1 z') (q2 z')
  rw [pairPt_q, pairPt_q] at h1
  refine h1.trans ?_
  have ha : DGPS.torusDist (q1 z) (q1 z') ≤ dist z z' :=
    (torusDist_le_dist_one_SEM011 _ _).trans (dist_q1_le_SEM011 z z')
  have hb : DGPS.torusDist (q2 z) (q2 z') ≤ dist z z' :=
    (torusDist_le_dist_one_SEM011 _ _).trans (dist_q2_le_SEM011 z z')
  have hsq : Real.sqrt (DGPS.torusDist (q1 z) (q1 z') ^ 2 + DGPS.torusDist (q2 z) (q2 z') ^ 2) ≤
      Real.sqrt 2 * dist z z' := by
    rw [← Real.sqrt_sq (dist_nonneg (x := z) (y := z')), ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    have h0a := dist_nonneg.trans (DGPS.torusDist_comparison (q1 z) (q1 z')).1
    have h0b := dist_nonneg.trans (DGPS.torusDist_comparison (q2 z) (q2 z')).1
    nlinarith
  calc M * Real.sqrt (DGPS.torusDist (q1 z) (q1 z') ^ 2 + DGPS.torusDist (q2 z) (q2 z') ^ 2) ^ α
      ≤ M * (Real.sqrt 2 * dist z z') ^ α := by
        gcongr
    _ = _ := by rw [Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg]; ring

lemma holderWith_of_dist_le_SEM011 {X : Type*} [PseudoMetricSpace X] {f : X → ℝ} {C r : ℝ≥0}
    (h : ∀ x y, dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ)) : HolderWith C r f := by
  intro x y
  rw [edist_dist, edist_dist]
  have := h x y
  calc ENNReal.ofReal (dist (f x) (f y)) ≤ ENNReal.ofReal (C * dist x y ^ (r : ℝ)) :=
        ENNReal.ofReal_le_ofReal this
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg dist_nonneg
        r.coe_nonneg]
      simp

lemma exists_holderWith_of_pair_bound_SEM011 {D : Torus 2 → ℝ} {M : ℝ} {α : ℝ≥0} (hM : 0 ≤ M)
    (h : ∀ x y x' y' : Torus 1, |D (pairPt x y) - D (pairPt x' y')| ≤
      M * Real.sqrt (DGPS.torusDist x x' ^ 2 + DGPS.torusDist y y' ^ 2) ^ (α : ℝ)) :
    ∃ C : ℝ≥0, HolderWith C α D := by
  refine ⟨⟨M * Real.sqrt 2 ^ (α : ℝ), by positivity⟩, holderWith_of_dist_le_SEM011 fun z z' => ?_⟩
  rw [Real.dist_eq]
  exact abs_sub_le_of_pair_bound_SEM011 hM α.coe_nonneg h z z'


/-! ### Hölder membership of the product kernels -/

/-- A fixed unit vector. -/
noncomputable def e0_SEM011 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

lemma norm_e0_SEM011 : ‖e0_SEM011‖ = 1 := by simp [e0_SEM011]

lemma prodKernel_const_SEM011 (x y : Torus 1) : prodKernel (fun _ => e0_SEM011) x y = 0 := by
  simp [prodKernel, norm_e0_SEM011]

lemma kernel_pair_bound_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    {f : Torus 1 → ℝ} (hf : TorusHolderBdd α f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y x' y' : Torus 1,
      |prodKernel (UfeatF L η f) x y - prodKernel (UfeatF L η f) x' y'| ≤
        M * Real.sqrt (DGPS.torusDist x x' ^ 2 + DGPS.torusDist y y' ^ 2) ^ α := by
  have hUt := holder_UfeatF hL η h0 h1 hf
  have hc : VecHolderBdd α (fun _ => e0_SEM011) := ⟨0, le_rfl, fun a b => by simp⟩
  have key := (quantitative_product_kernel_convergence (U := fun _ => e0_SEM011) (Ut := UfeatF L η f)
    (U' := fun _ => 0) (Ut' := fun _ => 0) (fun _ => norm_e0_SEM011) (norm_UfeatF L η f)).1 α h0 hc hUt
  have hk := kappa_nonneg
  refine ⟨Model.kappa * (2 * vecHolderSeminorm α (fun z => UfeatF L η f z - e0_SEM011) +
    vecSupNorm (fun z => UfeatF L η f z - e0_SEM011) *
      (vecHolderSeminorm α (UfeatF L η f) + vecHolderSeminorm α (fun _ => e0_SEM011))), by
    have := vecHolderSeminorm_nonneg α (fun z => UfeatF L η f z - e0_SEM011)
    have := vecHolderSeminorm_nonneg α (UfeatF L η f)
    have := vecHolderSeminorm_nonneg α (fun _ => e0_SEM011)
    have := vecSupNorm_nonneg (fun z => UfeatF L η f z - e0_SEM011)
    positivity, fun x y x' y' => ?_⟩
  have := key.2.2.2 x y x' y'
  simpa [prodKernel_const_SEM011] using this

lemma exists_holderWith_kernelOfProfile_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {α : ℝ≥0}
    (h0 : 0 < (α : ℝ)) (h1 : (α : ℝ) < 1) {f : Torus 1 → ℝ} (hf : TorusHolderBdd α f) :
    ∃ C : ℝ≥0, HolderWith C α (fun p : Torus 2 => prodKernel (UfeatF L η f) (q1 p) (q2 p)) := by
  obtain ⟨M, hM, hb⟩ := kernel_pair_bound_SEM011 hL η h0 h1 hf
  exact exists_holderWith_of_pair_bound_SEM011 hM fun x y x' y' => by
    simpa [q1_pairPt, q2_pairPt] using hb x y x' y'

lemma holderBdd_mollify_gT_SEM011 {h : ℝ} (hh : 0 < h) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    TorusHolderBdd α (mollify h Spikes.gT) := by
  obtain ⟨K, hK0, hK⟩ := holder_gT h0 h1
  exact ⟨K, hK0, fun x y => abs_mollify_sub_le hh continuous_gT hK x y⟩

/-! ### Uniform bounds for the feature difference under mollification -/

lemma feature_diff_bounds_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {α β : ℝ} (h0 : 0 < α) (hαβ : α < β)
    (hβ1 : β < 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ vecHolderSeminorm α (UfeatF L η Spikes.gT) ≤ B ∧
      ∀ h : ℝ, 0 < h → h < 1 / 4 →
        vecSupNorm (Efun L η Spikes.gT (mollify h Spikes.gT)) ≤ A * h ^ (β - α) ∧
        vecHolderSeminorm α (Efun L η Spikes.gT (mollify h Spikes.gT)) ≤ A * h ^ (β - α) ∧
        vecHolderSeminorm α (UfeatF L η (mollify h Spikes.gT)) ≤ B := by
  have hα1 : α < 1 := hαβ.trans hβ1
  have hβ0 : 0 < β := h0.trans hαβ
  have hgβ := holder_gT hβ0 hβ1
  have hgα := holder_gT h0 hα1
  have hk0 : 0 ≤ torusHolderSeminorm β Spikes.gT := torusHolderSeminorm_nonneg _ _
  have hu0 := vecHolderSeminorm_nonneg α (UfeatF L η Spikes.gT)
  have hUf := holder_UfeatF hL η h0 hα1 hgα
  have hH := (DGPS.Analysis.PeriodicMollification.same_exponent_holder_convergence_with_an_intermediate_exponent
    h0 hαβ hβ1 hgβ).1
  have hE5 := quantitative_phase_composition_continuity hL η
  have h6 : (0 : ℝ) ≤ 6 ^ α := by positivity
  have hpi := Real.pi_pos
  set k := torusHolderSeminorm β Spikes.gT with hk
  set u := vecHolderSeminorm α (UfeatF L η Spikes.gT) with hu
  have hc0 : 0 ≤ 2 * π * |η| * k := by positivity
  have hA0 : 0 ≤ 2 * π * |η| * k * (2 * 6 ^ α + u + 1) + u := by positivity
  refine ⟨2 * π * |η| * k * (2 * 6 ^ α + u + 1) + u,
    2 * π * |η| * k * (2 * 6 ^ α + u + 1) + u + u, hA0, by positivity, by linarith, ?_⟩
  intro h hh hh4
  have hh1 : h ≤ 1 := by linarith
  have hγ : 0 < β - α := by linarith
  have hx0 : 0 ≤ h ^ (β - α) := by positivity
  have hx1 : h ^ (β - α) ≤ 1 := Real.rpow_le_one hh.le hh1 hγ.le
  have hxb : h ^ β ≤ h ^ (β - α) :=
    Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)
  obtain ⟨hs, -, hsem, -⟩ := hH h hh hh4
  have hmol : TorusHolderBdd α (mollify h Spikes.gT) := holderBdd_mollify_gT_SEM011 hh h0 hα1
  obtain ⟨h1a, h1b⟩ := hE5.1 Spikes.gT (mollify h Spikes.gT) continuous_gT
    (continuous_mollify_gT hh)
  obtain ⟨h2a, h2b⟩ := hE5.2.1 α h0 hα1 Spikes.gT (mollify h Spikes.gT) hgα hmol
  have hT0 : torusSupNorm (fun y => mollify h Spikes.gT y - Spikes.gT y) ≤ k * h ^ (β - α) :=
    hs.trans (by gcongr)
  have hdn : torusSupNorm (phaseDiff η Spikes.gT (mollify h Spikes.gT)) ≤
      |η| * (k * h ^ (β - α)) := by
    rw [h1b]; gcongr
  have hd1 : torusHolderSeminorm α (phaseDiff η Spikes.gT (mollify h Spikes.gT)) ≤
      |η| * 6 ^ α * (2 * k * h ^ (β - α)) :=
    h2b.trans (by gcongr)
  have hdn0 := torusSupNorm_nonneg (phaseDiff η Spikes.gT (mollify h Spikes.gT))
  have hAx : 2 * π * |η| * k * (2 * 6 ^ α + u) ≤ 2 * π * |η| * k * (2 * 6 ^ α + u + 1) + u := by
    nlinarith
  have hS : vecSupNorm (Efun L η Spikes.gT (mollify h Spikes.gT)) ≤
      (2 * π * |η| * k * (2 * 6 ^ α + u + 1) + u) * h ^ (β - α) := by
    calc _ ≤ 2 * π * (|η| * (k * h ^ (β - α))) := h1a.trans (by gcongr)
      _ = (2 * π * |η| * k) * h ^ (β - α) := by ring
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ hx0
        nlinarith
  have hE : vecHolderSeminorm α (Efun L η Spikes.gT (mollify h Spikes.gT)) ≤
      (2 * π * |η| * k * (2 * 6 ^ α + u + 1) + u) * h ^ (β - α) := by
    calc _ ≤ 2 * π * (|η| * 6 ^ α * (2 * k * h ^ (β - α)) +
          |η| * (k * h ^ (β - α)) * u) := h2a.trans (by gcongr)
      _ = (2 * π * |η| * k * (2 * 6 ^ α + u)) * h ^ (β - α) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hAx hx0
  refine ⟨hS, hE, ?_⟩
  have hUt : VecHolderBdd α (UfeatF L η (mollify h Spikes.gT)) := holder_UfeatF hL η h0 hα1 hmol
  have hEb : VecHolderBdd α (Efun L η Spikes.gT (mollify h Spikes.gT)) :=
    vecHolderBdd_sub' hUt hUf
  have hdec : UfeatF L η (mollify h Spikes.gT) =
      fun y => Efun L η Spikes.gT (mollify h Spikes.gT) y + UfeatF L η Spikes.gT y := by
    funext y; simp [Efun]
  rw [hdec]
  refine (vecHolderSeminorm_add_le' hEb hUf).trans ?_
  have : (2 * π * |η| * k * (2 * 6 ^ α + u + 1) + u) * h ^ (β - α) ≤
      2 * π * |η| * k * (2 * 6 ^ α + u + 1) + u := by
    nlinarith
  linarith

/-! ### Hölder-topology convergence from uniform bounds -/

open DGPS.Analysis.RateTopology (HolderKernel holderEmbed holderTopology holderQuotient
  holderEmbed_isEmbedding)

lemma tendsto_holderKernel_SEM011 {α : ℝ≥0} (Kj : ℕ → HolderKernel α) (K : HolderKernel α) (c : ℕ → ℝ)
    (hc : Tendsto c atTop (𝓝 0))
    (hsup : ∀ j z, |(Kj j).1.W z - K.1.W z| ≤ c j)
    (hhol : ∀ j z z', |((Kj j).1.W z - K.1.W z) - ((Kj j).1.W z' - K.1.W z')| ≤
      c j * dist z z' ^ (α : ℝ)) :
    @Tendsto ℕ (HolderKernel α) Kj atTop (@nhds _ (holderTopology α) K) := by
  let _ : TopologicalSpace (HolderKernel α) := holderTopology α
  have hc0 : ∀ j, 0 ≤ c j := fun j =>
    (abs_nonneg _).trans (hsup j (Classical.arbitrary (Torus 2)))
  rw [(holderEmbed_isEmbedding α).tendsto_nhds_iff, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hc
  rw [Prod.dist_eq]
  refine max_le ?_ ?_
  · rw [dist_eq_norm]
    refine lp.norm_le_of_forall_le (hc0 j) fun z => ?_
    show ‖(Kj j).1.W z - K.1.W z‖ ≤ c j
    rw [Real.norm_eq_abs]
    exact hsup j z
  · rw [dist_eq_norm]
    refine lp.norm_le_of_forall_le (hc0 j) fun z => ?_
    simp only [holderEmbed, Function.comp_apply, lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs,
      holderQuotient]
    by_cases hz : z.1 = z.2
    · simp [hz, hc0 j]
    · have hd : 0 < dist z.1 z.2 := dist_pos.mpr hz
      have hpos : 0 < dist z.1 z.2 ^ (α : ℝ) := Real.rpow_pos_of_pos hd _
      have e : ((Kj j).1.W z.1 - (Kj j).1.W z.2) / dist z.1 z.2 ^ (α : ℝ) -
          (K.1.W z.1 - K.1.W z.2) / dist z.1 z.2 ^ (α : ℝ) =
          (((Kj j).1.W z.1 - K.1.W z.1) - ((Kj j).1.W z.2 - K.1.W z.2)) /
            dist z.1 z.2 ^ (α : ℝ) := by
        field_simp
        ring
      rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      exact hhol j z.1 z.2

/-! ### Uniform estimates for the kernel difference -/

lemma kernel_diff_estimates_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℝ, 0 < h → h < 1 / 4 →
      (∀ z : Torus 2,
        |prodKernel (UfeatF L η (mollify h Spikes.gT)) (q1 z) (q2 z) -
          prodKernel (UfeatF L η Spikes.gT) (q1 z) (q2 z)| ≤ M * h ^ ((α + 1) / 2 - α)) ∧
      (∀ z z' : Torus 2,
        |(prodKernel (UfeatF L η (mollify h Spikes.gT)) (q1 z) (q2 z) -
            prodKernel (UfeatF L η Spikes.gT) (q1 z) (q2 z)) -
          (prodKernel (UfeatF L η (mollify h Spikes.gT)) (q1 z') (q2 z') -
            prodKernel (UfeatF L η Spikes.gT) (q1 z') (q2 z'))| ≤
          M * h ^ ((α + 1) / 2 - α) * dist z z' ^ α) := by
  obtain ⟨A, B, hA, hB, hu, H⟩ := feature_diff_bounds_SEM011 hL η h0
    (show α < (α + 1) / 2 by linarith) (show (α + 1) / 2 < 1 by linarith)
  have hk := kappa_nonneg
  have hr1 : 1 ≤ Real.sqrt 2 ^ α := Real.one_le_rpow (by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) h0.le
  refine ⟨(Model.kappa * (2 * A + 2 * A * B) + 2 * Model.kappa * A) * Real.sqrt 2 ^ α,
    by positivity, fun h hh hh4 => ?_⟩
  obtain ⟨hS, hE, hUt⟩ := H h hh hh4
  have hh1 : h ≤ 1 := by linarith
  have hx0 : 0 ≤ h ^ ((α + 1) / 2 - α) := by positivity
  have hU : VecHolderBdd α (UfeatF L η Spikes.gT) := holder_UfeatF hL η h0 h1 (holder_gT h0 h1)
  have hUt' : VecHolderBdd α (UfeatF L η (mollify h Spikes.gT)) :=
    holder_UfeatF hL η h0 h1 (holderBdd_mollify_gT_SEM011 hh h0 h1)
  have hnU := norm_UfeatF L η Spikes.gT
  have hnUt := norm_UfeatF L η (mollify h Spikes.gT)
  have key := (quantitative_product_kernel_convergence (U := UfeatF L η Spikes.gT)
    (Ut := UfeatF L η (mollify h Spikes.gT)) (U' := fun _ => 0) (Ut' := fun _ => 0)
    hnU hnUt).1 α h0 hU hUt'
  have hS' : vecSupNorm (fun z => UfeatF L η (mollify h Spikes.gT) z - UfeatF L η Spikes.gT z) ≤
      A * h ^ ((α + 1) / 2 - α) := hS
  have hE' : vecHolderSeminorm α
      (fun z => UfeatF L η (mollify h Spikes.gT) z - UfeatF L η Spikes.gT z) ≤
      A * h ^ ((α + 1) / 2 - α) := hE
  have hS0 := vecSupNorm_nonneg (fun z => UfeatF L η (mollify h Spikes.gT) z - UfeatF L η Spikes.gT z)
  have hsU := vecHolderSeminorm_nonneg α (UfeatF L η Spikes.gT)
  have hsUt := vecHolderSeminorm_nonneg α (UfeatF L η (mollify h Spikes.gT))
  have hnorm : ∀ x, ‖UfeatF L η (mollify h Spikes.gT) x - UfeatF L η Spikes.gT x‖ ≤
      vecSupNorm (fun z => UfeatF L η (mollify h Spikes.gT) z - UfeatF L η Spikes.gT z) :=
    fun x => norm_le_vecSupNorm (fun z => norm_sub_le_two_vec hnU hnUt z) x
  have hBh : Model.kappa * (2 * vecHolderSeminorm α
        (fun z => UfeatF L η (mollify h Spikes.gT) z - UfeatF L η Spikes.gT z) +
      vecSupNorm (fun z => UfeatF L η (mollify h Spikes.gT) z - UfeatF L η Spikes.gT z) *
        (vecHolderSeminorm α (UfeatF L η (mollify h Spikes.gT)) +
          vecHolderSeminorm α (UfeatF L η Spikes.gT))) ≤
      (Model.kappa * (2 * A + 2 * A * B) + 2 * Model.kappa * A) * h ^ ((α + 1) / 2 - α) := by
    calc _ ≤ Model.kappa * (2 * (A * h ^ ((α + 1) / 2 - α)) +
          (A * h ^ ((α + 1) / 2 - α)) * (B + B)) := by gcongr
      _ = Model.kappa * (2 * A + 2 * A * B) * h ^ ((α + 1) / 2 - α) := by ring
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ hx0
        have : 0 ≤ 2 * Model.kappa * A := by positivity
        linarith
  refine ⟨fun z => ?_, fun z z' => ?_⟩
  · refine (abs_prodKernel_sub_le hnU hnUt (q1 z) (q2 z)).trans ?_
    have := hnorm (q1 z)
    have := hnorm (q2 z)
    calc _ ≤ Model.kappa * (2 * (A * h ^ ((α + 1) / 2 - α))) := by gcongr; linarith
      _ = 2 * Model.kappa * A * h ^ ((α + 1) / 2 - α) := by ring
      _ ≤ (Model.kappa * (2 * A + 2 * A * B) + 2 * Model.kappa * A) * h ^ ((α + 1) / 2 - α) := by
        refine mul_le_mul_of_nonneg_right ?_ hx0
        have : 0 ≤ Model.kappa * (2 * A + 2 * A * B) := by positivity
        linarith
      _ ≤ _ := by
        have hM0 : 0 ≤ Model.kappa * (2 * A + 2 * A * B) + 2 * Model.kappa * A := by positivity
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hM0 hr1) hx0
  · have hM : 0 ≤ (Model.kappa * (2 * A + 2 * A * B) + 2 * Model.kappa * A) *
        h ^ ((α + 1) / 2 - α) := by positivity
    have := abs_sub_le_of_pair_bound_SEM011 (D := fun z : Torus 2 =>
        prodKernel (UfeatF L η (mollify h Spikes.gT)) (q1 z) (q2 z) -
          prodKernel (UfeatF L η Spikes.gT) (q1 z) (q2 z)) hM h0.le
      (fun x y x' y' => by
        simp only [q1_pairPt, q2_pairPt]
        exact (key.2.2.2 x y x' y').trans (by gcongr)) z z'
    refine this.trans (le_of_eq ?_)
    ring

end DGPS.Examples.RoughBoundary.Semicontinuity
