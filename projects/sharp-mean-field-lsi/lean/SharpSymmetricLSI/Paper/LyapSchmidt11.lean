import SharpSymmetricLSI.Paper.LyapSchmidt10
import SharpSymmetricLSI.Paper.ProductFisherGrad
import SharpSymmetricLSI.Paper.UpperApprox
import SharpSymmetricLSI.Paper.EntFinite

/-!
# Section 4.2 (lane s42; R14): the dissipation on the graph, (4.6)

Let `μ = p m` be a minimizer, `h` continuous with `1 + h > 0`, `μ(h) = 0` and
`log(1+h) + T h = c + ∑ bᵢ φᵢ`. For `ρ = p (1 + h)`:
`log ρ = const - V - W * (p (1 + h + ∑ bᵢ φᵢ))`, hence (weak gradients)
`2∇√ρ + √ρ ∇(V + W*ρ) = -√ρ ∑ bᵢ ∇(W * (p φᵢ))`, and
`D(ρ) ≤ C_D |b|²` (manuscript (4.6): `D ≤ C |∇φ|²`), with `C_D` independent of `h`.
-/

noncomputable section
open MeasureTheory Filter Real Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section diss
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)
include hyp hμ

/-- Integrals against `μ` as integrals against `p m`. -/
theorem integral_minimizer (F : Torus d → ℝ) :
    ∫ y, F y ∂(μ : Measure (Torus d)) =
      ∫ y, elDens V W (μ : Measure (Torus d)) y * F y ∂haar d := by
  obtain ⟨-, hp0, hp1⟩ := elDensity_props hyp (μ : Measure (Torus d))
  have hμp := minimizer_eq_elDensity hyp hμ
  calc ∫ y, F y ∂(μ : Measure (Torus d)) =
      ∫ y, F y ∂densMeasure (elDens V W (μ : Measure (Torus d))) := by
        conv_lhs => rw [hμp]
    _ = _ := integral_densMeasure' (fun x => (hp0 x).le) hp1 F

/-- `∫ W(x,y) u(y) dμ(y) = (W * (p u))(x)`. -/
theorem integral_W_mul_eq_convDens (u : Torus d → ℝ) (x : Torus d) :
    ∫ y, W x y * u y ∂(μ : Measure (Torus d)) =
      convDens W (fun y => elDens V W (μ : Measure (Torus d)) y * u y) x := by
  rw [integral_minimizer hyp hμ]
  unfold convDens
  congr 1; funext y; ring

/-- `T u = W * (p u) - const`. -/
theorem Top_eq_convDens (u : Torus d → ℝ) :
    ∃ K : ℝ, ∀ x, Top W (μ : Measure (Torus d)) u x =
      convDens W (fun y => elDens V W (μ : Measure (Torus d)) y * u y) x - K :=
  ⟨_, fun x => by unfold Top; rw [integral_W_mul_eq_convDens hyp hμ]⟩

/-- `u ∈ L¹(μ)` gives `p u ∈ L¹(m)`. -/
theorem integrable_elDens_mul {u : Torus d → ℝ} (hu : Integrable u (μ : Measure (Torus d))) :
    Integrable (fun y => elDens V W (μ : Measure (Torus d)) y * u y) (haar d) := by
  set p := elDens V W (μ : Measure (Torus d)) with hp
  obtain ⟨hpm, hp0, -⟩ := elDensity_props hyp (μ : Measure (Torus d))
  have hμp : (μ : Measure (Torus d)) = densMeasure p := minimizer_eq_elDensity hyp hμ
  rw [hμp, densMeasure,
    integrable_withDensity_iff_integrable_smul' (f := fun x => ENNReal.ofReal (p x))
      (ENNReal.measurable_ofReal.comp hpm)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hu
  refine hu.congr (Eventually.of_forall fun y => ?_)
  show (ENNReal.ofReal (p y)).toReal • u y = p y * u y
  rw [smul_eq_mul, ENNReal.toReal_ofReal (show (0 : ℝ) ≤ p y from (hp0 y).le)]

omit hμ in
theorem integrable_bGrad_mul' {g : Torus d → ℝ} (hg : Integrable g (haar d)) (x : Torus d)
    (k : Fin d) : Integrable (fun y => bGrad W x y k * g y) (haar d) := by
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  refine Integrable.mono' (hg.abs.const_mul Cb)
    (((measurable_bGrad hyp k).comp measurable_prodMk_left).aestronglyMeasurable.mul
      hg.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hCb x y k) (abs_nonneg _)

omit hμ in
theorem bForceL_add {u v : Torus d → ℝ} (hu : Integrable u (haar d)) (hv : Integrable v (haar d))
    (a b : ℝ) (x : Torus d) (k : Fin d) :
    bForceL W (fun y => a * u y + b * v y) x k = a * bForceL W u x k + b * bForceL W v x k := by
  unfold bForceL
  have e : (fun y => bGrad W x y k * (a * u y + b * v y)) =
      fun y => a * (bGrad W x y k * u y) + b * (bGrad W x y k * v y) := by funext y; ring
  rw [e, integral_add ((integrable_bGrad_mul' hyp hu x k).const_mul a)
    ((integrable_bGrad_mul' hyp hv x k).const_mul b), integral_const_mul, integral_const_mul]

omit hμ in
theorem bForceL_finsetSum {u : Fin n → Torus d → ℝ} (hu : ∀ i, Integrable (u i) (haar d))
    (b : Fin n → ℝ) (x : Torus d) (k : Fin d) :
    bForceL W (fun y => ∑ i, b i * u i y) x k = ∑ i, b i * bForceL W (u i) x k := by
  unfold bForceL
  have e : (fun y => bGrad W x y k * ∑ i, b i * u i y) =
      fun y => ∑ i, b i * (bGrad W x y k * u i y) := by
    funext y; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, integral_finsetSum _ fun i _ => (integrable_bGrad_mul' hyp (hu i) x k).const_mul (b i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

omit hμ in
theorem convDens_finsetSum {u : Fin n → Torus d → ℝ} (hu : ∀ i, Integrable (u i) (haar d))
    (b : Fin n → ℝ) (x : Torus d) :
    convDens W (fun y => ∑ i, b i * u i y) x = ∑ i, b i * convDens W (u i) x := by
  unfold convDens
  have e : (fun y => W x y * ∑ i, b i * u i y) = fun y => ∑ i, b i * (W x y * u i y) := by
    funext y; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, integral_finsetSum _ fun i _ =>
    (integrable_W_mul hyp (haar d) (hu i) x).const_mul (b i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end diss

section bound
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)
include hyp hμ hφ

/-- The log-density on the zero set: `log(p(1+h)) = K₀ - V - W * (p(1 + h + ∑ bᵢ φᵢ))`. -/
theorem log_density_eq {h : CT d} (hpos : h ∈ posSet) {c : ℝ} {b : Fin n → ℝ}
    (hP : ∀ x, PhiC hyp (μ : Measure (Torus d)) h x = c + ∑ i, b i * phiC hyp hφ i x) :
    ∃ K₀ : ℝ, ∀ x, Real.log (elDens V W (μ : Measure (Torus d)) x * (1 + h x)) =
      K₀ - V x - convDens W (fun y => elDens V W (μ : Measure (Torus d)) y *
        (1 + h y + ∑ i, b i * φ i y)) x := by
  set μm := (μ : Measure (Torus d))
  set p := elDens V W μm with hp
  obtain ⟨hpm, hp0, hp1⟩ := elDensity_props hyp μm
  have hpi : Integrable p (haar d) := integrable_of_integral_eq_one' hp1
  have hphi : Integrable (fun y => p y * h y) (haar d) :=
    integrable_elDens_mul hyp hμ (integrable_of_continuous h.continuous)
  have hpφ : ∀ i, Integrable (fun y => p y * φ i y) (haar d) := fun i =>
    integrable_elDens_mul hyp hμ ((memL20_phi hyp hφ i).1.integrable one_le_two)
  obtain ⟨Kh, hKh⟩ := Top_eq_convDens hyp hμ (⇑h)
  choose Ki hKi using fun i => Top_eq_convDens hyp hμ (φ i)
  set Z := ∫ y, Real.exp (-V y - convMeas W μm y) ∂haar d with hZ
  have hZ0 : 0 < Z := by
    have := hp0 (Classical.arbitrary _)
    simp only [hp, elDens] at this
    exact (div_pos_iff.mp this).elim (fun h => h.2) fun h => absurd h.1 (not_lt.mpr (exp_pos _).le)
  have hlogp : ∀ x, Real.log (p x) = -V x - convDens W p x - Real.log Z := fun x => by
    have hc : convMeas W μm x = convDens W p x := by
      unfold convMeas
      rw [integral_minimizer hyp hμ]
      unfold convDens
      congr 1; funext y; ring
    simp only [hp, elDens]
    rw [Real.log_div (exp_pos _).ne' hZ0.ne', Real.log_exp, hc]
  refine ⟨-Real.log Z + c + ∑ i, b i * Ki i + Kh, fun x => ?_⟩
  have h1 : (0 : ℝ) < 1 + h x := hpos x
  rw [Real.log_mul (hp0 x).ne' h1.ne', hlogp x]
  have hlog1 : Real.log (1 + h x) = c + ∑ i, b i * phiC hyp hφ i x - Top W μm (⇑h) x := by
    have := hP x
    simp only [PhiC, ContinuousMap.add_apply, logC_apply hpos, TC_apply] at this
    linarith
  rw [hlog1, hKh x]
  have hphiC : ∀ i, phiC hyp hφ i x = -(convDens W (fun y => p y * φ i y) x - Ki i) := fun i => by
    show -Top W μm (φ i) x = _
    rw [hKi i x]
  simp_rw [hphiC]
  -- linearity of `convDens`
  have hg : convDens W (fun y => p y * (1 + h y + ∑ i, b i * φ i y)) x =
      convDens W p x + convDens W (fun y => p y * h y) x +
        ∑ i, b i * convDens W (fun y => p y * φ i y) x := by
    simp only [convDens]
    have iA := integrable_W_mul hyp (haar d) hpi x
    have iB := integrable_W_mul hyp (haar d) hphi x
    have iC : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Integrable (fun y => b i * (W x y * (p y * φ i y))) (haar d) := fun i _ =>
      (integrable_W_mul hyp (haar d) (hpφ i) x).const_mul (b i)
    have e : (fun y => W x y * (p y * (1 + h y + ∑ i, b i * φ i y))) =
        fun y => (W x y * p y + W x y * (p y * h y)) + ∑ i, b i * (W x y * (p y * φ i y)) := by
      funext y
      have e1 : W x y * (p y * (1 + h y + ∑ i, b i * φ i y)) =
          W x y * p y + W x y * (p y * h y) + W x y * (p y * ∑ i, b i * φ i y) := by ring
      rw [e1, Finset.mul_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have iAB : Integrable (fun y => W x y * p y + W x y * (p y * h y)) (haar d) := iA.add iB
    have iCs : Integrable (fun y => ∑ i, b i * (W x y * (p y * φ i y))) (haar d) :=
      integrable_finsetSum _ iC
    rw [e, integral_add iAB iCs, integral_add iA iB, integral_finsetSum _ iC]
    congr 1
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [hg]
  simp only [mul_neg, mul_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  ring

theorem abs_le_sqrt_sum_sq {b : Fin n → ℝ} (i : Fin n) : |b i| ≤ Real.sqrt (∑ j, b j ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => b j ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i))

/-- **(4.6)**: `D(p(1+h)) ≤ C_D |b|²` on the zero set. -/
theorem dissipation_graph_bound :
    ∃ CD : ℝ, 0 < CD ∧ ∀ (h : CT d), h ∈ posSet → ∫ x, h x ∂(μ : Measure (Torus d)) = 0 →
      ∀ (c : ℝ) (b : Fin n → ℝ),
        (∀ x, PhiC hyp (μ : Measure (Torus d)) h x = c + ∑ i, b i * phiC hyp hφ i x) →
        MemH1 (haar d) (fun x => Real.sqrt (elDens V W (μ : Measure (Torus d)) x * (1 + h x))) ∧
        dissipation V W (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + h x)) ≤
          ENNReal.ofReal (CD * ∑ i, b i ^ 2) := by
  set μm := (μ : Measure (Torus d))
  set p := elDens V W μm with hp
  obtain ⟨hpm, hp0, hp1⟩ := elDensity_props hyp μm
  have hpi : Integrable p (haar d) := integrable_of_integral_eq_one' hp1
  obtain ⟨cl, Cu, Lp, hcl, hbd⟩ := elDensity_bounds hyp
  obtain ⟨hpb, hpL⟩ := hbd μm inferInstance
  have hpc : Continuous p := hpL.continuous
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  set Cb := max Cb₀ 0
  have hCb : ∀ x y k, |bGrad W x y k| ≤ Cb := fun x y k => (hCb₀ x y k).trans (le_max_left _ _)
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  have hpφ : ∀ i, Integrable (fun y => p y * φ i y) (haar d) := fun i =>
    integrable_elDens_mul hyp hμ ((memL20_phi hyp hφ i).1.integrable one_le_two)
  -- bounds on the forces of the basis
  set B : Fin n → ℝ := fun i => Cb * ∫ y, |p y * φ i y| ∂haar d with hB
  have hbF : ∀ {u : Torus d → ℝ}, Integrable u (haar d) → ∀ x k,
      |bForceL W u x k| ≤ Cb * ∫ y, |u y| ∂haar d := fun {u} hu x k => by
    unfold bForceL
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (hu.abs.const_mul Cb) (Eventually.of_forall fun y => ?_)
    show |bGrad W x y k * u y| ≤ Cb * |u y|
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hCb x y k) (abs_nonneg _)
  have hB0 : ∀ i, 0 ≤ B i := fun i => mul_nonneg hCb0 (integral_nonneg fun _ => abs_nonneg _)
  set CD := (Fintype.card (Fin d) : ℝ) * (∑ i, B i) ^ 2 + 1 with hCD
  refine ⟨CD, by positivity, fun h hpos hh0 c b hP => ?_⟩
  -- the density `r = p (1 + h)`
  set r : Torus d → ℝ := fun x => p x * (1 + h x) with hr
  obtain ⟨mh, hmh, hmhx⟩ := exists_pos_lower hpos
  have hhx : ∀ x, |h x| ≤ ‖h‖ := fun x => abs_CT_le h x
  have hr0 : ∀ x, 0 < r x := fun x => mul_pos (hp0 x) (hpos x)
  have hrlo : ∀ x, cl * mh ≤ r x := fun x =>
    mul_le_mul (hpb x).1 (hmhx x) hmh.le (hp0 x).le
  have hrhi : ∀ x, r x ≤ Cu * (1 + ‖h‖) := fun x =>
    mul_le_mul (hpb x).2 (by linarith [le_abs_self (h x), hhx x]) (hpos x).le
      ((hp0 x).le.trans (hpb x).2)
  have hrc : Continuous r := hpc.mul (continuous_const.add h.continuous)
  have hri : Integrable r (haar d) := integrable_of_continuous hrc
  have hr1 : ∫ x, r x ∂haar d = 1 := by
    have e := integral_minimizer hyp hμ (fun x => 1 + h x)
    rw [show (∫ x, r x ∂haar d) = ∫ y, p y * (1 + h y) ∂haar d from rfl, ← e,
      integral_add (integrable_const _) (integrable_of_continuous h.continuous), hh0]
    simp
  -- the log-density
  obtain ⟨K₀, hK₀⟩ := log_density_eq hyp hμ hφ hpos hP
  set g : Torus d → ℝ := fun y => p y * (1 + h y + ∑ i, b i * φ i y) with hg
  have hgr : g = fun y => 1 * r y + 1 * ∑ i, b i * (p y * φ i y) := by
    funext y
    simp only [hg, hr, one_mul]
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsumi : Integrable (fun y => ∑ i, b i * (p y * φ i y)) (haar d) :=
    integrable_finsetSum _ fun i _ => (hpφ i).const_mul (b i)
  have hgi : Integrable g (haar d) := by
    rw [hgr]; exact (hri.const_mul 1).add (hsumi.const_mul 1)
  set F : Torus d → ℝ := fun x => K₀ - V x - convDens W g x with hF
  have hFeq : ∀ x, F x = Real.log (r x) := fun x => (hK₀ x).symm
  have hFc : Continuous F := by
    have : F = fun x => Real.log (r x) := funext hFeq
    rw [this]; exact hrc.log fun x => (hr0 x).ne'
  -- `|F| ≤ M`
  set M := |Real.log (cl * mh)| + |Real.log (Cu * (1 + ‖h‖))| with hM
  have hM0 : 0 ≤ M := by positivity
  have hFM : ∀ x, |F x| ≤ M := fun x => by
    rw [hFeq]
    have h1 := Real.log_le_log (by positivity) (hrlo x)
    have h2 := Real.log_le_log (hr0 x) (hrhi x)
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (cl * mh)), abs_nonneg (Real.log (Cu * (1 + ‖h‖)))]
    · linarith [le_abs_self (Real.log (Cu * (1 + ‖h‖))), abs_nonneg (Real.log (cl * mh))]
  -- weak gradients
  have hV := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp)
  have hCg := isWeakGrad_convDens' hyp hgi
  set GF : Torus d → Fin d → ℝ := fun x k => -lipGrad V x k - bForceL W g x k with hGF
  have hFw : IsWeakGrad F GF := by
    have := ((isWeakGrad_const K₀).add (hV.cmul (-1))).add (hCg.cmul (-1))
    convert this using 1
    · funext x; simp only [hF]; ring
    · funext x k; simp only [hGF, Pi.zero_apply]; ring
  set LV : ℝ := (Real.toNNReal (KV * Fintype.card (Fin d) / 2) : ℝ)
  set Bg : ℝ := Cb * ∫ y, |g y| ∂haar d
  have hGFb : ∀ x k, |GF x k| ≤ LV + Bg := fun x k => by
    simp only [hGF]
    refine (abs_sub _ _).trans (add_le_add ?_ (hbF hgi x k))
    rw [abs_neg]; exact abs_lipGrad_le (lipschitz_V hyp) x k
  have hGFm : ∀ k, Measurable fun x => GF x k := fun k =>
    ((measurable_lipGrad hyp.continuous_V k).neg).sub (measurable_bForceL' hyp hgi k)
  have hFi : Integrable F volume := integrable_of_continuous hFc
  have hGi : ∀ k, Integrable (fun x => GF x k) volume := fun k =>
    integrable_of_bdd (hGFm k) (C := LV + Bg) fun x => hGFb x k
  obtain ⟨Lc, hLc⟩ := deriv_expCut_bdd M hM0
  have hS0 := isWeakGrad_comp hFw hFi hGi ((contDiff_expCut M hM0).of_le (by simp)) hLc
  have hsqrt : ∀ x, Real.exp (F x / 2) = Real.sqrt (r x) := fun x => by
    rw [hFeq, ← Real.log_sqrt (hr0 x).le, Real.exp_log (Real.sqrt_pos.mpr (hr0 x))]
  have hS : IsWeakGrad (fun x => Real.sqrt (r x))
      (fun x k => Real.sqrt (r x) / 2 * GF x k) := by
    convert hS0 using 1
    · funext x; rw [expCut_eq hM0 (hFM x), hsqrt]
    · funext x k; rw [deriv_expCut hM0 (hFM x), hsqrt]
  have hVW : IsWeakGrad (fun x => V x + convDens W r x)
      (fun x k => lipGrad V x k + bForceL W r x k) := hV.add (isWeakGrad_convDens' hyp hri)
  -- bounds
  set Rs := Real.sqrt (Cu * (1 + ‖h‖))
  have hsqb : ∀ x, Real.sqrt (r x) ≤ Rs := fun x => Real.sqrt_le_sqrt (hrhi x)
  have hGSb : ∀ x k, |Real.sqrt (r x) / 2 * GF x k| ≤ Rs / 2 * (LV + Bg) := fun x k => by
    rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), abs_two]
    exact mul_le_mul (div_le_div_of_nonneg_right (hsqb x) (by norm_num)) (hGFb x k)
      (abs_nonneg _) (by positivity)
  have hGSm : ∀ k, Measurable fun x => Real.sqrt (r x) / 2 * GF x k := fun k =>
    ((hrc.measurable.sqrt).div_const 2).mul (hGFm k)
  have hH1 : MemH1 (haar d) (fun x => Real.sqrt (r x)) := by
    refine ⟨⟨_, hS⟩, ?_, ?_⟩
    · exact MemLp.of_bound hrc.sqrt.aestronglyMeasurable Rs (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]; exact hsqb x)
    · have hm : MemLp (fun x => Real.sqrt (sqNorm (fun k => Real.sqrt (r x) / 2 * GF x k))) 2
          (haar d) := by
        refine MemLp.of_bound ?_ (Real.sqrt (Fintype.card (Fin d) * (Rs / 2 * (LV + Bg)) ^ 2))
          (Eventually.of_forall fun x => ?_)
        · exact (Measurable.sqrt (Finset.measurable_sum _ fun k _ => (hGSm k).pow_const 2)
            ).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          refine Real.sqrt_le_sqrt ?_
          unfold sqNorm
          calc ∑ k, (Real.sqrt (r x) / 2 * GF x k) ^ 2 ≤ ∑ _k : Fin d, (Rs / 2 * (LV + Bg)) ^ 2 :=
                Finset.sum_le_sum fun k _ => by
                  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hGSb x k) 2
            _ = _ := by simp
      refine hm.ae_eq ?_
      filter_upwards [weakGrad_ae_eq hS] with x hx
      rw [hx]
  refine ⟨hH1, ?_⟩
  -- the dissipation
  set S := ∑ i, |b i| * B i with hS'
  have hdiff : ∀ x k, bForceL W g x k = bForceL W r x k +
      ∑ i, b i * bForceL W (fun y => p y * φ i y) x k := fun x k => by
    rw [hgr, bForceL_add hyp hri hsumi 1 1 x k, bForceL_finsetSum hyp hpφ b x k]
    ring
  have hpt : ∀ x, ∑ k, (2 * (Real.sqrt (r x) / 2 * GF x k) +
      Real.sqrt (r x) * (lipGrad V x k + bForceL W r x k)) ^ 2 ≤
        (Fintype.card (Fin d) : ℝ) * S ^ 2 * r x := fun x => by
    have e : ∀ k, 2 * (Real.sqrt (r x) / 2 * GF x k) +
        Real.sqrt (r x) * (lipGrad V x k + bForceL W r x k) =
        -(Real.sqrt (r x) * ∑ i, b i * bForceL W (fun y => p y * φ i y) x k) := fun k => by
      simp only [hGF, hdiff]; ring
    have hb : ∀ k, |∑ i, b i * bForceL W (fun y => p y * φ i y) x k| ≤ S := fun k => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := hbF (hpφ i) x k
      exact this
    have hrx := hr0 x
    calc ∑ k, (2 * (Real.sqrt (r x) / 2 * GF x k) +
          Real.sqrt (r x) * (lipGrad V x k + bForceL W r x k)) ^ 2
        ≤ ∑ _k : Fin d, S ^ 2 * r x := Finset.sum_le_sum fun k _ => by
          rw [e k, neg_sq, mul_pow, Real.sq_sqrt hrx.le, mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ hrx.le
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hb k) 2
      _ = (Fintype.card (Fin d) : ℝ) * S ^ 2 * r x := by simp; ring
  have hS2 : S ^ 2 ≤ (∑ i, B i) ^ 2 * ∑ i, b i ^ 2 := by
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hB0 i)
    have h1 : S ≤ Real.sqrt (∑ i, b i ^ 2) * ∑ i, B i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (abs_le_sqrt_sum_sq hyp hμ hφ i) (hB0 i)
    calc S ^ 2 ≤ (Real.sqrt (∑ i, b i ^ 2) * ∑ i, B i) ^ 2 := pow_le_pow_left₀ hS0 h1 2
      _ = (∑ i, B i) ^ 2 * ∑ i, b i ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]; ring
  unfold dissipation
  rw [if_pos ⟨hH1, ⟨_, hVW⟩⟩]
  calc ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (r y)) x k +
        Real.sqrt (r x) * weakGrad (fun y => V y + convDens W r y) x k) ^ 2) ∂haar d
      ≤ ∫⁻ x, ENNReal.ofReal ((Fintype.card (Fin d) : ℝ) * S ^ 2 * r x) ∂haar d := by
        refine lintegral_mono_ae ?_
        filter_upwards [weakGrad_ae_eq hS, weakGrad_ae_eq hVW] with x h1 h2
        rw [h1, h2]
        exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal ((Fintype.card (Fin d) : ℝ) * S ^ 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hri.const_mul _)
          (Eventually.of_forall fun x => mul_nonneg (by positivity) (hr0 x).le),
          integral_const_mul, hr1, mul_one]
    _ ≤ ENNReal.ofReal (CD * ∑ i, b i ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hb2 : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        rw [hCD]
        nlinarith [mul_le_mul_of_nonneg_left hS2 (Nat.cast_nonneg (Fintype.card (Fin d)) :
          (0 : ℝ) ≤ Fintype.card (Fin d))]

end bound

end SharpLSI
