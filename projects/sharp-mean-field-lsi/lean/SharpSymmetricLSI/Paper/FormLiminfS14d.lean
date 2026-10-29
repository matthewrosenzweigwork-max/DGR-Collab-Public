import SharpSymmetricLSI.Paper.FormLiminfS14c
import SharpSymmetricLSI.Paper.FormLiminfS13a

/-!
# R33 cross term (S14d): the error of the main part, for fixed `N`

`cross_err_le`: `|∫ f genL - ∫ f H_R(Z)| ≤ E_mob + E_force + E_mob'`, where `Z = fluct`, `H_R =
crossH` and the three errors are the mobility error of the diagonal part, the force error and the
mobility error of the finite-rank part of `genL_split`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem crossH2_congr (lam : ℕ → ℝ) (c : Cyl) (s : Finset ℕ) (a : ℕ → ℕ → ℝ) (w : Fin c.J → ℝ)
    {zq zq' : ℕ → ℝ} (h : ∀ q ∈ s, zq q = zq' q) :
    crossH2 lam c s a w zq = crossH2 lam c s a w zq' := by
  unfold crossH2
  refine Finset.sum_congr rfl fun i _ => congrArg _ (Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun q hq => by rw [h q hq])

theorem ite_lam_eq (lam : ℕ → ℝ) (i j : ℕ) :
    (if j = i then lam (i + 1) else 0) = (if j = i then lam (j + 1) else 0) := by
  split_ifs with h
  · rw [h]
  · rfl

section fixedN
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j) (N : ℕ) (c : Cyl)
  (s : Finset ℕ) (a : ℕ → ℕ → ℝ) {J' : ℕ} (hJ : c.J ≤ J') (hsJ : ∀ q ∈ s, q < J')
include hyp hμ hφ heC hsJ

omit hφ heC hsJ in
theorem gibbs_ac_pi_min : gibbs V W N ≪ Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  rw [gibbs_eq_centered_aux hyp hμ N]; exact withDensity_absolutelyContinuous _ _

/-- A.e., the test function in `Z = fluct` is the main part in `zC`. -/
theorem crossH_fluct_ae :
    ∀ᵐ X ∂gibbs V W N, crossH lam c s a hJ (fun n : Fin J' => fluct e N n X) =
      crossH1 lam c (zC eC N c.J X) +
        crossH2 lam c s a (zC eC N c.J X) (fun q => (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) := by
  have hac := minimizer_ac hyp hμ
  have h1 := zC_ae_eq_fluct hac heC N J'
  filter_upwards [(gibbs_ac_pi_min hyp hμ N).ae_le h1] with X hX
  have hp : projJ hJ (fun n : Fin J' => fluct e N n X) = zC eC N c.J X := by
    funext i
    have := congrFun hX (Fin.castLE hJ i)
    simp only [projJ]
    rw [← this]; rfl
  unfold crossH
  rw [hp]
  congr 1
  refine crossH2_congr lam c s a _ fun q hq => ?_
  have := congrFun hX ⟨q, hsJ q hq⟩
  rw [extN, dif_pos (hsJ q hq), ← this]; rfl

/-- **The error of the main part.** -/
theorem cross_err_le {f : Config N d → ℝ} (hfL : MemLp f 2 (gibbs V W N)) :
    |∫ X, f X * genL W (μ : Measure (Torus d)) eC lam N c X ∂gibbs V W N -
        ∫ X, f X * crossH lam c s a hJ (fun n : Fin J' => fluct e N n X) ∂gibbs V W N| ≤
      (∑ i : Fin c.J, ∑ j : Fin c.J, ∫ X, |f X * fderiv ℝ (cylD c i) (zC eC N c.J X) (Pi.single j 1) *
          (mobA eC N X j i - if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0)| ∂gibbs V W N) +
      (∑ i : Fin c.J, ∫ X, |f X * cylD c i (zC eC N c.J X) *
          (forceD W (μ : Measure (Torus d)) eC N i X - ∑ p ∈ s, ∑ q ∈ s, a p q *
            ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) * mobA eC N X p i)| ∂gibbs V W N) +
      (∑ i : Fin c.J, ∑ p ∈ s, ∑ q ∈ s, |a p q| * ∫ X, |f X * (cylD c i (zC eC N c.J X) *
          ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l))) *
          (mobA eC N X p i - if p = (i : ℕ) then lam (p + 1) else 0)| ∂gibbs V W N) := by
  have := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N
  set z : Config N d → Fin c.J → ℝ := fun X => zC eC N c.J X
  set Zq : ℕ → Config N d → ℝ := fun q X => (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)
  -- bounded measurable building blocks
  have bψ : ∀ i : Fin c.J, BddMeas fun X => cylD c i (z X) := fun i =>
    bddMeas_comp_zC hφ N (contDiff_cylD c i).continuous (hasCompactSupport_cylD c i)
  have bdψ : ∀ i j : Fin c.J, BddMeas fun X => fderiv ℝ (cylD c i) (z X) (Pi.single j 1) :=
    fun i j => bddMeas_comp_zC hφ N
      (((contDiff_cylD c i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hasCompactSupport_cylD c i).fderiv_apply (𝕜 := ℝ) _)
  have bZ : ∀ q, BddMeas (Zq q) := fun q => bddMeas_eCsum hφ N q
  have bA : ∀ i j, BddMeas fun X => mobA eC N X i j := fun i j => bddMeas_mobA hφ N i j
  have bD : ∀ i, BddMeas fun X => forceD W (μ : Measure (Torus d)) eC N i X := fun i =>
    bddMeas_forceD hφ N hyp hμ i
  -- the three error terms
  set e3 : Config N d → ℝ := fun X => ∑ i : Fin c.J, ∑ j : Fin c.J,
    fderiv ℝ (cylD c i) (z X) (Pi.single j 1) *
      (mobA eC N X j i - if (j : ℕ) = i then lam ((i : ℕ) + 1) else 0)
  set e4 : Config N d → ℝ := fun X => ∑ i : Fin c.J, cylD c i (z X) *
    (forceD W (μ : Measure (Torus d)) eC N i X - ∑ p ∈ s, ∑ q ∈ s, a p q * Zq q X * mobA eC N X p i)
  set e5 : Config N d → ℝ := fun X => ∑ i : Fin c.J, cylD c i (z X) * ∑ p ∈ s, ∑ q ∈ s,
    a p q * Zq q X * (mobA eC N X p i - if p = (i : ℕ) then lam ((i : ℕ) + 1) else 0)
  have b3 : BddMeas e3 := BddMeas.sum _ fun i _ => BddMeas.sum _ fun j _ =>
    (bdψ i j).mul ((bA _ _).sub (BddMeas.const _))
  have b4 : BddMeas e4 := BddMeas.sum _ fun i _ => (bψ i).mul ((bD _).sub
    (BddMeas.sum _ fun p _ => BddMeas.sum _ fun q _ => ((BddMeas.const _).mul (bZ q)).mul (bA _ _)))
  have b5 : BddMeas e5 := BddMeas.sum _ fun i _ => (bψ i).mul (BddMeas.sum _ fun p _ =>
    BddMeas.sum _ fun q _ => ((BddMeas.const _).mul (bZ q)).mul ((bA _ _).sub (BddMeas.const _)))
  set m : Config N d → ℝ := fun X => crossH1 lam c (z X) + crossH2 lam c s a (z X) (fun q => Zq q X)
  have bm : BddMeas m := by
    refine (BddMeas.sum (Finset.univ : Finset (Fin c.J)) fun i _ =>
      (BddMeas.const _).mul (((bZ (i : ℕ)).mul (bψ i)).sub (bdψ i i))).add
      (BddMeas.sum (Finset.univ : Finset (Fin c.J)) fun i _ => (bψ i).mul (BddMeas.sum _ fun p _ => BddMeas.sum _ fun q _ =>
        ((BddMeas.const _).mul (bZ q)).mul (BddMeas.const _)))
  -- `genL = m - e3 + e4 + e5`
  have hgen : ∀ X, genL W (μ : Measure (Torus d)) eC lam N c X = m X - e3 X + e4 X + e5 X := by
    intro X
    rw [genL_split W (μ : Measure (Torus d)) eC lam N c s a X]
    simp only [m, e3, e4, e5, crossH1, crossH2, lamShift, Zq, z]
  have hae := crossH_fluct_ae (lam := lam) hyp hμ hφ heC N c s a hJ hsJ
  have i1 : Integrable (fun X => f X * genL W (μ : Measure (Torus d)) eC lam N c X) P := by
    have : BddMeas fun X => genL W (μ : Measure (Torus d)) eC lam N c X := by
      have := ((bm.sub b3).add b4).add b5
      have heq : (fun X => genL W (μ : Measure (Torus d)) eC lam N c X) =
          fun X => m X - e3 X + e4 X + e5 X := funext hgen
      rw [heq]; exact this
    exact integrable_mul_of_bddMeas hfL this
  have i2 : Integrable (fun X => f X * crossH lam c s a hJ (fun n : Fin J' => fluct e N n X)) P :=
    (integrable_mul_of_bddMeas hfL bm).congr (hae.mono fun X hX => by simp only [hX, m, z, Zq])
  have i3 := integrable_mul_of_bddMeas hfL b3
  have i4 := integrable_mul_of_bddMeas hfL b4
  have i5 := integrable_mul_of_bddMeas hfL b5
  have hdiff : ∫ X, f X * genL W (μ : Measure (Torus d)) eC lam N c X ∂P -
      ∫ X, f X * crossH lam c s a hJ (fun n : Fin J' => fluct e N n X) ∂P =
      ∫ X, (-(f X * e3 X) + f X * e4 X + f X * e5 X) ∂P := by
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (hae.mono fun X hX => ?_)
    simp only [hX, hgen]
    simp only [m, z, Zq]
    ring
  rw [hdiff]
  refine (abs_integral_le_integral_abs).trans ?_
  have hpt : ∀ X, |-(f X * e3 X) + f X * e4 X + f X * e5 X| ≤
      |f X * e3 X| + |f X * e4 X| + |f X * e5 X| := fun X => by
    calc _ ≤ |-(f X * e3 X) + f X * e4 X| + |f X * e5 X| := abs_add_le _ _
      _ ≤ |-(f X * e3 X)| + |f X * e4 X| + |f X * e5 X| := by gcongr; exact abs_add_le _ _
      _ = _ := by rw [abs_neg]
  refine (integral_mono ((i3.neg.add i4).add i5).abs ((i3.abs.add i4.abs).add i5.abs) hpt).trans ?_
  simp only [Pi.add_apply]
  rw [integral_add (f := fun X => |f X * e3 X| + |f X * e4 X|) (g := fun X => |f X * e5 X|)
      (i3.abs.add i4.abs) i5.abs,
    integral_add (f := fun X => |f X * e3 X|) (g := fun X => |f X * e4 X|) i3.abs i4.abs]
  -- each error term
  have hb3 : ∫ X, |f X * e3 X| ∂P ≤ ∑ i : Fin c.J, ∑ j : Fin c.J, ∫ X, |f X *
      fderiv ℝ (cylD c i) (z X) (Pi.single j 1) *
        (mobA eC N X j i - if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0)| ∂P := by
    have hint : ∀ i j : Fin c.J, Integrable (fun X => |f X *
        fderiv ℝ (cylD c i) (z X) (Pi.single j 1) *
          (mobA eC N X j i - if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0)|) P := fun i j => by
      have := integrable_mul_of_bddMeas hfL ((bdψ i j).mul ((bA (j : ℕ) i).sub
        (BddMeas.const (if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0))))
      exact (this.congr (Eventually.of_forall fun X => by simp only [mul_assoc])).abs
    calc ∫ X, |f X * e3 X| ∂P ≤ ∫ X, ∑ i : Fin c.J, ∑ j : Fin c.J, |f X *
          fderiv ℝ (cylD c i) (z X) (Pi.single j 1) *
            (mobA eC N X j i - if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0)| ∂P := by
          refine integral_mono i3.abs (integrable_finset_sum _ fun i _ =>
            integrable_finset_sum _ fun j _ => hint i j) fun X => ?_
          simp only [e3, Finset.mul_sum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => le_of_eq ?_))
          rw [ite_lam_eq lam (i : ℕ) (j : ℕ), mul_assoc]
      _ = _ := by
          rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
          exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ fun j _ => hint i j
  have hb4 : ∫ X, |f X * e4 X| ∂P ≤ ∑ i : Fin c.J, ∫ X, |f X * cylD c i (z X) *
      (forceD W (μ : Measure (Torus d)) eC N i X - ∑ p ∈ s, ∑ q ∈ s, a p q *
        Zq q X * mobA eC N X p i)| ∂P := by
    have hint : ∀ i : Fin c.J, Integrable (fun X => |f X * cylD c i (z X) *
        (forceD W (μ : Measure (Torus d)) eC N i X - ∑ p ∈ s, ∑ q ∈ s, a p q *
          Zq q X * mobA eC N X p i)|) P := fun i => by
      have := integrable_mul_of_bddMeas hfL ((bψ i).mul ((bD (i : ℕ)).sub
        (BddMeas.sum s fun p _ => BddMeas.sum s fun q _ =>
          ((BddMeas.const (a p q)).mul (bZ q)).mul (bA p i))))
      exact (this.congr (Eventually.of_forall fun X => by simp only [mul_assoc])).abs
    rw [← integral_finset_sum _ fun i _ => hint i]
    refine integral_mono i4.abs (integrable_finset_sum _ fun i _ => hint i) fun X => ?_
    simp only [e4, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
    rw [mul_assoc]
  have hb5 : ∫ X, |f X * e5 X| ∂P ≤ ∑ i : Fin c.J, ∑ p ∈ s, ∑ q ∈ s, |a p q| * ∫ X,
      |f X * (cylD c i (z X) * Zq q X) *
        (mobA eC N X p i - if p = (i : ℕ) then lam (p + 1) else 0)| ∂P := by
    have hint : ∀ (i : Fin c.J) (p q : ℕ), Integrable (fun X => |a p q| * |f X *
        (cylD c i (z X) * Zq q X) *
        (mobA eC N X p i - if p = (i : ℕ) then lam (p + 1) else 0)|) P := fun i p q => by
      have := integrable_mul_of_bddMeas hfL (((bψ i).mul (bZ q)).mul ((bA p i).sub
        (BddMeas.const (if p = (i : ℕ) then lam (p + 1) else 0))))
      exact ((this.congr (Eventually.of_forall fun X => by simp only [mul_assoc])).abs).const_mul _
    calc ∫ X, |f X * e5 X| ∂P ≤ ∫ X, ∑ i : Fin c.J, ∑ p ∈ s, ∑ q ∈ s, |a p q| * |f X *
          (cylD c i (z X) * Zq q X) *
          (mobA eC N X p i - if p = (i : ℕ) then lam (p + 1) else 0)| ∂P := by
          refine integral_mono i5.abs (integrable_finset_sum _ fun i _ => integrable_finset_sum _
            fun p _ => integrable_finset_sum _ fun q _ => hint i p q) fun X => ?_
          simp only [e5, Finset.mul_sum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ =>
              (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => le_of_eq ?_)))
          rw [ite_lam_eq lam (i : ℕ) p, ← abs_mul]
          congr 1
          ring
      _ = _ := by
          rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun p _ =>
            integrable_finset_sum _ fun q _ => hint i p q]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finset_sum _ fun p _ => integrable_finset_sum _ fun q _ => hint i p q]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [integral_finset_sum _ fun q _ => hint i p q]
          exact Finset.sum_congr rfl fun q _ => integral_const_mul _ _
  linarith

end fixedN

end SharpLSI
