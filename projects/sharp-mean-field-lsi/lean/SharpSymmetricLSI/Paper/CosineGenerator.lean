import SharpSymmetricLSI.Paper.CosineCalculus
import SharpSymmetricLSI.Paper.R37Particle
import SharpSymmetricLSI.Paper.CosineHyp

/-!
# The generator `L_N` of the cosine model: (3.33) (Phase 3, lane C)

Weighted integration by parts on `𝕋^ι` for periodic smooth lifts (`ibp_weighted`), and its
transfer to `P_{N,κ}` (`cosine_generator_ibp_aux`), using `H_N = U_N - κN/2`.
-/

open MeasureTheory Set Filter
open scoped Real ContDiff

namespace SharpLSI

section Periodic

variable {ι : Type*} [Fintype ι]

/-- `Φ` is `ℤ^ι`-periodic. -/
def IsPer {E : Type*} (Φ : (ι → ℝ) → E) : Prop := ∀ (m : ι → ℤ) x, Φ (x + intVec m) = Φ x

theorem IsPer.fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : (ι → ℝ) → E}
    (hp : IsPer Φ) : IsPer (fderiv ℝ Φ) := fun m x => by
  rw [← fderiv_comp_add_right (𝕜 := ℝ) (f := Φ) (x := x) (intVec m)]
  congr 1; funext z; exact hp m z

omit [Fintype ι] in
theorem IsPer.secT_liftT {E : Type*} {Φ : (ι → ℝ) → E} (hp : IsPer Φ) (x : ι → ℝ) :
    Φ (secT (liftT x)) = Φ x := by
  obtain ⟨m, hm⟩ := secT_liftT_eq x; rw [hm, hp]

omit [Fintype ι] in
theorem IsPer.eq_of_liftT_eq {E : Type*} {Φ : (ι → ℝ) → E} (hp : IsPer Φ) {a b : ι → ℝ}
    (h : liftT a = liftT b) : Φ a = Φ b := by
  rw [← hp.secT_liftT a, h, hp.secT_liftT b]

omit [Fintype ι] in
theorem isPer_lift {E : Type*} (f : UnitAddTorus ι → E) : IsPer (f ∘ liftT) := fun m x => by
  simp only [Function.comp_apply, liftT_add_intVec]

/-- `∂_k Φ`. -/
noncomputable def Dk [DecidableEq ι] (Φ : (ι → ℝ) → ℝ) (k : ι) (x : ι → ℝ) : ℝ :=
  fderiv ℝ Φ x (Pi.single k 1)

theorem IsPer.Dk [DecidableEq ι] {Φ : (ι → ℝ) → ℝ} (hp : IsPer Φ) (k : ι) : IsPer (Dk Φ k) :=
  fun m x => by simp only [SharpLSI.Dk, hp.fderiv m x]

theorem contDiff_Dk [DecidableEq ι] {Φ : (ι → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (k : ι) :
    ContDiff ℝ ∞ (Dk Φ k) :=
  (hΦ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem integrable_secT {Φ : (ι → ℝ) → ℝ} (hc : Continuous Φ) (hp : IsPer Φ) :
    Integrable (fun y => Φ (secT y)) volume := by
  obtain ⟨C, hC⟩ := periodic_bounded hc hp
  exact Integrable.of_bound (hc.comp_aestronglyMeasurable measurable_secT.aestronglyMeasurable) C
    (Eventually.of_forall fun y => hC _)

/-- Weighted integration by parts in direction `k`:
`∫ e^{-h}(∂_k²g - ∂_kh ∂_kg) w = -∫ e^{-h} ∂_kg ∂_kw`. -/
theorem ibp_weighted [DecidableEq ι] {g w h : (ι → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h) (pg : IsPer g) (pw : IsPer w) (ph : IsPer h)
    (k : ι) :
    ∫ y, Real.exp (-h (secT y)) *
        ((Dk (Dk g k) k (secT y) - Dk h k (secT y) * Dk g k (secT y)) * w (secT y)) =
      -∫ y, Real.exp (-h (secT y)) * (Dk g k (secT y) * Dk w k (secT y)) := by
  have hDg := contDiff_Dk hg k
  have hE : ContDiff ℝ ∞ (fun x => Real.exp (-h x)) := Real.contDiff_exp.comp hh.neg
  set Ψ : (ι → ℝ) → ℝ := fun x => Real.exp (-h x) * (Dk g k x * w x) with hΨdef
  have hΨ : ContDiff ℝ ∞ Ψ := hE.mul (hDg.mul hw)
  have pΨ : IsPer Ψ := fun m x => by simp only [hΨdef, ph m x, (pg.Dk k) m x, pw m x]
  set T : UnitAddTorus ι → ℝ := fun y => Ψ (secT y)
  have hT : T ∘ liftT = Ψ := funext pΨ.secT_liftT
  have h0 := integral_fderiv_torus_eq_zero (W := T) (by rw [hT]; exact hΨ.of_le (by simp))
    (Pi.single k 1)
  rw [hT] at h0
  have d1 : ∀ x, DifferentiableAt ℝ (fun x => Real.exp (-h x)) x := fun x =>
    (hE.differentiable (by simp)) x
  have d2 : ∀ x, DifferentiableAt ℝ (Dk g k) x := fun x => (hDg.differentiable (by simp)) x
  have d3 : ∀ x, DifferentiableAt ℝ w x := fun x => (hw.differentiable (by simp)) x
  have d4 : ∀ x, DifferentiableAt ℝ h x := fun x => (hh.differentiable (by simp)) x
  have hd : ∀ x, fderiv ℝ Ψ x (Pi.single k 1) =
      Real.exp (-h x) * (-Dk h k x) * (Dk g k x * w x) +
        Real.exp (-h x) * (Dk (Dk g k) k x * w x + Dk g k x * Dk w k x) := by
    intro x
    rw [hΨdef, fderiv_fun_mul (d1 x)
      (by exact (d2 x).mul (d3 x) : DifferentiableAt ℝ (fun y => Dk g k y * w y) x),
      fderiv_fun_mul (d2 x) (d3 x),
      fderiv_exp (by exact (d4 x).neg : DifferentiableAt ℝ (fun y => -h y) x), fderiv_fun_neg]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.neg_apply, SharpLSI.Dk]
    ring
  simp_rw [hd] at h0
  have i1 := integrable_secT (Φ := fun x => Real.exp (-h x) * (-Dk h k x) * (Dk g k x * w x))
    (hE.continuous.mul (contDiff_Dk hh k).continuous.neg |>.mul
      (hDg.continuous.mul hw.continuous))
    (fun m x => by simp only [ph m x, (ph.Dk k) m x, (pg.Dk k) m x, pw m x])
  have i2 := integrable_secT (Φ := fun x => Real.exp (-h x) * (Dk (Dk g k) k x * w x))
    (hE.continuous.mul ((contDiff_Dk hDg k).continuous.mul hw.continuous))
    (fun m x => by simp only [ph m x, ((pg.Dk k).Dk k) m x, pw m x])
  have i3 := integrable_secT (Φ := fun x => Real.exp (-h x) * (Dk g k x * Dk w k x))
    (hE.continuous.mul (hDg.continuous.mul (contDiff_Dk hw k).continuous))
    (fun m x => by simp only [ph m x, (pg.Dk k) m x, (pw.Dk k) m x])
  have e : ∀ y, Real.exp (-h (secT y)) * (-Dk h k (secT y)) * (Dk g k (secT y) * w (secT y)) +
      Real.exp (-h (secT y)) * (Dk (Dk g k) k (secT y) * w (secT y) +
        Dk g k (secT y) * Dk w k (secT y)) =
      (Real.exp (-h (secT y)) * (-Dk h k (secT y)) * (Dk g k (secT y) * w (secT y)) +
        Real.exp (-h (secT y)) * (Dk (Dk g k) k (secT y) * w (secT y))) +
        Real.exp (-h (secT y)) * (Dk g k (secT y) * Dk w k (secT y)) := fun y => by ring
  simp_rw [e] at h0
  have s1 : ∫ y, ((Real.exp (-h (secT y)) * (-Dk h k (secT y)) * (Dk g k (secT y) * w (secT y)) +
        Real.exp (-h (secT y)) * (Dk (Dk g k) k (secT y) * w (secT y))) +
        Real.exp (-h (secT y)) * (Dk g k (secT y) * Dk w k (secT y))) =
      (∫ y, (Real.exp (-h (secT y)) * (-Dk h k (secT y)) * (Dk g k (secT y) * w (secT y)) +
        Real.exp (-h (secT y)) * (Dk (Dk g k) k (secT y) * w (secT y)))) +
        ∫ y, Real.exp (-h (secT y)) * (Dk g k (secT y) * Dk w k (secT y)) :=
    integral_add (i1.add i2) i3
  have s2 : ∫ y, (Real.exp (-h (secT y)) * (-Dk h k (secT y)) * (Dk g k (secT y) * w (secT y)) +
      Real.exp (-h (secT y)) * (Dk (Dk g k) k (secT y) * w (secT y))) =
      (∫ y, Real.exp (-h (secT y)) * (-Dk h k (secT y)) * (Dk g k (secT y) * w (secT y))) +
      ∫ y, Real.exp (-h (secT y)) * (Dk (Dk g k) k (secT y) * w (secT y)) := integral_add i1 i2
  rw [s1, s2] at h0
  have e2 : ∫ y, Real.exp (-h (secT y)) *
      ((Dk (Dk g k) k (secT y) - Dk h k (secT y) * Dk g k (secT y)) * w (secT y)) =
      (∫ y, Real.exp (-h (secT y)) * (-Dk h k (secT y)) * (Dk g k (secT y) * w (secT y))) +
        ∫ y, Real.exp (-h (secT y)) * (Dk (Dk g k) k (secT y) * w (secT y)) := by
    rw [← s2]
    congr 1; funext y; ring
  rw [e2]
  linarith

end Periodic

/-! ### Transfer to `P_{N,κ}` -/

section Cosine

variable {N : ℕ}

/-- `H_N = U_N - κN/2` for the cosine model. -/
theorem hamiltonian_cos (κ : ℝ) (X : Config N 1) :
    hamiltonian cosV (cosW κ) N X = cosU κ N X - κ * N / 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [hamiltonian, cosU]
  unfold hamiltonian cosV cosW
  simp_rw [gCos_X]
  rw [cosU_X]
  set x := repTorus (flat X)
  have hi : ∀ i : Fin N, ∑ j : Fin N, κ * (Real.cos (thetaC x i) * Real.cos (thetaC x j) +
      Real.sin (thetaC x i) * Real.sin (thetaC x j) - 1) =
      κ * (Real.cos (thetaC x i) * sumCos x + Real.sin (thetaC x i) * sumSin x - N) := by
    intro i
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    simp only [sumCos, sumSin]
    ring
  simp_rw [hi]
  have hs : ∑ i : Fin N, κ * (Real.cos (thetaC x i) * sumCos x +
      Real.sin (thetaC x i) * sumSin x - N) = κ * (sumCos x ^ 2 + sumSin x ^ 2 - N ^ 2) := by
    simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul,
      ← Finset.mul_sum]
    simp only [sumCos, sumSin, ← Finset.mul_sum]
    ring
  rw [hs]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Finset.sum_const_zero, zero_add]
  field_simp
  try ring

theorem cosU_unflat (κ : ℝ) (y : UnitAddTorus (Fin N × Fin 1)) :
    cosU κ N (unflat y) = UL κ N (secT y) := by
  conv_lhs => rw [← liftT_secT y]
  exact cosU_lift κ _

theorem measurePreserving_flat :
    MeasurePreserving (flat : Config N 1 → UnitAddTorus (Fin N × Fin 1)) volume volume :=
  ⟨measurable_flat, map_flat_volume N⟩

/-- `∫ F dP_{N,κ} = (e^{κN/2}/Z_N) ∫_{𝕋^{N×1}} F e^{-U_N}`. -/
theorem integral_gibbs_cos (κ : ℝ) (F : Config N 1 → ℝ) :
    ∫ X, F X ∂gibbs cosV (cosW κ) N =
      Real.exp (κ * N / 2) / partitionFn cosV (cosW κ) N *
        ∫ y, F (unflat y) * Real.exp (-UL κ N (secT y)) := by
  have hH := continuous_hamiltonian (cosine_hyp_all κ) N
  have hm := measurable_gibbsDensity (volume : Measure (Config N 1)) hH
  rw [show gibbs cosV (cosW κ) N = (volume : Measure (Config N 1)).withDensity
      (gibbsDensity volume (hamiltonian cosV (cosW κ) N)) from rfl,
    integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have e1 : ∀ X : Config N 1, (gibbsDensity volume (hamiltonian cosV (cosW κ) N) X).toReal • F X =
      Real.exp (κ * N / 2) / partitionFn cosV (cosW κ) N * (F X * Real.exp (-cosU κ N X)) := by
    intro X
    have hZ := partition_pos_of_continuous (volume : Measure (Config N 1)) hH
    simp only [gibbsDensity, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le), hamiltonian_cos,
      show -(cosU κ N X - κ * N / 2) = κ * N / 2 + -cosU κ N X by ring, Real.exp_add]
    unfold partitionFn
    ring
  simp_rw [e1]
  rw [integral_const_mul]
  congr 1
  have := (measurePreserving_flat (N := N)).integral_comp measurableEmbedding_flat
    (fun y => F (unflat y) * Real.exp (-cosU κ N (unflat y)))
  rw [show (∫ y, F (unflat y) * Real.exp (-UL κ N (secT y))) =
      ∫ y, F (unflat y) * Real.exp (-cosU κ N (unflat y)) by simp only [cosU_unflat]]
  exact this

theorem cpartialC_unflat (f : Config N 1 → ℝ) (i : Fin N) (k : Fin 1)
    (y : UnitAddTorus (Fin N × Fin 1)) :
    cpartialC f i k (unflat y) = Dk ((f ∘ unflat) ∘ liftT) (i, k) (secT y) := by
  unfold cpartialC cpartial Dk
  rw [(isPer_lift (f ∘ unflat)).fderiv.eq_of_liftT_eq
    (show liftT (repTorus (flat (unflat y))) = liftT (secT y) by
      rw [liftT_repTorus, liftT_secT]; rfl)]

theorem cpartial2C_unflat (f : Config N 1 → ℝ) (i : Fin N) (k : Fin 1) (j : Fin N) (l : Fin 1)
    (y : UnitAddTorus (Fin N × Fin 1)) :
    cpartial2C f i k j l (unflat y) = Dk (Dk ((f ∘ unflat) ∘ liftT) (i, k)) (j, l) (secT y) := by
  have h := ((isPer_lift (f ∘ unflat)).Dk (i, k)).fderiv.eq_of_liftT_eq
    (show liftT (repTorus (flat (unflat y))) = liftT (secT y) by
      rw [liftT_repTorus, liftT_secT]; rfl)
  exact congrArg (fun L => L (Pi.single (j, l) 1)) h

theorem lift_secT_apply (f : Config N 1 → ℝ) (y : UnitAddTorus (Fin N × Fin 1)) :
    ((f ∘ unflat) ∘ liftT) (secT y) = f (unflat y) := by
  simp [liftT_secT]

theorem UL_eq_lift (κ : ℝ) : UL κ N = (cosU κ N ∘ unflat) ∘ liftT := by
  rw [cosU_comp_lift]; rfl

/-- (3.33). -/
theorem cosine_generator_ibp_aux (κ : ℝ) {g w : Config N 1 → ℝ} (hg : IsSmoothC g)
    (hw : IsSmoothC w) :
    ∫ X, cosGen κ N g X * w X ∂gibbs cosV (cosW κ) N =
      -∫ X, gradDotC g w X ∂gibbs cosV (cosW κ) N := by
  rw [integral_gibbs_cos, integral_gibbs_cos, ← mul_neg]
  congr 1
  set Φg := (g ∘ unflat) ∘ liftT
  set Φw := (w ∘ unflat) ∘ liftT
  have hU : ContDiff ℝ ∞ (UL κ N) := (contDiff_UL κ).of_le le_top
  have pU : IsPer (UL κ N) := by rw [UL_eq_lift]; exact isPer_lift _
  have hgp : IsPer Φg := isPer_lift _
  have hwp : IsPer Φw := isPer_lift _
  have hL : ∀ y, cosGen κ N g (unflat y) * w (unflat y) * Real.exp (-UL κ N (secT y)) =
      ∑ p : Fin N × Fin 1, Real.exp (-UL κ N (secT y)) *
        ((Dk (Dk Φg p) p (secT y) - Dk (UL κ N) p (secT y) * Dk Φg p (secT y)) * Φw (secT y)) := by
    intro y
    simp only [cosGen, laplacianC, gradDotC, cpartialC_unflat, cpartial2C_unflat, ← UL_eq_lift]
    rw [show w (unflat y) = Φw (secT y) from (lift_secT_apply w y).symm, Fintype.sum_prod_type]
    simp only [← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hR : ∀ y, gradDotC g w (unflat y) * Real.exp (-UL κ N (secT y)) =
      ∑ p : Fin N × Fin 1, Real.exp (-UL κ N (secT y)) * (Dk Φg p (secT y) * Dk Φw p (secT y)) := by
    intro y
    simp only [gradDotC, cpartialC_unflat]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hgc : ContDiff ℝ ∞ Φg := hg
  have hwc : ContDiff ℝ ∞ Φw := hw
  have hE : Continuous fun x => Real.exp (-UL κ N x) := (Real.continuous_exp.comp hU.continuous.neg)
  simp_rw [hL, hR]
  rw [integral_finset_sum _ (fun p _ => integrable_secT (Φ := fun x => Real.exp (-UL κ N x) *
      ((Dk (Dk Φg p) p x - Dk (UL κ N) p x * Dk Φg p x) * Φw x))
      (hE.mul (((contDiff_Dk (contDiff_Dk hgc p) p).continuous.sub
        ((contDiff_Dk hU p).continuous.mul (contDiff_Dk hgc p).continuous)).mul hwc.continuous))
      (fun m x => by simp only [pU m x, ((hgp.Dk p).Dk p) m x, (pU.Dk p) m x, (hgp.Dk p) m x,
        hwp m x])),
    integral_finset_sum _ (fun p _ => integrable_secT (Φ := fun x => Real.exp (-UL κ N x) *
      (Dk Φg p x * Dk Φw p x))
      (hE.mul ((contDiff_Dk hgc p).continuous.mul (contDiff_Dk hwc p).continuous))
      (fun m x => by simp only [pU m x, (hgp.Dk p) m x, (hwp.Dk p) m x])),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => ibp_weighted hgc hwc hU hgp hwp pU p

end Cosine

end SharpLSI
