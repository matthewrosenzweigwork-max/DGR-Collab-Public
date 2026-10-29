import SharpSymmetricLSI.Paper.Centering

/-!
# (5.9), (5.10): the centered partition function and the exact entropy identity
(Phase 3, lane D; R19)
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section ce
variable (hyp : Hyp V W KV KW)
include hyp

theorem centeredKernel_bdd (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    ∃ B, ∀ x y, |centeredKernel W μ x y| ≤ B := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  refine ⟨4 * BW, fun x y => ?_⟩
  have hwb : ∀ y, |convMeas W μ y| ≤ BW := fun y => abs_integral_le_of_bdd fun z => hBW (y, z)
  have hIb : |interE W μ μ| ≤ BW := abs_integral_le_of_bdd fun y => abs_integral_le_of_bdd
    fun x => hBW (x, y)
  unfold centeredKernel
  have := hBW (x, y); have := hwb x; have := hwb y
  have h1 := abs_add_le (W x y - convMeas W μ x - convMeas W μ y) (interE W μ μ)
  have h2 := abs_sub (W x y - convMeas W μ x) (convMeas W μ y)
  have h3 := abs_sub (W x y) (convMeas W μ x)
  simp only [Function.uncurry] at *
  linarith

theorem measurable_centeredKernel (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Measurable (Function.uncurry (centeredKernel W μ)) := by
  unfold centeredKernel
  exact ((hyp.continuous_W.measurable.sub ((measurable_convMeas hyp μ).comp measurable_fst)).sub
    ((measurable_convMeas hyp μ).comp measurable_snd)).add measurable_const

theorem Ucentered_bdd (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N : ℕ) :
    ∃ B, ∀ X, |Ucentered W μ N X| ≤ B := by
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μ
  refine ⟨N * B, fun X => ?_⟩
  unfold Ucentered
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  have hN : (0 : ℝ) < N := by exact_mod_cast h
  rw [abs_mul, abs_of_pos (by positivity)]
  have hs : |∑ i, ∑ j, centeredKernel W μ (X i) (X j)| ≤ N * N * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, ∑ j, |centeredKernel W μ (X i) (X j)| ≤ ∑ _i : Fin N, ∑ _j : Fin N, B :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hB _ _
      _ = N * N * B := by simp; ring
  calc 1 / (2 * (N : ℝ)) * |∑ i, ∑ j, centeredKernel W μ (X i) (X j)| ≤
      1 / (2 * (N : ℝ)) * (N * N * B) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ N * B := by
        have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (X ⟨0, h⟩) (X ⟨0, h⟩))
        rw [show 1 / (2 * (N : ℝ)) * (N * N * B) = N * B / 2 by field_simp]
        linarith [mul_nonneg hN.le hB0]

/-- `E_{μ^{⊗N}} U_N = ½ ∫ K(x,x) dμ`. -/
theorem integral_Ucentered (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ} (hN : 1 ≤ N) :
    ∫ X, Ucentered W μ N X ∂Measure.pi (fun _ : Fin N => μ) =
      (∫ x, centeredKernel W μ x x ∂μ) / 2 := by
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μ
  have hKm := measurable_centeredKernel hyp μ
  have hij : ∀ i j : Fin N, ∫ X, centeredKernel W μ (X i) (X j) ∂Measure.pi (fun _ : Fin N => μ) =
      if i = j then ∫ x, centeredKernel W μ x x ∂μ else 0 := by
    intro i j
    split_ifs with h
    · subst h
      have hm : Measurable fun x => centeredKernel W μ x x := hKm.comp (measurable_id.prodMk measurable_id)
      calc ∫ X, centeredKernel W μ (X i) (X i) ∂Measure.pi (fun _ : Fin N => μ)
          = ∫ x, centeredKernel W μ x x ∂((Measure.pi fun _ : Fin N => μ).map fun X => X i) :=
            (integral_map (μ := Measure.pi fun _ : Fin N => μ) (φ := fun X : Config N d => X i)
              (f := fun x => centeredKernel W μ x x) (measurable_pi_apply i).aemeasurable
              hm.aestronglyMeasurable).symm
        _ = _ := by rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq]
    · have hp : Measurable fun X : Config N d => (X i, X j) := by fun_prop
      have := integral_map (μ := Measure.pi fun _ : Fin N => μ) hp.aemeasurable
        hKm.aestronglyMeasurable
      simp only [Function.uncurry] at this
      rw [← this, map_pair_pi h, integral_prod (fun q : Torus d × Torus d =>
        centeredKernel W μ q.1 q.2) (integrable_of_bdd hKm fun q => hB q.1 q.2)]
      simp only
      simp_rw [integral_centeredKernel hyp μ]
      simp
  have hint : ∀ i j : Fin N, Integrable (fun X : Config N d => centeredKernel W μ (X i) (X j))
      (Measure.pi fun _ : Fin N => μ) := fun i j =>
    integrable_of_bdd (hKm.comp (by fun_prop : Measurable fun X : Config N d => (X i, X j)))
      fun X => hB _ _
  have hsum : ∫ X, ∑ i, ∑ j, centeredKernel W μ (X i) (X j) ∂Measure.pi (fun _ : Fin N => μ) =
      ∑ i, ∑ j, ∫ X, centeredKernel W μ (X i) (X j) ∂Measure.pi (fun _ : Fin N => μ) := by
    rw [integral_finset_sum (μ := Measure.pi fun _ : Fin N => μ) Finset.univ
      (f := fun i X => ∑ j, centeredKernel W μ (X i) (X j)) fun i _ =>
        integrable_finset_sum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_finset_sum (μ := Measure.pi fun _ : Fin N => μ) Finset.univ
      (f := fun j X => centeredKernel W μ (X i) (X j)) fun j _ => hint i j
  unfold Ucentered
  rw [integral_const_mul, hsum]
  simp_rw [hij]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp

/-- **(5.9), (5.10).** -/
theorem centered_entropy_identities_aux {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {N : ℕ} (hN : 1 ≤ N) :
    -(∫ x, centeredKernel W μ x x ∂(μ : Measure (Torus d))) / 2 ≤
        Real.log (centeredPartition W μ N) ∧
    ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤ →
      ((klDiv ν (gibbs V W N)).toReal =
        (klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))).toReal +
          ∫ X, Ucentered W μ N X ∂ν + Real.log (centeredPartition W μ N)) ∧
      klDiv ν (gibbs V W N) ≠ ⊤ := by
  set μm := (μ : Measure (Torus d))
  set P := Measure.pi fun _ : Fin N => μm
  obtain ⟨B, hB⟩ := Ucentered_bdd hyp μm N
  have hUm := measurable_Ucentered hyp μm N
  have hm := integral_Ucentered hyp μm hN
  have hei : Integrable (fun X => exp (-Ucentered W μm N X)) P :=
    integrable_of_bdd (measurable_exp.comp hUm.neg) (C := exp B) fun X => by
      rw [abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr ((neg_le_abs _).trans (hB X))
  have hUi : Integrable (Ucentered W μm N) P := integrable_of_bdd hUm hB
  refine ⟨?_, fun ν _ hν => ?_⟩
  · set m := ∫ X, Ucentered W μm N X ∂P
    have hlow : exp (-m) ≤ centeredPartition W μm N := by
      unfold centeredPartition
      have hpt : ∀ X, exp (-m) * (1 - (Ucentered W μm N X - m)) ≤ exp (-Ucentered W μm N X) :=
        fun X => by
          have := Real.add_one_le_exp (-(Ucentered W μm N X - m))
          calc exp (-m) * (1 - (Ucentered W μm N X - m)) ≤ exp (-m) * exp (-(Ucentered W μm N X - m)) :=
                mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
            _ = exp (-Ucentered W μm N X) := by rw [← exp_add]; ring_nf
      calc exp (-m) = ∫ X, exp (-m) * (1 - (Ucentered W μm N X - m)) ∂P := by
            rw [integral_const_mul, integral_sub (f := fun _ => (1 : ℝ))
              (g := fun X => Ucentered W μm N X - m) (integrable_const _) (hUi.sub (integrable_const _)),
              integral_sub (f := Ucentered W μm N) (g := fun _ => m) hUi (integrable_const _)]
            simp [m]
        _ ≤ _ := integral_mono ((integrable_const _).sub (hUi.sub (integrable_const _)) |>.const_mul _)
            hei hpt
    have := Real.log_le_log (exp_pos _) hlow
    rw [Real.log_exp, hm] at this
    linarith
  · have hg : gibbs V W N = P.tilted (fun X => -Ucentered W μm N X) := by
      rw [gibbs_eq_centered_aux hyp hμ N]
      rfl
    obtain ⟨hne, hid⟩ := klDiv_tilted (ρ := ν) (ν := P) (f := fun X => -Ucentered W μm N X)
      hUm.neg (B := B) (fun X => by rw [abs_neg]; exact hB X) hν
    rw [hg]
    refine ⟨?_, hne⟩
    rw [hid, integral_neg]
    unfold centeredPartition
    ring

end ce

end SharpLSI
