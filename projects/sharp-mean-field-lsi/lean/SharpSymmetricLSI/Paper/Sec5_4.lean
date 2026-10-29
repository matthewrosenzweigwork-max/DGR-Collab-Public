import SharpSymmetricLSI.Paper.Sec5_3

/-!
# R19 (Lemma 5.2), part 4: the partition functions and (5.6), (5.7)

For `s ≥ 0` let `Z_N(s) = ∫ e^{-s U_N} dμ^{⊗N}` and `Q = μ^{⊗N}` tilted by `-s U_N` (symmetric, of
finite entropy). `H(Q|Q) = 0 = H(Q|μ^{⊗N}) + s E_Q U_N + log Z_N(s)`, so joint coercivity bounds
`log Z_N(s)` above; Jensen bounds it below. With `s = 1` (`Z_N(1) = K_N`) and `s = p = 1 + c/2`
(coercive with constant `c/2`) this gives (5.7); (5.6) follows from (5.10) and joint coercivity.
-/

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem Ucentered_comp_perm_S5 (μ : Measure (Torus d)) {N : ℕ} (σ : Equiv.Perm (Fin N))
    (X : Config N d) : Ucentered W μ N (X ∘ σ) = Ucentered W μ N X := by
  unfold Ucentered
  congr 1
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp σ (fun i => ∑ j, centeredKernel W μ (X i) (X (σ j)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp σ (fun j => centeredKernel W μ (X i) (X j))

/-- Jensen: `log ∫ e^{-f} dP ≥ -∫ f dP` for bounded measurable `f`. -/
theorem neg_integral_le_log_integral_exp {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {f : α → ℝ} (hfm : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    -∫ x, f x ∂P ≤ Real.log (∫ x, exp (-f x) ∂P) := by
  have hfi : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hei : Integrable (fun x => exp (-f x)) P :=
    Integrable.of_bound (measurable_exp.comp hfm.neg).aestronglyMeasurable (exp B)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr ((neg_le_abs _).trans (hB x)))
  set m := ∫ x, f x ∂P
  have hpt : ∀ x, exp (-m) * (1 - (f x - m)) ≤ exp (-f x) := fun x => by
    have := Real.add_one_le_exp (-(f x - m))
    calc exp (-m) * (1 - (f x - m)) ≤ exp (-m) * exp (-(f x - m)) :=
          mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
      _ = exp (-f x) := by rw [← exp_add]; ring_nf
  have hlow : exp (-m) ≤ ∫ x, exp (-f x) ∂P := by
    calc exp (-m) = ∫ x, exp (-m) * (1 - (f x - m)) ∂P := by
          rw [integral_const_mul, integral_sub (f := fun _ => (1 : ℝ))
            (g := fun x => f x - m) (integrable_const _) (hfi.sub (integrable_const _)),
            integral_sub (f := f) (g := fun _ => m) hfi (integrable_const _)]
          simp [m]
      _ ≤ _ := integral_mono ((integrable_const _).sub (hfi.sub (integrable_const _)) |>.const_mul _)
          hei hpt
  have := Real.log_le_log (exp_pos _) hlow
  rwa [Real.log_exp] at this

section part
variable (hyp : Hyp V W KV KW)
include hyp

/-- Upper bound for `log Z_N(s)` from joint coercivity. -/
theorem log_partition_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {s c' : ℝ} (hs : 0 ≤ s)
    (hc'0 : 0 < c') (hc'1 : c' ≤ 1)
    (hcoer : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → klDiv ρ μ ≠ ⊤ →
      c' * (klDiv ρ μ).toReal ≤ (klDiv ρ μ).toReal + s * Jfun W μ ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      Real.log (∫ X, exp (-(s * Ucentered W μ N X)) ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  obtain ⟨C, hC⟩ := joint_coercive hyp μ hs hc'0 hc'1 hcoer
  refine ⟨C, fun N hN => ?_⟩
  set P := Measure.pi fun _ : Fin N => μ
  obtain ⟨BK, hBK⟩ := centeredKernel_bdd hyp μ
  have hUm := measurable_Ucentered hyp μ N
  have hUb := abs_Ucentered_le hyp μ hBK N
  set f : Config N d → ℝ := fun X => -(s * Ucentered W μ N X) with hf
  have hfm : Measurable f := (hUm.const_mul s).neg
  have hfB : ∀ X, |f X| ≤ s * (N * BK / 2) := fun X => by
    simp only [hf, abs_neg, abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left (hUb X) hs
  have hfB' : ∀ X, |-f X| ≤ s * (N * BK / 2) := fun X => by rw [abs_neg]; exact hfB X
  have hei : Integrable (fun X => exp (f X)) P :=
    Integrable.of_bound (measurable_exp.comp hfm).aestronglyMeasurable (exp (s * (N * BK / 2)))
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr ((le_abs_self _).trans (hfB X)))
  haveI hQ : IsProbabilityMeasure (P.tilted f) := isProbabilityMeasure_tilted hei
  set Q := P.tilted f
  -- `Q` is symmetric and of finite entropy relative to `μ^{⊗N}`
  have hsym : IsSymmetricMeasure Q :=
    isSymmetricMeasure_tilted μ hfm fun σ X => by simp only [hf, Ucentered_comp_perm_S5]
  have hback : Q.tilted (fun X => -f X) = P := by
    rw [tilted_tilted hei]
    have : (f + fun X => -f X) = 0 := by funext X; simp
    rw [this, tilted_zero]
  have hQP : klDiv Q P ≠ ⊤ := by
    have h0 : klDiv Q Q ≠ ⊤ := by simp
    have := (klDiv_tilted (ρ := Q) (ν := Q) (f := fun X => -f X) hfm.neg hfB' h0).1
    rwa [hback] at this
  -- the exact identity at `ν = Q`
  have hid := (klDiv_tilted (ρ := Q) (ν := P) (f := f) hfm hfB hQP).2
  rw [klDiv_self, ENNReal.toReal_zero] at hid
  have hJ := hC N hN Q hQ hsym hQP
  have hH0 : 0 ≤ (klDiv Q P).toReal := ENNReal.toReal_nonneg
  have hint : ∫ X, f X ∂Q = -(s * ∫ X, Ucentered W μ N X ∂Q) := by
    simp only [hf]; rw [integral_neg, integral_const_mul]
  rw [hint] at hid
  have : c' / 4 * (klDiv Q P).toReal ≥ 0 := by positivity
  linarith

end part

section ref
variable (hyp : Hyp V W KV KW)
include hyp

theorem klDiv_pi_ne_top_of_gibbs {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {N : ℕ} {ν : Measure (Config N d)} [IsProbabilityMeasure ν]
    (h : klDiv ν (gibbs V W N) ≠ ⊤) :
    klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤ := by
  set μm := (μ : Measure (Torus d))
  set P := Measure.pi fun _ : Fin N => μm
  haveI := gibbs_isProbabilityMeasure hyp N
  obtain ⟨B, hB⟩ := Ucentered_bdd hyp μm N
  have hUm := measurable_Ucentered hyp μm N
  have hg : gibbs V W N = P.tilted (fun X => -Ucentered W μm N X) := by
    rw [gibbs_eq_centered_aux hyp hμ N]
    rfl
  have hei : Integrable (fun X => exp (-Ucentered W μm N X)) P :=
    Integrable.of_bound (measurable_exp.comp hUm.neg).aestronglyMeasurable (exp B)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr ((neg_le_abs _).trans (hB X)))
  have hback : (gibbs V W N).tilted (Ucentered W μm N) = P := by
    rw [hg, tilted_tilted hei]
    have : ((fun X => -Ucentered W μm N X) + Ucentered W μm N) = 0 := by funext X; simp
    rw [this, tilted_zero]
  have := (klDiv_tilted (ρ := ν) (ν := gibbs V W N) (f := Ucentered W μm N) hUm hB h).1
  rwa [hback] at this

/-- **Lemma 5.2**, conditional on the mean-field coercivity of Lemma 4.2 (`hco`). -/
theorem reference_entropy_of {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    (hco : MFCoercive V W μ) :
    ∃ C p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      (∀ ν : Measure (Config N d), IsProbabilityMeasure ν → IsSymmetricMeasure ν →
        klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
          ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1)) ∧
      |Real.log (centeredPartition W μ N)| ≤ C ∧
      ∫ X, (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C := by
  obtain ⟨c, hc0, hc1, hc⟩ := mf_coercive_of hyp hμ hco
  obtain ⟨BK, hBK⟩ := centeredKernel_bdd hyp (μ : Measure (Torus d))
  have hBK0 : 0 ≤ BK := (abs_nonneg _).trans (hBK (Classical.arbitrary _) (Classical.arbitrary _))
  -- coercivity for `s = 1` and `s = p`
  have hco1 : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → klDiv ρ (μ : Measure (Torus d)) ≠ ⊤ →
      c * (klDiv ρ (μ : Measure (Torus d))).toReal ≤ (klDiv ρ (μ : Measure (Torus d))).toReal + 1 * Jfun W (μ : Measure (Torus d)) ρ := fun ρ hρ h => by
    rw [one_mul]; exact hc ρ hρ h
  set p : ℝ := 1 + c / 2
  have hp1 : 1 < p := by simp only [p]; linarith
  have hcop : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → klDiv ρ (μ : Measure (Torus d)) ≠ ⊤ →
      c / 2 * (klDiv ρ (μ : Measure (Torus d))).toReal ≤ (klDiv ρ (μ : Measure (Torus d))).toReal + p * Jfun W (μ : Measure (Torus d)) ρ := fun ρ hρ h => by
    have h1 := hc ρ hρ h
    have h0 : 0 ≤ (klDiv ρ (μ : Measure (Torus d))).toReal := ENNReal.toReal_nonneg
    simp only [p]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + c / 2),
      mul_nonneg (sq_nonneg c) h0]
  obtain ⟨CJ, hCJ⟩ := joint_coercive hyp (μ : Measure (Torus d)) zero_le_one hc0 hc1 hco1
  obtain ⟨C1, hC1⟩ := log_partition_le hyp (μ : Measure (Torus d)) zero_le_one hc0 hc1 hco1
  obtain ⟨Cp, hCp⟩ := log_partition_le hyp (μ : Measure (Torus d)) (by linarith) (by linarith) (by linarith) hcop
  set CA := max C1 (BK / 2)
  set D := max (CJ + CA) 0
  set Cf := 4 / c * (1 + D)
  have hCf : 0 < Cf := by positivity
  set C := max Cf (max CA (exp (Cp + p * CA)))
  refine ⟨C, p, hp1, fun N hN => ?_⟩
  set P := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  have hlogK : |Real.log (centeredPartition W μ N)| ≤ CA := by
    have hup : Real.log (centeredPartition W μ N) ≤ C1 := by
      have := hC1 N hN
      simp only [one_mul] at this
      exact this
    have hlo := (centered_entropy_identities_aux hyp hμ hN).1
    have hdiag : |∫ x, centeredKernel W (μ : Measure (Torus d)) x x ∂(μ : Measure (Torus d))| ≤ BK := by
      have := norm_integral_le_of_norm_le_const (μ := (μ : Measure (Torus d)))
        (Filter.Eventually.of_forall fun x => (show ‖centeredKernel W (μ : Measure (Torus d)) x x‖ ≤ BK by
          rw [Real.norm_eq_abs]; exact hBK x x))
      simpa [Real.norm_eq_abs] using this
    rw [abs_le]
    constructor
    · have := (abs_le.mp hdiag).2
      have : -(BK / 2) ≤ -(∫ x, centeredKernel W (μ : Measure (Torus d)) x x ∂(μ : Measure (Torus d))) / 2 := by linarith
      linarith [le_max_right C1 (BK / 2)]
    · exact hup.trans (le_max_left _ _)
  refine ⟨fun ν hν hsym => ?_, hlogK.trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  · -- (5.6)
    by_cases hfin : klDiv ν (gibbs V W N) = ⊤
    · rw [hfin, top_add, ENNReal.mul_top (by simp; exact hCf.trans_le (le_max_left _ _))]
      exact le_top
    have hH := klDiv_pi_ne_top_of_gibbs hyp hμ hfin
    obtain ⟨hid, -⟩ := (centered_entropy_identities_aux hyp hμ hN).2 ν hν hH
    have hJ := hCJ N hN ν hν hsym hH
    simp only [one_mul] at hJ
    set H0 := (klDiv ν P).toReal
    set HP := (klDiv ν (gibbs V W N)).toReal
    have hHP : 0 ≤ HP := ENNReal.toReal_nonneg
    have hD : CJ + CA ≤ D := le_max_left _ _
    have hD0 : 0 ≤ D := le_max_right _ _
    have hlogK' := (abs_le.mp hlogK).1
    have hH0 : H0 ≤ Cf * (HP + 1) := by
      have h1 : c / 4 * H0 ≤ HP + CJ + CA := by linarith
      have h2 : H0 ≤ 4 / c * (HP + CJ + CA) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc0]; linarith
      have h3 : HP + CJ + CA ≤ (1 + D) * (HP + 1) := by nlinarith
      calc H0 ≤ 4 / c * (HP + CJ + CA) := h2
        _ ≤ 4 / c * ((1 + D) * (HP + 1)) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = Cf * (HP + 1) := by simp only [Cf]; ring
    calc klDiv ν P = ENNReal.ofReal H0 := (ENNReal.ofReal_toReal hH).symm
      _ ≤ ENNReal.ofReal (Cf * (HP + 1)) := ENNReal.ofReal_le_ofReal hH0
      _ = ENNReal.ofReal Cf * (klDiv ν (gibbs V W N) + 1) := by
          rw [ENNReal.ofReal_mul hCf.le, ENNReal.ofReal_add hHP zero_le_one, ENNReal.ofReal_one,
            ENNReal.ofReal_toReal hfin]
      _ ≤ ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) := by
          gcongr; exact le_max_left _ _
  · -- (5.7): `∫ p_N^p = Z_N(p) / K_N^p`
    have hK : 0 < centeredPartition W μ N := by
      unfold centeredPartition
      have hUm := measurable_Ucentered hyp (μ : Measure (Torus d)) N
      obtain ⟨B, hB⟩ := Ucentered_bdd hyp (μ : Measure (Torus d)) N
      exact integral_exp_pos (Integrable.of_bound (measurable_exp.comp hUm.neg).aestronglyMeasurable
        (exp B) (Filter.Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
          exact exp_le_exp.mpr ((neg_le_abs _).trans (hB X))))
    have hZp : 0 < ∫ X, exp (-(p * Ucentered W (μ : Measure (Torus d)) N X)) ∂P := by
      have hUm := measurable_Ucentered hyp (μ : Measure (Torus d)) N
      obtain ⟨B, hB⟩ := Ucentered_bdd hyp (μ : Measure (Torus d)) N
      refine integral_exp_pos (Integrable.of_bound ((measurable_exp.comp (hUm.const_mul p).neg)).aestronglyMeasurable
        (exp (p * B)) (Filter.Eventually.of_forall fun X => ?_))
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      refine exp_le_exp.mpr ?_
      have := neg_le_abs (Ucentered W (μ : Measure (Torus d)) N X)
      have := hB X
      nlinarith
    have hrw : ∀ X, (exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p =
        exp (-(p * Ucentered W (μ : Measure (Torus d)) N X)) / centeredPartition W μ N ^ p := fun X => by
      rw [Real.div_rpow (exp_pos _).le hK.le, ← Real.exp_mul]
      ring_nf
    simp_rw [hrw]
    rw [integral_div]
    have hlog : Real.log ((∫ X, exp (-(p * Ucentered W (μ : Measure (Torus d)) N X)) ∂P) /
        centeredPartition W μ N ^ p) ≤ Cp + p * CA := by
      rw [Real.log_div hZp.ne' (Real.rpow_pos_of_pos hK p).ne', Real.log_rpow hK]
      have := hCp N hN
      have := (abs_le.mp hlogK).1
      nlinarith
    have hpos : 0 < (∫ X, exp (-(p * Ucentered W (μ : Measure (Torus d)) N X)) ∂P) / centeredPartition W μ N ^ p :=
      div_pos hZp (Real.rpow_pos_of_pos hK p)
    calc (∫ X, exp (-(p * Ucentered W (μ : Measure (Torus d)) N X)) ∂P) / centeredPartition W μ N ^ p
        = exp (Real.log ((∫ X, exp (-(p * Ucentered W (μ : Measure (Torus d)) N X)) ∂P) /
            centeredPartition W μ N ^ p)) := (Real.exp_log hpos).symm
      _ ≤ exp (Cp + p * CA) := exp_le_exp.mpr hlog
      _ ≤ C := (le_max_right _ _).trans (le_max_right _ _)

end ref

end SharpLSI
