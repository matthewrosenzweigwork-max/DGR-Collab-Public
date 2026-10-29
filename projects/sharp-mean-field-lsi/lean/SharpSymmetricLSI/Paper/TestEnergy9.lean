import SharpSymmetricLSI.Paper.TestEnergy8
import SharpSymmetricLSI.Paper.ULimit4
import SharpSymmetricLSI.Paper.ForceApprox4

/-!
# R33: (8.14), (8.18), given Prop. 2.1 and the partition estimates of Lemma 5.2
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem sum_mul_sub_ite {J : ℕ} (a : Fin J → ℝ) (m : Fin J → Fin J → ℝ) (l : Fin J → ℝ)
    (i : Fin J) :
    ∑ j, a i * a j * m i j =
      ∑ j, a i * a j * (m i j - if (i : ℕ) = j then l i else 0) + l i * a i ^ 2 := by
  have h : ∑ j, a i * a j * (if (i : ℕ) = j then l i else 0) = l i * a i ^ 2 := by
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (fun h => hj (Fin.ext h).symm),
      mul_zero]) (by simp), if_pos rfl]
    ring
  simp only [mul_sub, Finset.sum_sub_distrib, h]
  ring

/-- **(8.14), (8.18)**: convergence of the test energies, given `Prop21Conclusion` and the
partition estimates (5.6). -/
theorem test_energy_convergence_of (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (h21 : Prop21Conclusion V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    (hpart : ∃ B p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      |Real.log (centeredPartition W μ N)| ≤ B ∧
      ∫ X, (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ B) (c : Cyl) :
    Tendsto (fun N => energy V W N (fun X => c.φ (fun i => fluct e N i X))) atTop
      (𝓝 (c.form (lamShift lam) γ)) := by
  set μm := (μ : Measure (Torus d))
  have hμ := h21.minimizer
  have hac := minimizer_ac hyp hμ
  obtain ⟨Q, hQ⟩ := exists_secondChaos_Tmat hyp hμ he
  obtain ⟨-, -, hγi, hlaw⟩ := gaussian_limit_law_of hyp h21 he hQ hC hpart
  obtain ⟨eC, heC⟩ := exists_c1_reps hd hyp hr hμ he
  have hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT) := fun j => (heC j).1
  have heCh : ∀ j, eC j =ᵐ[haar d] e j := fun j => (heC j).2.1
  have hpart' : ∃ Bp p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (rexp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => μm) ≤ Bp := by
    obtain ⟨B, p, hp, hB⟩ := hpart; exact ⟨B, p, hp, fun N hN => (hB N hN).2⟩
  have hlam : ∀ i, 0 ≤ lamShift lam i := fun i => he.lam_nonneg' (i + 1)
  obtain ⟨Ka, hKa0, hKa⟩ := exists_bound_fderiv_cyl c
  have hP : ∀ N, IsProbabilityMeasure (gibbs V W N) := fun N => gibbs_isProbabilityMeasure hyp N
  have hPac : ∀ N, gibbs V W N ≪ Measure.pi (fun _ : Fin N => μm) := fun N => by
    rw [gibbs_eq_centered_aux hyp hμ N]; exact withDensity_absolutelyContinuous _ _
  -- the target
  have htarget : c.form (lamShift lam) γ =
      ENNReal.ofReal (∫ z, cylH (lamShift lam) c (fun n => z n) ∂gammaInfOf W μm Q) := by
    have hm : Measurable fun y : Fin c.J → ℝ => ENNReal.ofReal (cylH (lamShift lam) c y) :=
      ENNReal.measurable_ofReal.comp (continuous_cylH _ c).measurable
    have h1 : c.form (lamShift lam) γ =
        ∫⁻ z, ENNReal.ofReal (cylH (lamShift lam) c (fun n => z n)) ∂γ := rfl
    rw [h1, lintegral_cyl_eq_of_cov hγ hγi hm]
    obtain ⟨K, hK⟩ := cylH_bounds hlam c
    have := hγi.1
    rw [ofReal_integral_eq_lintegral_ofReal]
    · exact integrable_of_bdd ((continuous_cylH _ c).measurable.comp (measurable_zBlock c.J))
        fun z => by rw [abs_of_nonneg (hK _).1]; exact (hK _).2
    · exact Eventually.of_forall fun z => (hK _).1
  -- the particle side
  have hzm : ∀ N, Measurable (zC eC N c.J) := fun N => measurable_pi_iff.2 fun i =>
    measurable_const.mul (Finset.measurable_sum _ fun l _ =>
      (measurable_of_contDiff (hφ _)).comp (measurable_pi_apply l))
  have hmob : ∀ i j : ℕ, ∃ K, ∀ N (X : Config N d), |mobA eC N X i j| ≤ K := fun i j => by
    obtain ⟨Ci, hCi⟩ := exists_bound_cgrad (hφ (i + 1))
    obtain ⟨Cj, hCj⟩ := exists_bound_cgrad (hφ (j + 1))
    refine ⟨d * (|Ci| * |Cj|), abs_mobA_le fun x => ?_⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |cgrad (eC (i + 1)) x k * cgrad (eC (j + 1)) x k| ≤ ∑ _k : Fin d, |Ci| * |Cj| :=
          Finset.sum_le_sum fun k _ => by
            rw [abs_mul]
            exact mul_le_mul ((hCi x k).trans (le_abs_self _)) ((hCj x k).trans (le_abs_self _))
              (abs_nonneg _) (abs_nonneg _)
      _ = d * (|Ci| * |Cj|) := by simp
  choose Kmob hKmob using hmob
  obtain ⟨G, hG⟩ : ∃ G : (N : ℕ) → Config N d → ℝ, G = fun N X => ∑ i : Fin c.J, ∑ j : Fin c.J,
      fderiv ℝ c.φ (zC eC N c.J X) (Pi.single i 1) *
        fderiv ℝ c.φ (zC eC N c.J X) (Pi.single j 1) * mobA eC N X i j := ⟨_, rfl⟩
  have hGae : ∀ N, ∀ᵐ X ∂gibbs V W N,
      gradSqC (fun X => c.φ (fun i => fluct e N i X)) X = G N X := fun N => by
    rw [hG]; exact (hPac N).ae_le (gradSqC_cyl_ae hyp hμ hφ heCh N c)
  have hGm : ∀ N, Measurable (G N) := fun N => by
    rw [hG]
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      (((continuous_fderiv_cyl c i).measurable.comp (hzm N)).mul
        ((continuous_fderiv_cyl c j).measurable.comp (hzm N))).mul (measurable_mobA hφ N i j)
  have hGb : ∀ N X, |G N X| ≤ ∑ i : Fin c.J, ∑ j : Fin c.J, Ka * Ka * Kmob i j := fun N X => by
    rw [hG]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hKa _ i) (hKa _ j) (abs_nonneg _) hKa0) (hKmob i j N X)
      (abs_nonneg _) (mul_nonneg hKa0 hKa0)
  have hE : ∀ N, energy V W N (fun X => c.φ (fun i => fluct e N i X)) =
      ENNReal.ofReal (∫ X, G N X ∂gibbs V W N) := fun N => by
    unfold energy
    rw [lintegral_congr_ae ((hGae N).mono fun X hX => by rw [hX]),
      ← ofReal_integral_eq_lintegral_ofReal (integrable_of_bdd (hGm N) (hGb N))]
    filter_upwards [hGae N] with X hX
    rw [← hX]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [show (fun N => energy V W N (fun X => c.φ (fun i => fluct e N i X))) =
    fun N => ENNReal.ofReal (∫ X, G N X ∂gibbs V W N) from funext hE, htarget]
  refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
  -- the Gaussian limit of the main term
  have hHlaw := hlaw c.J (cylHb hlam c)
  simp only [cylHb_apply] at hHlaw
  obtain ⟨KH, hKH⟩ := cylH_bounds hlam c
  have hHz : ∀ N, ∫ X, cylH (lamShift lam) c (zC eC N c.J X) ∂gibbs V W N =
      ∫ X, cylH (lamShift lam) c (fun n => fluct e N n X) ∂gibbs V W N := fun N =>
    integral_congr_ae ((hPac N).ae_le ((zC_ae_eq_fluct hac heCh N c.J).mono fun X hX => by
      simp only; rw [hX]))
  -- the mobility error
  obtain ⟨Y, hY⟩ : ∃ Y : (N : ℕ) → Config N d → Fin c.J → Fin c.J → ℝ,
      Y = fun N X (i j : Fin c.J) => mobA eC N X i j -
        (if (i : ℕ) = j then lam ((i : ℕ) + 1) else 0) := ⟨_, rfl⟩
  have hdiff : ∀ N, ∫ X, G N X ∂gibbs V W N =
      (∑ i : Fin c.J, ∑ j : Fin c.J, ∫ X, fderiv ℝ c.φ (zC eC N c.J X) (Pi.single i 1) *
        fderiv ℝ c.φ (zC eC N c.J X) (Pi.single j 1) * Y N X i j ∂gibbs V W N) +
      ∫ X, cylH (lamShift lam) c (zC eC N c.J X) ∂gibbs V W N := fun N => by
    have hYint : ∀ i j : Fin c.J, Integrable (fun X => fderiv ℝ c.φ (zC eC N c.J X)
        (Pi.single i 1) * fderiv ℝ c.φ (zC eC N c.J X) (Pi.single j 1) * Y N X i j)
        (gibbs V W N) := fun i j => by
      rw [hY]
      refine integrable_of_bdd (C := Ka * Ka * (Kmob i j + |lam (i + 1)|)) ?_ fun X => ?_
      · exact (((continuous_fderiv_cyl c i).measurable.comp (hzm N)).mul
          ((continuous_fderiv_cyl c j).measurable.comp (hzm N))).mul
          ((measurable_mobA hφ N i j).sub_const _)
      · rw [abs_mul, abs_mul]
        refine mul_le_mul (mul_le_mul (hKa _ i) (hKa _ j) (abs_nonneg _) hKa0) ?_ (abs_nonneg _)
          (mul_nonneg hKa0 hKa0)
        refine (abs_sub _ _).trans (add_le_add (hKmob i j N X) ?_)
        split_ifs <;> simp
    have hHint : Integrable (fun X => cylH (lamShift lam) c (zC eC N c.J X)) (gibbs V W N) :=
      integrable_of_bdd ((continuous_cylH _ c).measurable.comp (hzm N))
        fun X => by rw [abs_of_nonneg (hKH _).1]; exact (hKH _).2
    have hpt : ∀ X, G N X = (∑ i : Fin c.J, ∑ j : Fin c.J, fderiv ℝ c.φ (zC eC N c.J X)
        (Pi.single i 1) * fderiv ℝ c.φ (zC eC N c.J X) (Pi.single j 1) * Y N X i j) +
        cylH (lamShift lam) c (zC eC N c.J X) := fun X => by
      rw [hG, hY]
      simp only [cylH, lamShift]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact sum_mul_sub_ite (fun i => fderiv ℝ c.φ (zC eC N c.J X) (Pi.single i 1))
        (fun i j => mobA eC N X i j) (fun i => lam ((i : ℕ) + 1)) i
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add (integrable_finsetSum _
      fun i _ => integrable_finsetSum _ fun j _ => hYint i j) hHint,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hYint i j]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hYint i j]
  have hterm : ∀ i j : Fin c.J, Tendsto (fun N => ∫ X, fderiv ℝ c.φ (zC eC N c.J X)
      (Pi.single i 1) * fderiv ℝ c.φ (zC eC N c.J X) (Pi.single j 1) * Y N X i j ∂gibbs V W N)
      atTop (𝓝 0) := by
    intro i j
    have h0 := (tendsto_gibbs_abs_mob hyp hμ he hφ heCh hpart' i j).const_mul (Ka * Ka)
    rw [mul_zero] at h0
    refine squeeze_zero_norm (fun N => ?_) h0
    rw [Real.norm_eq_abs, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun X => abs_nonneg _) ?_ (Eventually.of_forall fun X => ?_))
    · refine Integrable.const_mul ?_ _
      refine integrable_of_bdd (C := Kmob i j + |lam (i + 1)|)
        ((measurable_mobA hφ N i j).sub_const _).abs fun X => ?_
      rw [abs_abs]
      refine (abs_sub _ _).trans (add_le_add (hKmob i j N X) ?_)
      split_ifs <;> simp
    · rw [hY]
      simp only
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hKa _ i) (hKa _ j) (abs_nonneg _) hKa0)
        (abs_nonneg _)
  have hsum : Tendsto (fun N => ∑ i : Fin c.J, ∑ j : Fin c.J, ∫ X, fderiv ℝ c.φ (zC eC N c.J X)
      (Pi.single i 1) * fderiv ℝ c.φ (zC eC N c.J X) (Pi.single j 1) * Y N X i j ∂gibbs V W N)
      atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin c.J)) fun i _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin c.J)) fun j _ => hterm i j
    simpa using this
  simp_rw [hdiff, hHz]
  simpa using hsum.add hHlaw

end SharpLSI
