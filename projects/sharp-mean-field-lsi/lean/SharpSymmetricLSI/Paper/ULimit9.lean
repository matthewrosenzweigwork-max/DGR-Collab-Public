import SharpSymmetricLSI.Paper.ULimit8

/-!
# (6.9) for a general kernel (Phase 3, lane D; R26)

Under i.i.d. sampling from `ν`, `(U_N, Z_{N,1..J}) ⇒ (½Q_T + ½d_κ, z_1..z_J)` under `γ`:
the truncated quadratic part converges by the CLT, the diagonal part by the strong law, and the
remainders are uniformly small in `L¹` as the truncation level grows.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

section limit
variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
  {κ : α → α → ℝ} {e : ℕ → α → ℝ} {T : ℕ → ℕ → ℝ}

/-- The diagonal remainder `κ(x,x) - K_M(x,x)`. -/
def hdiag (κ : α → α → ℝ) (T : ℕ → ℕ → ℝ) (e : ℕ → α → ℝ) (M : ℕ) (x : α) : ℝ :=
  κ x x - kTrunc T e M x x

/-- The limiting map `(v, s) ↦ (½ ∑ T_{ab} v_a v_b + s, (v_n)_{n<J})`. -/
def phiMap (T : ℕ → ℕ → ℝ) (J R : ℕ) (q : EuclideanSpace ℝ (Fin (R + J)) × ℝ) : ℝ × (Fin J → ℝ) :=
  (1 / 2 * ∑ a : Fin (R + J), ∑ b : Fin (R + J), T a b * (q.1 a * q.1 b) + q.2,
    fun n => q.1 (Fin.castLE (Nat.le_add_left J R) n))

theorem continuous_phiMap (T : ℕ → ℕ → ℝ) (J R : ℕ) : Continuous (phiMap T J R) := by
  unfold phiMap
  fun_prop

namespace KerData
variable (hD : KerData ν κ e T)
include hD

theorem measurable_hdiag (M : ℕ) : Measurable (hdiag κ T e M) := by
  unfold hdiag
  exact (hD.meas.comp (measurable_id.prodMk measurable_id)).sub
    ((hD.measurable_kTrunc M).comp (measurable_id.prodMk measurable_id))

theorem integrable_hdiag (M : ℕ) : Integrable (hdiag κ T e M) ν := by
  obtain ⟨B, hB⟩ := hD.bdd
  exact (integrable_of_bdd (hD.meas.comp (measurable_id.prodMk measurable_id)) fun x => hB x x).sub
    (hD.integrable_kTrunc_diag M)

theorem integrable_kTrunc_left (M : ℕ) (w : α) : Integrable (fun y => kTrunc T e M y w) ν := by
  unfold kTrunc
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (((hD.eL2 (a + 1)).integrable one_le_two).mul_const _).const_mul _

end KerData

theorem sum_fin_fin_eq_range (g : ℕ → ℕ → ℝ) (M : ℕ) :
    ∑ a : Fin M, ∑ b : Fin M, g a b = ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M, g a b := by
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin M, g a b)]
  exact Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range _ _

theorem quadTrunc_eq (T : ℕ → ℕ → ℝ) (M : ℕ) (z : ℕ → ℝ) :
    quadTrunc T M z = ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M, T a b * (z a * z b) -
      ∑ a ∈ Finset.range M, T a a := by
  unfold quadTrunc
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [ha]

/-- **(6.9) for a general kernel.** -/
theorem tendstoInDistribution_Ugen (hD : KerData ν κ e T) (J : ℕ) {Q : (ℕ → ℝ) → ℝ}
    (hQ : IsSecondChaos T Q) :
    TendstoInDistribution
      (fun N (ω : ℕ → α) => (Ugen κ N (fun i : Fin N => ω i),
        fun n : Fin J => zSum e N n (fun i : Fin N => ω i)))
      atTop (fun z => (Q z / 2 + (∫ x, κ x x ∂ν) / 2, fun n : Fin J => z n))
      (fun _ => Measure.infinitePi fun _ : ℕ => ν) gammaRef := by
  set P := Measure.infinitePi fun _ : ℕ => ν
  set dK := ∫ x, κ x x ∂ν
  -- the truncated objects at level `M = R + J`
  set f : (R : ℕ) → Fin (R + J) → α → ℝ := fun R a => e (a + 1)
  set D : ℕ → ℕ → (ℕ → α) → ℝ := fun R N ω =>
    1 / 2 * ((∑ k ∈ Finset.range N, hdiag κ T e (R + J) (ω k)) / N)
  set c : ℕ → ℝ := fun R => 1 / 2 * ∫ x, hdiag κ T e (R + J) x ∂ν
  set W : ℕ → ℕ → (ℕ → α) → ℝ × (Fin J → ℝ) := fun R N ω =>
    phiMap T J R (cltVec (f R) N ω, D R N ω)
  set Yr : ℕ → (ℕ → ℝ) → ℝ × (Fin J → ℝ) := fun R z => phiMap T J R (gaussVec (R + J) z, c R)
  set κ' : ℕ → α → α → ℝ := fun R x y => κ x y - kTrunc T e (R + J) x y
  set δ : ℕ → ℝ := fun R => Real.sqrt (1 / 2 * ∫ p, κ' R p.1 p.2 ^ 2 ∂(ν.prod ν)) +
    1 / 2 * Real.sqrt (2 * ((∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) - sqSum T (R + J)))
  have hfL : ∀ R a, MemLp (f R a) 2 ν := fun R a => hD.eL2 _
  have hfm : ∀ R a, Measurable (f R a) := fun R a => hD.emeas _
  have hf0 : ∀ R a, ∫ x, f R a x ∂ν = 0 := fun R a => hD.emean _
  have hf1 : ∀ R (a b : Fin (R + J)), ∫ x, f R a x * f R b x ∂ν = if a = b then 1 else 0 :=
    fun R a b => by
      simp only [f]
      rw [hD.orth]
      by_cases h : a = b
      · simp [h]
      · have : (a : ℕ) ≠ b := fun h' => h (Fin.ext h')
        simp [h, this]
  -- the strong law for the diagonal
  have hDae : ∀ R, ∀ᵐ ω ∂P, Tendsto (fun N => D R N ω) atTop (𝓝 (c R)) := fun R => by
    set X : ℕ → (ℕ → α) → ℝ := fun k ω => hdiag κ T e (R + J) (ω k)
    have hm := hD.measurable_hdiag (R + J)
    have hXmap : ∀ k, P.map (X k) = ν.map (hdiag κ T e (R + J)) := fun k => by
      rw [show X k = hdiag κ T e (R + J) ∘ fun ω => ω k from rfl,
        ← Measure.map_map hm (measurable_pi_apply k), Measure.infinitePi_map_eval]
    have hind : iIndepFun X P := iIndepFun_infinitePi (X := fun _ => hdiag κ T e (R + J))
      fun _ => hm
    have hident : ∀ k, IdentDistrib (X k) (X 0) P P := fun k =>
      ⟨(hm.comp (measurable_pi_apply k)).aemeasurable, (hm.comp (measurable_pi_apply 0)).aemeasurable,
        by rw [hXmap, hXmap]⟩
    have hint : Integrable (X 0) P := by
      have : Integrable (hdiag κ T e (R + J)) (P.map fun ω : ℕ → α => ω 0) := by
        rw [Measure.infinitePi_map_eval]; exact hD.integrable_hdiag _
      exact this.comp_measurable (measurable_pi_apply 0)
    have hE : ∫ ω, X 0 ω ∂P = ∫ x, hdiag κ T e (R + J) x ∂ν := by
      have h := integral_map (μ := P) (measurable_pi_apply 0).aemeasurable
        hm.aestronglyMeasurable
      rw [Measure.infinitePi_map_eval] at h
      exact h.symm
    have hslln := strong_law_ae_real X hint (fun i j hij => hind.indepFun hij) hident
    filter_upwards [hslln] with ω hω
    rw [hE] at hω
    exact hω.const_mul (1 / 2)
  have hDmeas : ∀ R N, Measurable (D R N) := fun R N =>
    ((Finset.measurable_sum _ fun k _ => (hD.measurable_hdiag _).comp (measurable_pi_apply k)).div_const
      _).const_mul _
  have hW : ∀ R, TendstoInDistribution (W R) atTop (Yr R) (fun _ => P) gammaRef := fun R =>
    (tendstoInDistribution_cltVec (hfm R) (hfL R) (hf0 R) (hf1 R)).continuous_comp_prodMk_of_tendstoInMeasure_const
      (continuous_phiMap T J R)
      (tendstoInMeasure_of_tendsto_ae (fun N => (hDmeas R N).aestronglyMeasurable) (hDae R))
      (fun N => (hDmeas R N).aemeasurable)
  -- pointwise identities
  have hmapN : ∀ N, P.map (fun (ω : ℕ → α) (i : Fin N) => ω i) = Measure.pi fun _ : Fin N => ν :=
    fun N => infinitePi_map_fin ν N
  have hv : ∀ R N (ω : ℕ → α) (a : Fin (R + J)),
      cltVec (f R) N ω a = zSum e N a (fun i : Fin N => ω i) := fun R N ω a => by
    simp only [cltVec, zSum, f, PiLp.toLp_apply]
    rw [Fin.sum_univ_eq_sum_range (fun k => e (↑a + 1) (ω k))]
  have hVW_pt : ∀ R N, 1 ≤ N → ∀ ω : ℕ → α,
      (Ugen κ N (fun i : Fin N => ω i), fun n : Fin J => zSum e N n (fun i : Fin N => ω i)) -
        W R N ω = (offDiag (κ' R) N (fun i : Fin N => ω i), 0) := by
    intro R N hN ω
    have hdec := Ugen_decomp hD hN (R + J) (fun i : Fin N => ω i)
    have h1 : 1 / 2 * ∑ a : Fin (R + J), ∑ b : Fin (R + J),
        T a b * (cltVec (f R) N ω a * cltVec (f R) N ω b) =
        1 / 2 * ∑ a ∈ Finset.range (R + J), ∑ b ∈ Finset.range (R + J),
          T a b * (zSum e N a (fun i : Fin N => ω i) * zSum e N b (fun i : Fin N => ω i)) := by
      simp_rw [hv]
      rw [sum_fin_fin_eq_range (fun a b => T a b * (zSum e N a (fun i : Fin N => ω i) *
        zSum e N b (fun i : Fin N => ω i)))]
    have h2 : D R N ω = 1 / 2 * ((∑ i : Fin N, (κ (ω i) (ω i) - kTrunc T e (R + J) (ω i) (ω i))) /
        N) := by
      simp only [D, hdiag]
      rw [Fin.sum_univ_eq_sum_range (fun k => κ (ω k) (ω k) - kTrunc T e (R + J) (ω k) (ω k))]
    refine Prod.ext ?_ ?_
    · simp only [W, phiMap, Prod.fst_sub]
      rw [h1, h2, hdec]
      ring
    · funext n
      simp only [W, phiMap, Prod.snd_sub, Pi.sub_apply, Pi.zero_apply]
      rw [hv]
      simp
  have hYY_pt : ∀ R (z : ℕ → ℝ), (Q z / 2 + dK / 2, fun n : Fin J => z n) - Yr R z =
      ((Q z - quadTrunc T (R + J) z) / 2, 0) := by
    intro R z
    have hc : c R = 1 / 2 * (dK - ∑ a ∈ Finset.range (R + J), T a a) := by
      obtain ⟨B, hB⟩ := hD.bdd
      simp only [c, hdiag]
      rw [integral_sub (f := fun x => κ x x) (g := fun x => kTrunc T e (R + J) x x)
        (integrable_of_bdd (f := fun x => κ x x)
          (hD.meas.comp (measurable_id.prodMk measurable_id)) fun x => hB x x)
        (hD.integrable_kTrunc_diag _), hD.integral_kTrunc_diag]
    refine Prod.ext ?_ ?_
    · simp only [Yr, phiMap, Prod.fst_sub]
      rw [hc, quadTrunc_eq]
      have h3 : ∑ a : Fin (R + J), ∑ b : Fin (R + J), T a b * (gaussVec (R + J) z a *
          gaussVec (R + J) z b) = ∑ a ∈ Finset.range (R + J), ∑ b ∈ Finset.range (R + J),
            T a b * (z a * z b) := by
        simp only [gaussVec, PiLp.toLp_apply]
        exact sum_fin_fin_eq_range (fun a b => T a b * (z a * z b)) _
      rw [h3]; ring
    · funext n
      simp [Yr, phiMap, gaussVec]
  -- the off-diagonal kernel
  have hκ'm : ∀ R, Measurable (Function.uncurry (κ' R)) := fun R =>
    hD.meas.sub (hD.measurable_kTrunc _)
  have hκ's : ∀ R x y, κ' R x y = κ' R y x := fun R x y => by
    simp only [κ']; rw [hD.symm, hD.kTrunc_symm]
  have hκ'c : ∀ R w, ∫ y, κ' R y w ∂ν = 0 := fun R w => by
    obtain ⟨B, hB⟩ := hD.bdd
    simp only [κ']
    rw [integral_sub (integrable_of_bdd (f := fun y => κ y w)
      (hD.meas.comp (measurable_id.prodMk measurable_const)) fun y => hB y w)
      (hD.integrable_kTrunc_left _ w), hD.cent, hD.integral_kTrunc_left, sub_zero]
  have hκ'L : ∀ R, MemLp (fun p : α × α => κ' R p.1 p.2) 2 (ν.prod ν) := fun R =>
    hD.memLp_kappa.sub (hD.memLp_kTrunc _)
  -- the error bounds
  have hVW : ∀ R, ∀ᶠ N in atTop,
      Integrable (fun ω => ‖(Ugen κ N (fun i : Fin N => ω i),
        fun n : Fin J => zSum e N n (fun i : Fin N => ω i)) - W R N ω‖) P ∧
      ∫ ω, ‖(Ugen κ N (fun i : Fin N => ω i),
        fun n : Fin J => zSum e N n (fun i : Fin N => ω i)) - W R N ω‖ ∂P ≤ δ R := by
    intro R
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hnorm : ∀ ω : ℕ → α, ‖(Ugen κ N (fun i : Fin N => ω i),
        fun n : Fin J => zSum e N n (fun i : Fin N => ω i)) - W R N ω‖ =
        |offDiag (κ' R) N (fun i : Fin N => ω i)| := fun ω => by
      rw [hVW_pt R N hN ω, Prod.norm_def, norm_zero, Real.norm_eq_abs]
      exact max_eq_left (abs_nonneg _)
    simp_rw [hnorm]
    have hOL := memLp_offDiag (N := N) (hκ'L R)
    have hrm : Measurable fun (ω : ℕ → α) (i : Fin N) => ω i := by fun_prop
    have hint : Integrable (fun X : Fin N → α => |offDiag (κ' R) N X|)
        (P.map fun (ω : ℕ → α) (i : Fin N) => ω i) := by
      rw [hmapN]; exact (hOL.integrable one_le_two).abs
    refine ⟨hint.comp_measurable hrm, ?_⟩
    have e1 := integral_map (μ := P) hrm.aemeasurable hint.aestronglyMeasurable
    rw [hmapN] at e1
    rw [← e1]
    refine (integral_abs_le_sqrt' hOL).trans ?_
    refine le_add_of_le_of_nonneg (Real.sqrt_le_sqrt (integral_offDiag_sq_le hN
      (hκ'm R).aestronglyMeasurable (hκ's R) (hκ'c R) (hκ'L R))) (by positivity)
  have hYY : ∀ R, Integrable (fun z => ‖(Q z / 2 + dK / 2, fun n : Fin J => z n) - Yr R z‖)
      gammaRef ∧ ∫ z, ‖(Q z / 2 + dK / 2, fun n : Fin J => z n) - Yr R z‖ ∂gammaRef ≤ δ R := by
    intro R
    have hnorm : ∀ z, ‖(Q z / 2 + dK / 2, fun n : Fin J => z n) - Yr R z‖ =
        |Q z - quadTrunc T (R + J) z| / 2 := fun z => by
      rw [hYY_pt, Prod.norm_def, norm_zero, Real.norm_eq_abs, max_eq_left (abs_nonneg _), abs_div,
        abs_two]
    simp_rw [hnorm]
    have hL := hQ.1.sub (memLp_quadTrunc T (R + J))
    refine ⟨((hL.integrable one_le_two).abs).div_const 2, ?_⟩
    rw [integral_div]
    have h1 := integral_abs_le_sqrt' hL
    simp only [Pi.sub_apply] at h1
    rw [integral_secondChaos_sub_trunc_sq hD.T_symm hD.hs.summable hQ] at h1
    refine le_add_of_nonneg_of_le (Real.sqrt_nonneg _) ?_
    linarith
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hA := (hD.tendsto_integral_kappa_sub_kTrunc_sq).comp (tendsto_add_atTop_nat J)
    have hA' := (Real.continuous_sqrt.tendsto _).comp (hA.const_mul (1 / 2))
    have hB := (tendsto_sqSum hD.hs.summable).comp (tendsto_add_atTop_nat J)
    have hB' := ((Real.continuous_sqrt.tendsto _).comp
      ((tendsto_const_nhds (x := ∑' p : ℕ × ℕ, T p.1 p.2 ^ 2)).sub hB |>.const_mul 2)).const_mul
      (1 / 2)
    have h := hA'.add hB'
    simp only [mul_zero, sub_self, Real.sqrt_zero, add_zero] at h
    exact h
  have hV : ∀ N, AEMeasurable (fun ω : ℕ → α => (Ugen κ N (fun i : Fin N => ω i),
      fun n : Fin J => zSum e N n (fun i : Fin N => ω i))) P := fun N => by
    refine Measurable.aemeasurable (Measurable.prodMk ?_ ?_)
    · unfold Ugen
      exact (Finset.measurable_sum (f := fun (i : Fin N) (ω : ℕ → α) => ∑ j : Fin N, κ (ω i) (ω j)) _
        fun i _ => Finset.measurable_sum (f := fun (j : Fin N) (ω : ℕ → α) => κ (ω i) (ω j)) _
        fun j _ => hD.meas.comp (f := fun ω : ℕ → α => (ω (i : ℕ), ω (j : ℕ)))
          ((measurable_pi_apply (i : ℕ)).prodMk (measurable_pi_apply (j : ℕ)))).const_mul _
    · refine measurable_pi_iff.mpr fun n => ?_
      unfold zSum
      exact (Finset.measurable_sum _ fun l _ => (hD.emeas _).comp (measurable_pi_apply _)).const_mul _
  have hY : AEMeasurable (fun z : ℕ → ℝ => (Q z / 2 + dK / 2, fun n : Fin J => z n)) gammaRef :=
    (((hQ.1.aestronglyMeasurable.aemeasurable.div_const 2).add_const _)).prodMk
      (measurable_pi_iff.mpr fun n => measurable_pi_apply _).aemeasurable
  exact tendstoInDistribution_of_approx hV hY hW hδ hVW hYY

end limit

end SharpLSI
