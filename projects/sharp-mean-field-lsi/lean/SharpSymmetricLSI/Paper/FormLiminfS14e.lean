import SharpSymmetricLSI.Paper.FormLiminfS14d
import SharpSymmetricLSI.Paper.FormLiminfS15
import SharpSymmetricLSI.Paper.FormLiminfS16b
import SharpSymmetricLSI.Paper.FormLiminfS8b
import SharpSymmetricLSI.Paper.FormLiminfS11A

/-!
# R33 cross term (S14e): `tendsto_cross_cyl`

`E[f_k · L_N(-φ_N)] → E_γ[F · (-L_∞φ)]`: `genL` splits (`cross_err_le`) into the main part
`H_R(Z)` (limit by `tendsto_mul_fluct_law`, then `R → ∞` by `tendsto_alphaR`), the mobility errors
(`tendsto_mob_err`) and the force error (`force_err_bound`); `tendsto_of_approx_family` combines.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem memLp_four_of_bddMeas {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {g : α → ℝ} (hg : BddMeas g) : MemLp g 4 P ∧ ∃ K, ∀ (_ : Unit), ∫ x, g x ^ 4 ∂P ≤ K := by
  obtain ⟨hgm, M, hM⟩ := hg
  refine ⟨MemLp.of_bound hgm.aestronglyMeasurable M (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hM x), M ^ 4, fun _ => ?_⟩
  have h : ∀ x, g x ^ 4 ≤ M ^ 4 := fun x => by
    have := pow_le_pow_left₀ (abs_nonneg _) (hM x) 4
    rwa [show |g x| ^ 4 = g x ^ 4 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]]
      at this
  calc ∫ x, g x ^ 4 ∂P ≤ ∫ _x, M ^ 4 ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
          (integrable_const _) (Eventually.of_forall h)
    _ = M ^ 4 := by simp

/-- **The cross term**: `E[f_k · L_N(-φ_N)] → E_γ[F · (-L_∞φ)]`. -/
theorem tendsto_cross_cyl (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) {Y : ℕ → (ℕ → ℝ) → ℝ}
    (hY : ∀ i, IsRowVariable (Tmat W μ e) γ i (Y i)) {eC : ℕ → Torus d → ℝ}
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j) (c : Cyl)
    {Ns : ℕ → ℕ} (hNs : Tendsto Ns atTop atTop) {f : (k : ℕ) → Config (Ns k) d → ℝ}
    (hf : ∀ k, MemH1C (gibbs V W (Ns k)) (f k)) {B : ℝ} (hf2 : ∀ k, ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) ≤ B)
    (hUI : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k, ∫⁻ X in {X | M < f k X ^ 2}, ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k) ≤ ENNReal.ofReal ε)
    {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ)
    (hlaw : ∀ (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ), Tendsto (fun k => ∫ X, g (f k X, fun n => fluct e (Ns k) n X) ∂gibbs V W (Ns k)) atTop (𝓝 (∫ z, g (F z, fun n => z n) ∂γ))) :
    Tendsto (fun k => ∫ X, f k X * genL W (μ : Measure (Torus d)) eC lam (Ns k) c X ∂gibbs V W (Ns k)) atTop
      (𝓝 (∫ z, F z * (-(c.gen (lamShift lam) Y z)) ∂γ)) := by
  have hP : ∀ k, IsProbabilityMeasure (gibbs V W (Ns k)) := fun k =>
    gibbs_isProbabilityMeasure hyp (Ns k)
  have hfL : ∀ k, MemLp (f k) 2 (gibbs V W (Ns k)) := fun k => memLp_of_memH1C hyp (hf k)
  have hfm : ∀ k, AEStronglyMeasurable (f k) (gibbs V W (Ns k)) := fun k => (hfL k).aestronglyMeasurable
  have hf2' : ∀ k, MemLp (f k) 2 (gibbs V W (Ns k)) ∧ ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) ≤ B :=
    fun k => ⟨hfL k, hf2 k⟩
  obtain ⟨Cp, pp, hpp, hCp⟩ := reference_entropy hd hyp hr hμ
  have hpart : ∃ Bp p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bp :=
    ⟨Cp, pp, hpp, fun N hN => (hCp N hN).2.2⟩
  -- the kernel data
  obtain ⟨KR, hKR⟩ := kernel_approximation hd hyp hr hμ he
  choose s a ha hK using hKR.1
  set J' : ℕ → ℕ := fun R => max c.J ((s R).sup id + 1)
  have hJ : ∀ R, c.J ≤ J' R := fun R => le_max_left _ _
  have hsJ : ∀ R, ∀ q ∈ s R, q < J' R := fun R q hq =>
    lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hq)) (le_max_right _ _)
  -- the family
  set x : ℕ → ℝ := fun k => ∫ X, f k X * genL W (μ : Measure (Torus d)) eC lam (Ns k) c X
    ∂gibbs V W (Ns k)
  set u : ℕ → ℕ → ℝ := fun R k => ∫ X, f k X * crossH lam c (s R) (a R) (hJ R)
    (fun n : Fin (J' R) => fluct e (Ns k) n X) ∂gibbs V W (Ns k)
  set αR : ℕ → ℝ := fun R => ∫ z, F z * crossH lam c (s R) (a R) (hJ R)
    (fun n : Fin (J' R) => z n) ∂γ
  have hu : ∀ R, Tendsto (u R) atTop (𝓝 (αR R)) := fun R =>
    tendsto_mul_fluct_law hd hyp hr hμ he hC hγ hNs hfm hf2 hUI hF (hlaw (J' R))
      (continuous_crossH lam c (s R) (a R) (hJ R))
      (crossH_growth lam c (s R) (a R) (hJ R)).choose_spec
  have hα := tendsto_alphaR hd hyp hr hμ he hC hγ hY hF hKR hK c hJ hsJ
  -- bounds for the test functions
  have hψK : ∀ i : Fin c.J, ∃ K, 0 ≤ K ∧ ∀ w, |cylD c i w| ≤ K := fun i =>
    exists_bound_of_compact (contDiff_cylD c i).continuous (hasCompactSupport_cylD c i)
  choose Kψ hKψ0 hKψ using hψK
  have hDK : ∀ i : Fin c.J, ∃ K, 0 ≤ K ∧ ∀ w (j : Fin c.J),
      |fderiv ℝ (cylD c i) w (Pi.single j 1)| ≤ K := fun i =>
    exists_bound_fderiv_of (contDiff_cylD c i) (hasCompactSupport_cylD c i)
  choose KD hKD0 hKD using hDK
  -- the force errors
  have hforce : ∀ i : Fin c.J, ∃ εR : ℕ → ℝ, Tendsto εR atTop (𝓝 0) ∧ ∀ R, ∀ᶠ k in atTop,
      ∫ X, |f k X * cylD c i (zC eC (Ns k) c.J X) * (forceD W (μ : Measure (Torus d)) eC (Ns k) i X -
        ∑ p ∈ s R, ∑ q ∈ s R, a R p q * ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) *
          mobA eC (Ns k) X p i)| ∂gibbs V W (Ns k) ≤ εR R := fun i =>
    force_err_bound hd hyp hr hμ he hφ heC hKR ha hK hNs hfL hf2 i
      (ψ := fun k X => cylD c i (zC eC (Ns k) c.J X))
      (fun k => ((contDiff_cylD c i).continuous.measurable.comp
        (measurable_zC hφ (Ns k) c.J)).aestronglyMeasurable)
      (fun k X => hKψ i _)
  choose ε4 hε4 hε4b using hforce
  set εR : ℕ → ℝ := fun R => 1 / ((R : ℝ) + 1) + ∑ i : Fin c.J, ε4 i R
  have hε : Tendsto εR atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℕ => 1 / ((R : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun R => ∑ i : Fin c.J, ε4 i R) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.univ : Finset (Fin c.J)) fun i _ => hε4 i
    rw [show (0 : ℝ) = 0 + 0 by simp]
    exact h1.add h2
  -- the mobility errors
  have hmob3 : ∀ i j : Fin c.J, Tendsto (fun k => ∫ X, |f k X *
      fderiv ℝ (cylD c i) (zC eC (Ns k) c.J X) (Pi.single j 1) *
        (mobA eC (Ns k) X j i - if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0)|
        ∂gibbs V W (Ns k)) atTop (𝓝 0) := fun i j =>
    tendsto_mob_err hyp hμ he hφ heC hpart hNs hfm hf2'
      (H := fun k X => fderiv ℝ (cylD c i) (zC eC (Ns k) c.J X) (Pi.single j 1)) (K := KD i ^ 4)
      (fun k => by
        have hb : BddMeas fun X : Config (Ns k) d =>
            fderiv ℝ (cylD c i) (zC eC (Ns k) c.J X) (Pi.single j 1) :=
          ⟨(((contDiff_cylD c i).continuous_fderiv one_ne_zero).clm_apply
            continuous_const).measurable.comp (measurable_zC hφ (Ns k) c.J), KD i,
            fun X => hKD i _ j⟩
        refine ⟨(memLp_four_of_bddMeas hb).1, ?_⟩
        have h : ∀ X : Config (Ns k) d,
            (fderiv ℝ (cylD c i) (zC eC (Ns k) c.J X) (Pi.single j 1)) ^ 4 ≤ KD i ^ 4 := fun X => by
          have := pow_le_pow_left₀ (abs_nonneg _) (hKD i (zC eC (Ns k) c.J X) j) 4
          rwa [show ∀ y : ℝ, |y| ^ 4 = y ^ 4 from fun y => by
            rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]] at this
        calc ∫ X, (fderiv ℝ (cylD c i) (zC eC (Ns k) c.J X) (Pi.single j 1)) ^ 4 ∂gibbs V W (Ns k)
            ≤ ∫ _X, KD i ^ 4 ∂gibbs V W (Ns k) :=
              integral_mono_of_nonneg (Eventually.of_forall fun X => by positivity)
                (integrable_const _) (Eventually.of_forall h)
          _ = KD i ^ 4 := by simp)
      (j : ℕ) (i : ℕ)
  have h4q : ∀ q, ∃ K, 0 ≤ K ∧ ∀ k, ∫ X, ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) ^ 4
      ∂gibbs V W (Ns k) ≤ K := fun q => by
    obtain ⟨K, hK4⟩ := fourth_moment_zq hyp hμ he hφ heC hpart q
    have hK0 : 0 ≤ K := (integral_nonneg fun X => by positivity).trans (hK4 1 le_rfl).2
    refine ⟨K, hK0, fun k => ?_⟩
    by_cases hk : 1 ≤ Ns k
    · exact (hK4 (Ns k) hk).2
    · have h0 : Ns k = 0 := by omega
      have : ∀ X : Config (Ns k) d, ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) = 0 :=
        fun X => by
          have : (Finset.univ : Finset (Fin (Ns k))) = ∅ := by
            rw [Finset.univ_eq_empty_iff]; rw [h0]; exact Fin.isEmpty'
          rw [this, Finset.sum_empty, mul_zero]
      simp_rw [this]; simpa using hK0
  choose K4 hK40 hK4 using h4q
  have hmob5 : ∀ (i : Fin c.J) (p q : ℕ), Tendsto (fun k => ∫ X, |f k X *
      (cylD c i (zC eC (Ns k) c.J X) * ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l))) *
        (mobA eC (Ns k) X p i - if p = (i : ℕ) then lam (p + 1) else 0)| ∂gibbs V W (Ns k))
        atTop (𝓝 0) := fun i p q =>
    tendsto_mob_err hyp hμ he hφ heC hpart hNs hfm hf2'
      (H := fun k X => cylD c i (zC eC (Ns k) c.J X) *
        ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l))) (K := Kψ i ^ 4 * K4 q)
      (fun k => by
        have hb : BddMeas fun X : Config (Ns k) d => cylD c i (zC eC (Ns k) c.J X) *
            ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) :=
          (bddMeas_comp_zC hφ (Ns k) (contDiff_cylD c i).continuous (hasCompactSupport_cylD c i)).mul
            (bddMeas_eCsum hφ (Ns k) q)
        refine ⟨(memLp_four_of_bddMeas hb).1, ?_⟩
        have hZi : Integrable (fun X : Config (Ns k) d =>
            ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) ^ 4) (gibbs V W (Ns k)) := by
          obtain ⟨hm, M, hM⟩ := bddMeas_eCsum hφ (Ns k) q
          refine Integrable.of_bound (hm.pow_const 4).aestronglyMeasurable (M ^ 4)
            (Eventually.of_forall fun X => ?_)
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hM X) 4
        calc ∫ X, (cylD c i (zC eC (Ns k) c.J X) *
              ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l))) ^ 4 ∂gibbs V W (Ns k)
            ≤ ∫ X, Kψ i ^ 4 * ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) ^ 4
              ∂gibbs V W (Ns k) := by
              refine integral_mono_of_nonneg (Eventually.of_forall fun X => by positivity)
                (hZi.const_mul _) (Eventually.of_forall fun X => ?_)
              dsimp only
              rw [mul_pow]
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              have := pow_le_pow_left₀ (abs_nonneg _) (hKψ i (zC eC (Ns k) c.J X)) 4
              rwa [show ∀ y : ℝ, |y| ^ 4 = y ^ 4 from fun y => by
                rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]] at this
          _ = Kψ i ^ 4 * ∫ X, ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) ^ 4
              ∂gibbs V W (Ns k) := integral_const_mul _ _
          _ ≤ Kψ i ^ 4 * K4 q := mul_le_mul_of_nonneg_left (hK4 q k) (by positivity))
      p (i : ℕ)
  -- the eventual bound
  have hw : ∀ R, ∀ᶠ k in atTop, |x k - u R k| ≤ εR R := by
    intro R
    have hm : Tendsto (fun k => (∑ i : Fin c.J, ∑ j : Fin c.J, ∫ X, |f k X *
        fderiv ℝ (cylD c i) (zC eC (Ns k) c.J X) (Pi.single j 1) *
          (mobA eC (Ns k) X j i - if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0)|
          ∂gibbs V W (Ns k)) +
        ∑ i : Fin c.J, ∑ p ∈ s R, ∑ q ∈ s R, |a R p q| * ∫ X, |f k X *
          (cylD c i (zC eC (Ns k) c.J X) * ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l))) *
          (mobA eC (Ns k) X p i - if p = (i : ℕ) then lam (p + 1) else 0)| ∂gibbs V W (Ns k))
        atTop (𝓝 0) := by
      have h3 := tendsto_finsetSum (Finset.univ : Finset (Fin c.J)) fun i _ =>
        tendsto_finsetSum (Finset.univ : Finset (Fin c.J)) fun j _ => hmob3 i j
      have h5 := tendsto_finsetSum (Finset.univ : Finset (Fin c.J)) fun i _ =>
        tendsto_finsetSum (s R) fun p _ => tendsto_finsetSum (s R) fun q _ =>
          (hmob5 i p q).const_mul |a R p q|
      simpa using h3.add h5
    have hpos : (0 : ℝ) < 1 / ((R : ℝ) + 1) := by positivity
    have hall : ∀ᶠ k in atTop, ∀ i : Fin c.J, ∫ X, |f k X * cylD c i (zC eC (Ns k) c.J X) *
        (forceD W (μ : Measure (Torus d)) eC (Ns k) i X - ∑ p ∈ s R, ∑ q ∈ s R, a R p q *
          ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) * mobA eC (Ns k) X p i)|
          ∂gibbs V W (Ns k) ≤ ε4 i R :=
      Filter.eventually_all.2 fun i => hε4b i R
    filter_upwards [hm.eventually (gt_mem_nhds hpos), hall] with k hk1 hk2
    have herr := cross_err_le (lam := lam) hyp hμ hφ heC (Ns k) c (s R) (a R) (hJ R) (hsJ R)
      (hfL k)
    have h4 : (∑ i : Fin c.J, ∫ X, |f k X * cylD c i (zC eC (Ns k) c.J X) *
        (forceD W (μ : Measure (Torus d)) eC (Ns k) i X - ∑ p ∈ s R, ∑ q ∈ s R, a R p q *
          ((Ns k : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (q + 1) (X l)) * mobA eC (Ns k) X p i)|
          ∂gibbs V W (Ns k)) ≤ ∑ i : Fin c.J, ε4 i R :=
      Finset.sum_le_sum fun i _ => hk2 i
    simp only [x, u, εR]
    linarith
  exact tendsto_of_approx_family (u := u) (w := fun R k => x k - u R k)
    (fun R k => by ring) hu hw hε hα

end SharpLSI
