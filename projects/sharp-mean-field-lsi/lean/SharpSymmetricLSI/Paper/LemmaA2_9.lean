import SharpSymmetricLSI.Paper.LemmaA2_8

/-!
# R25 (A.9), part 9: the Lipschitz estimate for the resolvent of a smooth density

If `ρ` is a good density with smooth lift and `Q = -log ρ` satisfies `D²Q ≥ -K`, then for
`Kτ < 1` and a smooth periodic `Φ` with `Φ(x) - Φ(y) ≤ L|x - y|`, the resolvent
`u = (1 - τL_ρ)^{-1}Φ` of `exists_resolvent_smooth` satisfies
`u(x) - u(y) ≤ L/(1 - Kτ) |x - y|` (`resolvent_smooth_lip`).

`u` is only `C¹`; its heat regularizations `u_s` are smooth and satisfy
`u_s - τΔu_s + τ∇Q·∇u_s = Φ + E_s` with `E_s → 0` uniformly (the commutator of `e^{sΔ}` with the
drift vanishes in the limit because `∇u` and `∇Q` are continuous). The doubling bound for `u_s`
passes to the limit `s → 0`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal
open UnitAddTorus

namespace SharpLSI

section heatlin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem heatT_lin {t : ℝ} (ht : 0 < t) {f g : UnitAddTorus ι → ℝ} (hf : Continuous f)
    (hg : Continuous g) (a b : ℝ) (x : UnitAddTorus ι) :
    heatT t (fun y => a * f y + b * g y) x = a * heatT t f x + b * heatT t g x := by
  obtain ⟨Bf, hBf⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Bg, hBg⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have hP := integrable_heatP (ι := ι) ht
  have hi : ∀ {h : UnitAddTorus ι → ℝ}, Continuous h →
      Integrable (fun z => heatP t z * h (x - z)) := by
    intro h hh
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hh.continuousOn
    exact hP.mul_bdd (c := B) (hh.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => hB _ (mem_univ _))
  rw [heatT_eq ht (f := fun y => a * f y + b * g y)
      ((continuous_const.mul hf).add (continuous_const.mul hg)).aestronglyMeasurable,
    heatT_eq ht hf.aestronglyMeasurable, heatT_eq ht hg.aestronglyMeasurable,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hi hf).const_mul a) ((hi hg).const_mul b)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]; ring

theorem eq_of_ae_eq_continuous {f g : UnitAddTorus ι → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[volume] g) : f = g :=
  (Continuous.ae_eq_iff_eq volume hf hg).mp h

end heatlin

variable {d : ℕ}

section lip

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρs : ContDiff ℝ ∞ (ρ ∘ liftT))
include hρ hρs

theorem fderiv_negLog_eq (x : Fin d → ℝ) (k : Fin d) :
    fderiv ℝ (fun z => -Real.log (ρ (liftT z))) x (Pi.single k 1) = -betaL ρ k x := by
  have hpos : 0 < ρ (liftT x) := hρ.pos.trans_le (hρ.lower _)
  have hd : HasFDerivAt (ρ ∘ liftT) (fderiv ℝ (ρ ∘ liftT) x) x :=
    ((hρs.differentiable (by simp)) x).hasFDerivAt
  have h : HasFDerivAt (fun z => -Real.log (ρ (liftT z))) _ x := (hd.log hpos.ne').neg
  rw [h.fderiv]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, betaL, Dk,
    Function.comp]
  field_simp

/-- **The Lipschitz estimate for the smooth resolvent.** -/
theorem resolvent_smooth_lip (hd : 1 ≤ d) {τ K : ℝ} (hτ : 0 < τ) (hKτ : K * τ < 1)
    (hQ : ∀ x v, -K * ∑ i, v i ^ 2 ≤ secondDirDeriv (fun z => -Real.log (ρ (liftT z))) v x)
    {Φ : (Fin d → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦp : IsPer Φ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, Φ x - Φ y ≤ L * dE x y) {BΦ : ℝ} (hBΦ : ∀ x, |Φ x| ≤ BΦ) :
    ∃ u : Torus d → ℝ, ContDiff ℝ 1 (u ∘ liftT) ∧
      (∀ x y, u (liftT x) - u (liftT y) ≤ L / (1 - K * τ) * dE x y) ∧
      (∀ y, |u y| ≤ BΦ) ∧
      ∀ Θ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ Θ → IsPer Θ →
        ∫ y, ρ y * (Φ (secT y) - u y) * Θ (secT y) = -τ * ∫ y, u y * divRho ρ Θ (secT y) := by
  have hpos : ∀ y, 0 < ρ y := fun y => hρ.pos.trans_le (hρ.lower y)
  obtain ⟨u, hu1, hres⟩ := exists_resolvent_smooth hρ hρs hd hτ hΦ hΦp
  have huc : Continuous u := continuous_of_liftT' hu1.continuous
  suffices hboth : (∀ x y, u (liftT x) - u (liftT y) ≤ L / (1 - K * τ) * dE x y) ∧
      ∀ y, |u y| ≤ BΦ from ⟨u, hu1, hboth.1, hboth.2, hres⟩
  -- setting
  have hint : ∀ {f : Torus d → ℝ}, Continuous f → Integrable f := fun hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmem : ∀ {f : Torus d → ℝ}, Continuous f → MemLp f 2 volume := fun hf =>
    hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcomp : ∀ {F : (Fin d → ℝ) → ℝ}, Continuous F → IsPer F → Continuous fun y => F (secT y) :=
    fun {F} hF hp => continuous_of_liftT' (by
      rw [show (fun y => F (secT y)) ∘ liftT = F from comp_secT_comp_liftT hp]; exact hF)
  have hdc : ∀ k, Continuous (dpart u k) := fun k =>
    continuous_of_liftT' (contDiff_dpart (n := 0) (by simpa using hu1) k).continuous
  have hβc : ∀ k, Continuous fun y => betaL ρ k (secT y) := fun k =>
    hcomp (contDiff_betaL hρ hρs k).continuous (isPer_betaL k)
  set Φs : Torus d → ℝ := fun y => Φ (secT y)
  have hΦc : Continuous Φs := hcomp hΦ.continuous hΦp
  set h : Torus d → ℝ := fun y => ∑ k, betaL ρ k (secT y) * dpart u k y
  have hhc : Continuous h := continuous_finset_sum _ fun k _ => (hβc k).mul (hdc k)
  set g : Torus d → ℝ := fun y => (1 / τ) * (Φs y - u y) + 1 * h y
  have hgc : Continuous g := (continuous_const.mul (hΦc.sub huc)).add (continuous_const.mul hhc)
  -- Fourier form of the equation
  have hw := isWeakGrad_of_contDiff hu1
  have hcf : ∀ k, mFourierCoeff (fun y => (g y : ℂ)) k =
      4 * π ^ 2 * (∑ j, ((k j : ℂ)) ^ 2) * mFourierCoeff (fun y => (u y : ℂ)) k := by
    intro k
    refine cf_of_weak_eq hw (hint huc) (fun j => hint (hdc j)) (hint hgc) (fun Θ hΘ hp => ?_) k
    have := weak_haar_of_resolvent hρ hρs hτ hu1 hΦ hΦp hres hΘ hp
    convert this using 2
    · rfl
    · funext y; simp only [g, h, Φs]; ring
  -- bounds on β
  have hβb : ∀ k, ∃ B, ∀ x, ‖betaL ρ k x‖ ≤ B := fun k =>
    periodic_bounded (contDiff_betaL hρ hρs k).continuous (isPer_betaL k)
  choose Bβ hBβ using hβb
  set Bs := ∑ k, Bβ k
  have hBs : 0 ≤ Bs := Finset.sum_nonneg fun k _ => (norm_nonneg _).trans (hBβ k 0)
  -- the semimonotone field `B = ∇Q`
  set B : (Fin d → ℝ) → Fin d → ℝ := fun x k => -betaL ρ k x
  have hQ2 : ContDiff ℝ 2 (fun z => -Real.log (ρ (liftT z))) :=
    ((hρs.log fun x => (hpos _).ne').neg).of_le (by norm_cast)
  have hB : ∀ x y, -K * dE x y ^ 2 ≤ ∑ k, (B x k - B y k) * (x k - y k) := by
    intro x y
    have := semimono_of_hessian hQ2 hQ x y
    simpa only [fderiv_negLog_eq hρ hρs, B] using this
  -- the bound for each admissible `M`
  have hKτ' : 0 < 1 - K * τ := by linarith
  -- pointwise identities for the heat regularizations
  have hlapU : ∀ t, 0 < t → ∀ x, ∑ k, secondDirDeriv (heatT t u ∘ liftT) (Pi.single k 1) x =
      -((1 / τ) * (heatT t Φs (liftT x) - heatT t u (liftT x)) + heatT t h (liftT x)) := by
    intro t ht x
    have hsm := isSmoothT_heatT ht (hint huc)
    have hl := heat_lap (hmem huc) (hmem hgc) hcf ht
    have hlc : Continuous (lap (heatT t u)) := continuous_finset_sum _ fun i _ =>
      continuous_of_liftT' (contDiff_dpart (n := 0)
        (contDiff_dpart (n := 1) (hsm.of_le (by norm_cast)) i) i).continuous
    have hgc' : Continuous fun y => -heatT t g y := (continuous_heatT ht (hint hgc)).neg
    have hl' := congrFun (eq_of_ae_eq_continuous hlc hgc' hl) (liftT x)
    have e1 : lap (heatT t u) (liftT x) =
        ∑ k, secondDirDeriv (heatT t u ∘ liftT) (Pi.single k 1) x := by
      simp only [lap]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [dpart_liftT, dpart_comp_liftT]; rfl
    rw [← e1, hl']
    show -heatT t (fun y => (1 / τ) * (Φs y - u y) + 1 * h y) (liftT x) = _
    rw [heatT_lin ht (f := fun y => Φs y - u y) (hΦc.sub huc) hhc (1 / τ) 1,
      ← heatT_sub ht (hint hΦc) (hint huc)]
    ring
  have hgradU : ∀ t, 0 < t → ∀ x k, fderiv ℝ (heatT t u ∘ liftT) x (Pi.single k 1) =
      heatT t (dpart u k) (liftT x) := by
    intro t ht x k
    have hsm := isSmoothT_heatT ht (hint huc)
    have hg := heat_grad (hmem huc) ht hw (fun j => hint (hdc j)) k
    have hc1 : Continuous (dpart (heatT t u) k) :=
      continuous_of_liftT' (contDiff_dpart (n := 0) (hsm.of_le (by norm_cast)) k).continuous
    have := congrFun (eq_of_ae_eq_continuous hc1 (continuous_heatT ht (hint (hdc k))) hg) (liftT x)
    rw [dpart_liftT] at this
    exact this
  have hβper : ∀ k x, betaL ρ k (secT (liftT x)) = betaL ρ k x := fun k x =>
    (isPer_betaL k).secT_liftT x
  have hΦper : ∀ x, Φs (liftT x) = Φ x := fun x => hΦp.secT_liftT x
  -- the regularized equations with small errors
  have hKτ' : 0 < 1 - K * τ := by linarith
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hs : ∀ n, 0 < s n := fun n => by positivity
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set U : ℕ → (Fin d → ℝ) → ℝ := fun n => heatT (s n) u ∘ liftT
  have hU : ∀ n, ContDiff ℝ 2 (U n) := fun n =>
    (isSmoothT_heatT (hs n) (hint huc)).of_le (by norm_cast)
  have hUp : ∀ n, IsPer (U n) := fun n m z => by simp only [U, Function.comp, liftT_add_intVec]
  set E : ℕ → (Fin d → ℝ) → ℝ := fun n z => (heatT (s n) Φs (liftT z) - Φ z) +
    τ * (heatT (s n) h (liftT z) - ∑ k, betaL ρ k z * fderiv ℝ (U n) z (Pi.single k 1))
  have heq : ∀ n z, U n z - τ * ∑ k, secondDirDeriv (U n) (Pi.single k 1) z +
      τ * ∑ k, B z k * fderiv ℝ (U n) z (Pi.single k 1) = Φ z + E n z := by
    intro n z
    rw [hlapU (s n) (hs n) z]
    simp only [E, B, U, Function.comp, neg_mul, Finset.sum_neg_distrib]
    field_simp
    ring
  have hstep : ∀ η > 0, ∃ N, ∀ n ≥ N, ∀ z, |E n z| ≤ η / 2 := by
    intro η hη
    set ε := η / (2 * (1 + τ + τ * Bs))
    have hε : 0 < ε := by positivity
    obtain ⟨N1, hN1⟩ := uniform_heatT hΦc hs hs0 ε hε
    obtain ⟨N2, hN2⟩ := uniform_heatT hhc hs hs0 ε hε
    have hN3 : ∀ k, ∃ N, ∀ n ≥ N, ∀ x, |heatT (s n) (dpart u k) x - dpart u k x| ≤ ε :=
      fun k => uniform_heatT (hdc k) hs hs0 ε hε
    choose N3 hN3 using hN3
    refine ⟨max (max N1 N2) (Finset.univ.sup N3), fun n hn z => ?_⟩
    have hn1 : n ≥ N1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : n ≥ N2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn3 : ∀ k, n ≥ N3 k := fun k =>
      le_trans (le_trans (Finset.le_sup (Finset.mem_univ k)) (le_max_right _ _)) hn
    have e1 : |heatT (s n) Φs (liftT z) - Φ z| ≤ ε := by rw [← hΦper z]; exact hN1 n hn1 _
    have e2 : |heatT (s n) h (liftT z) - h (liftT z)| ≤ ε := hN2 n hn2 _
    have e3 : |h (liftT z) - ∑ k, betaL ρ k z * fderiv ℝ (U n) z (Pi.single k 1)| ≤ ε * Bs := by
      simp only [h, U, hgradU (s n) (hs n), hβper, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← mul_sub, abs_mul, mul_comm ε]
      refine mul_le_mul (by rw [← Real.norm_eq_abs]; exact hBβ k z) ?_ (abs_nonneg _)
        ((norm_nonneg _).trans (hBβ k z))
      rw [abs_sub_comm]; exact hN3 k n (hn3 k) _
    have e4 : |heatT (s n) h (liftT z) - ∑ k, betaL ρ k z * fderiv ℝ (U n) z (Pi.single k 1)| ≤
        ε + ε * Bs := by
      have := abs_add_le (heatT (s n) h (liftT z) - h (liftT z))
        (h (liftT z) - ∑ k, betaL ρ k z * fderiv ℝ (U n) z (Pi.single k 1))
      rw [sub_add_sub_cancel] at this
      linarith
    simp only [E]
    calc |heatT (s n) Φs (liftT z) - Φ z + τ * (heatT (s n) h (liftT z) -
          ∑ k, betaL ρ k z * fderiv ℝ (U n) z (Pi.single k 1))|
        ≤ |heatT (s n) Φs (liftT z) - Φ z| + τ * |heatT (s n) h (liftT z) -
          ∑ k, betaL ρ k z * fderiv ℝ (U n) z (Pi.single k 1)| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_of_pos hτ]
      _ ≤ ε + τ * (ε + ε * Bs) := add_le_add e1 (mul_le_mul_of_nonneg_left e4 hτ.le)
      _ = η / 2 := by
          simp only [ε]; field_simp; ring
  have hlimU : ∀ x, Tendsto (fun n => U n x) atTop (𝓝 (u (liftT x))) := by
    intro x
    have hs0' : Tendsto s atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hs0, Eventually.of_forall hs⟩
    exact (tendsto_heatT_of_continuous huc _).comp hs0'
  refine ⟨?_, fun y => ?_⟩
  swap
  · -- the maximum principle
    obtain ⟨x, rfl⟩ : ∃ x, liftT x = y := ⟨secT y, liftT_secT y⟩
    rw [abs_le]
    have hup : ∀ η > 0, u (liftT x) ≤ BΦ + η := by
      intro η hη
      obtain ⟨N, hN⟩ := hstep η hη
      refine le_of_tendsto (hlimU x) (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
      have := max_bound (hU n) (hUp n) hτ (η := η / 2) (fun z => (le_abs_self _).trans (hBΦ z))
        (fun z => (le_abs_self _).trans (hN n hn z)) (heq n) x
      linarith
    have hlow : ∀ η > 0, -BΦ - η ≤ u (liftT x) := by
      intro η hη
      obtain ⟨N, hN⟩ := hstep η hη
      refine ge_of_tendsto (hlimU x) (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
      have hneg : IsPer (fun z => -U n z) := fun m z => by simp only [hUp n m z]
      have hU' : ContDiff ℝ 2 (fun z => -U n z) := (hU n).neg
      have heq' : ∀ z, (fun z => -U n z) z -
          τ * ∑ k, secondDirDeriv (fun z => -U n z) (Pi.single k 1) z +
          τ * ∑ k, B z k * fderiv ℝ (fun z => -U n z) z (Pi.single k 1) =
            (fun z => -Φ z) z + (fun z => -E n z) z := by
        intro z
        have h2 : ∀ k, secondDirDeriv (fun z => -U n z) (Pi.single k 1) z =
            -secondDirDeriv (U n) (Pi.single k 1) z := fun k => by
          unfold secondDirDeriv
          have : (fun y => fderiv ℝ (fun z => -U n z) y (Pi.single k 1)) =
              fun y => -fderiv ℝ (U n) y (Pi.single k 1) := by
            funext y; rw [fderiv_fun_neg]; rfl
          rw [this, fderiv_fun_neg]; rfl
        have h1 : ∀ k, fderiv ℝ (fun z => -U n z) z (Pi.single k 1) =
            -fderiv ℝ (U n) z (Pi.single k 1) := fun k => by rw [fderiv_fun_neg]; rfl
        simp only [h1, h2, Finset.sum_neg_distrib, mul_neg]
        have := heq n z
        linarith
      have := max_bound hU' hneg hτ (BF := BΦ) (η := η / 2) (fun z => (neg_le_abs _).trans (hBΦ z))
        (fun z => (neg_le_abs _).trans (hN n hn z)) heq' x
      linarith
    constructor
    · refine le_of_forall_pos_le_add fun η hη => ?_
      have := hlow η hη; linarith
    · exact le_of_forall_pos_le_add fun η hη => hup η hη
  suffices hM : ∀ M, 0 < M → L ≤ M * (1 - K * τ) → ∀ x y,
      u (liftT x) - u (liftT y) ≤ M * dE x y by
    intro x y
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hdE := dE_nonneg x y
    set δ := ε / (dE x y + 1)
    have hδ : 0 < δ := by positivity
    have h1 := hM (L / (1 - K * τ) + δ) (by positivity) (by
      rw [add_mul, div_mul_cancel₀ _ hKτ'.ne']; nlinarith [mul_pos hδ hKτ']) x y
    have h2 : δ * dE x y ≤ ε := by
      simp only [δ]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  intro M hM hML x y
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨N, hN⟩ := hstep η hη
  refine le_of_tendsto ((hlimU x).sub (hlimU y)) (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
  have := doubling_bound (hU n) (hUp n) hτ hM hML (by positivity) hL (hN n hn) hB (heq n) x y
  linarith

end lip

end SharpLSI
