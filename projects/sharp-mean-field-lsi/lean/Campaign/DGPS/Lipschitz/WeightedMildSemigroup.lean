import DGPS.Lipschitz.DuhamelEigenCoeff
import DGPS.Lipschitz.DuhamelC1
import DGPS.Lipschitz.SemigroupEigen
import DGPS.Lipschitz.WeightedGenerator
import DGPS.Lipschitz.WeightedSpectrum

/-!
# LIP007e: the mild solution is the weighted semigroup, with `C¹` representatives for all times

Assembly of LIP007.  For the Gibbs weight `w = gibbsW Φ` (`Φ` Lipschitz) with drift `b`
(`∇ log w = b`), and the generator/semigroup `(Lg, S)` of LIP005:

* `mild_step` (short interval, `16 B₀² T ≤ π`): the fixed point `v` of the Duhamel map
  (LIP007a/b) gives `u(t) = duhamelPotential b f v t` with weak gradient `v(t, ·)` continuous
  (LIP007c), and `u(t) = S t f` in `L²(w m)`: both have the coefficients `e^{-λ_j t} ⟨f, e_j⟩` in the
  LIP009 eigenbasis (LIP007d1 and LIP007d2), so they agree by Hilbert-basis uniqueness.
* `mild_restart`: for every `t > 0`, `S t f` has a `C¹` representative with gradient bounded by
  `2 ^ (k + 1) L`, `k = ⌈2 t / τ⌉₊`, obtained by restarting at time `τ / 2` with the
  Lipschitz constant `2 L` of the `C¹` representative of `S (τ/2) f`.
* `bounded_drift_mild_solution_with_continuous_gradient`: the packaged output.
-/
open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace LinearPMap NNReal ENNReal
namespace DGPS.Lipschitz
open DGPS.Analysis DGPS.Analysis.CompactResolvent DGPS.Lipschitz.ParabolicChainRule
variable {d : ℕ}

/-- The properties of the LIP005 generator `Lg` and semigroup `S` of the weighted form on
`L²(w m)` that are used here. -/
structure IsWeightedSemigroup (w : Torus d → ℝ) (Lg : Hw d w →ₗ.[ℝ] Hw d w)
    (S : ℝ≥0 → Hw d w →L[ℝ] Hw d w) : Prop where
  selfAdjoint : IsSelfAdjoint Lg
  mem_domain_iff : ∀ f : Hw d w, f ∈ Lg.domain ↔ MemH2 (f : Torus d → ℝ)
  form : ∀ (f : Hw d w) (hf : f ∈ Lg.domain) (Gf : Torus d → Tangent d),
    IsWeakGradient (f : Torus d → ℝ) Gf → ∀ (v : Hw d w) (Gv : Torus d → Tangent d),
    IsWeakGradient (v : Torus d → ℝ) Gv → weightedForm w Gf Gv = -⟪Lg ⟨f, hf⟩, v⟫_ℝ
  zero : ∀ f, S 0 f = f
  add : ∀ (s t : ℝ≥0) f, S (s + t) f = S s (S t f)
  symm : ∀ t, ∀ f g : Hw d w, ⟪S t f, g⟫_ℝ = ⟪f, S t g⟫_ℝ
  cont : ∀ f, Continuous fun t : ℝ≥0 => S t f
  deriv : ∀ f : Lg.domain, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S t (f : Hw d w) - f))
    (𝓝[≠] (0 : ℝ≥0)) (𝓝 (Lg f))

theorem inner_Hw_eq_integral {w : Torus d → ℝ} (a b : Hw d w) :
    ⟪a, b⟫_ℝ = ∫ x, (a : Torus d → ℝ) x * (b : Torus d → ℝ) x ∂wMeasure d w := by
  rw [L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [mul_comm]

/-- A continuous function with a bounded `L²` weak gradient is Lipschitz. -/
theorem torusLipschitz_of_weakGradient_bound {u : Torus d → ℝ} {g : Torus d → Tangent d} {M : ℝ}
    (hu : Continuous u) (hg : IsWeakGradient u g) (hgM : ∀ x, ‖g x‖ ≤ M) :
    TorusLipschitzWith M u := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hgM 0)
  obtain ⟨Cu, hCu⟩ := exists_bound_continuous hu
  have hLp : IsWeakGradientLp ∞ u g :=
    ⟨memLp_top_of_bound hu.aestronglyMeasurable Cu (Eventually.of_forall fun x => by
        simpa using hCu x),
      memLp_top_of_bound hg.memLp_grad.aestronglyMeasurable M (Eventually.of_forall hgM), hg.ibp⟩
  obtain ⟨v, hvc, hvu, hv⟩ := exists_lipschitz_rep hLp hM (Eventually.of_forall hgM)
  rw [← continuous_ae_eq hvc hu hvu]
  exact hv

/-- **LIP007e (1).** On `(0,T)` with `16 B₀² T ≤ π`, the Duhamel potential of the fixed point is
the weighted semigroup applied to `f`, and it has a `C¹` representative with gradient `v(t, ·)`. -/
theorem mild_step {T B0 L c C : ℝ} (hd : 0 < d) (hT : 0 < T) (hL : 0 ≤ L)
    {w : Torus d → ℝ} {b : Torus d → Tangent d} (hW : WeightedGenerator.WData d w b c C)
    (hint : ∫ x, w x ∂haar d = 1) (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    (hTB : 16 * B0 ^ 2 * T ≤ π) {Lg : Hw d w →ₗ.[ℝ] Hw d w} {S : ℝ≥0 → Hw d w →L[ℝ] Hw d w}
    (hS : IsWeightedSemigroup w Lg S) {f : Torus d → ℝ} (hf : TorusLipschitzWith L f) :
    ∃ v : ℝ × Torus d → Tangent d, Measurable v ∧ (∀ p, ‖v p‖ ≤ 2 * L) ∧
      ∀ t ∈ Ioo 0 T, IsWeakGradient (duhamelPotential b f v t) (fun x => v (t, x)) ∧
        Continuous (fun x => v (t, x)) ∧
        ∃ ũ : Torus d → ℝ, IsC1Periodic ũ ∧ ũ =ᵐ[haar d] duhamelPotential b f v t ∧
          (∀ x j, coordPartial j ũ x = v (t, x) j) ∧
          ∀ F : Hw d w, ((F : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] f →
            ũ =ᵐ[wMeasure d w] ((S t.toNNReal F : Hw d w) : Torus d → ℝ) := by
  obtain ⟨v, hvm, hvb, hvf, -, hgrad⟩ := lip007b_mild_gradient hT hL hb hbB hTB hf
  have hfc := continuous_of_torusLipschitz hL hf
  have hfm : MemLp f 2 (haar d) :=
    hfc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hW.bound
  obtain ⟨e, lam, G, -, -, -, -, -, hG, hE, -, -⟩ :=
    WeightedSpectrum.weighted_eigenbasis_and_growth hd hW.meas hW.pos hwb hint
  obtain ⟨-, -, -, huniq⟩ := SemigroupEigen.lip007d1_semigroup_eigen Lg S hS.selfAdjoint
    (fun f hf => (hS.mem_domain_iff f).mp hf) hS.form hS.zero hS.add hS.symm hS.cont hS.deriv
    e lam G hG hE
  refine ⟨v, hvm, hvb, fun t ht => ⟨hgrad t ht, ?_⟩⟩
  have hcv := continuous_duhamel_gradient hb hbB hfc hvm hvb hvf ht
  refine ⟨hcv, ?_⟩
  obtain ⟨ũ, h1, h2, h3⟩ := exists_isC1Periodic_of_continuous_weakGradient (hgrad t ht) hcv
    (memLp_top_duhamelPotential hb hbB hfc hvm hvb ht.1)
  refine ⟨ũ, h1, h2, h3, fun F hF => ?_⟩
  have hmemU : MemLp (duhamelPotential b f v t) 2 (wMeasure d w) :=
    (memLp_wMeasure_iff hW.pos hwb).mpr (hgrad t ht).memLp
  set U : Hw d w := hmemU.toLp _ with hU
  have hUae : (U : Torus d → ℝ) =ᵐ[wMeasure d w] duhamelPotential b f v t :=
    MemLp.coeFn_toLp hmemU
  have hcoef : ∀ j, ∫ x, duhamelPotential b f v t x * ((e j : Hw d w) : Torus d → ℝ) x
        ∂wMeasure d w =
      Real.exp (-lam j * t) * ∫ x, f x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w := by
    intro j
    have h := duhamel_eigen_coeff_ode hW hb hbB hfm hvm hvb hgrad (e j) (hG j) (hE j) t ht
    rw [integral_wMeasure hW.meas hW.pos hwb, integral_wMeasure hW.meas hW.pos hwb]
    simpa only [smul_eq_mul, mul_comm (w _), mul_assoc] using h
  have hUF : U = S t.toNNReal F := by
    refine huniq F U t.toNNReal fun j => ?_
    rw [Real.coe_toNNReal _ ht.1.le, inner_Hw_eq_integral, inner_Hw_eq_integral]
    have h1 : ∫ x, (U : Torus d → ℝ) x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w =
        ∫ x, duhamelPotential b f v t x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w := by
      refine integral_congr_ae ?_
      filter_upwards [hUae] with x hx
      rw [hx]
    have h2 : ∫ x, (F : Torus d → ℝ) x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w =
        ∫ x, f x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w := by
      refine integral_congr_ae ?_
      filter_upwards [hF] with x hx
      rw [hx]
    rw [h1, h2]
    exact hcoef j
  have : (U : Torus d → ℝ) =ᵐ[wMeasure d w] ((S t.toNNReal F : Hw d w) : Torus d → ℝ) := by
    rw [hUF]
  exact (ae_eq_wMeasure h2).trans (hUae.symm.trans this)

/-- **LIP007e (2).** Restart: for every `t < τ + k τ / 2` the semigroup applied to a Lipschitz `f`
has a `C¹` representative with gradient bounded by `2 ^ (k + 1) L`. -/
theorem mild_restart {B0 c C τ : ℝ} (hd : 0 < d) (hτ : 0 < τ)
    {w : Torus d → ℝ} {b : Torus d → Tangent d} (hW : WeightedGenerator.WData d w b c C)
    (hint : ∫ x, w x ∂haar d = 1) (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    (hτB : 16 * B0 ^ 2 * τ ≤ π) {Lg : Hw d w →ₗ.[ℝ] Hw d w} {S : ℝ≥0 → Hw d w →L[ℝ] Hw d w}
    (hS : IsWeightedSemigroup w Lg S) (k : ℕ) :
    ∀ (L : ℝ), 0 ≤ L → ∀ f : Torus d → ℝ, TorusLipschitzWith L f → ∀ t : ℝ, 0 < t →
      t < τ + k * (τ / 2) → ∀ F : Hw d w, ((F : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] f →
      ∃ ũ : Torus d → ℝ, IsC1Periodic ũ ∧
        (∃ G : Torus d → Tangent d, (∀ x, ‖G x‖ ≤ 2 ^ (k + 1) * L) ∧
          ∀ x j, coordPartial j ũ x = G x j) ∧
        ũ =ᵐ[wMeasure d w] ((S t.toNNReal F : Hw d w) : Torus d → ℝ) := by
  induction k with
  | zero =>
    intro L hL f hf t ht htk F hF
    obtain ⟨v, -, hvb, hv⟩ := mild_step hd hτ hL hW hint hb hbB hτB hS hf
    obtain ⟨-, -, ũ, h1, -, h3, h4⟩ := hv t ⟨ht, by simpa using htk⟩
    exact ⟨ũ, h1, ⟨fun x => v (t, x), fun x => by simpa [pow_one, mul_comm] using hvb (t, x), h3⟩,
      h4 F hF⟩
  | succ k ih =>
    intro L hL f hf t ht htk F hF
    obtain ⟨v, -, hvb, hv⟩ := mild_step hd hτ hL hW hint hb hbB hτB hS hf
    by_cases htτ : t < τ
    · obtain ⟨-, -, ũ, h1, -, h3, h4⟩ := hv t ⟨ht, htτ⟩
      refine ⟨ũ, h1, ⟨fun x => v (t, x), fun x => ?_, h3⟩, h4 F hF⟩
      have h2 : (2 : ℝ) ≤ 2 ^ (k + 1 + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      calc ‖v (t, x)‖ ≤ 2 * L := hvb _
        _ ≤ 2 ^ (k + 1 + 1) * L := mul_le_mul_of_nonneg_right h2 hL
    · have hs0 : 0 < τ / 2 := by positivity
      have hs : τ / 2 ∈ Ioo 0 τ := ⟨hs0, by linarith⟩
      obtain ⟨hwg, -, ũ1, h1, h2, -, h4⟩ := hv (τ / 2) hs
      have hlip : TorusLipschitzWith (2 * L) ũ1 :=
        torusLipschitz_of_weakGradient_bound h1.continuous_torus
          (hwg.congr_ae h2.symm Filter.EventuallyEq.rfl) fun x => hvb _
      set F1 : Hw d w := S (τ / 2).toNNReal F with hF1
      have hF1ae : ((F1 : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] ũ1 := (h4 F hF).symm
      have hr0 : 0 < t - τ / 2 := by linarith
      have hrk : t - τ / 2 < τ + k * (τ / 2) := by
        push_cast at htk
        linarith
      obtain ⟨ũ2, h5, ⟨G, hG1, hG2⟩, h6⟩ := ih (2 * L) (by positivity) ũ1 hlip (t - τ / 2) hr0 hrk
        F1 hF1ae
      refine ⟨ũ2, h5, ⟨G, fun x => ?_, hG2⟩, ?_⟩
      · calc ‖G x‖ ≤ 2 ^ (k + 1) * (2 * L) := hG1 x
          _ = 2 ^ (k + 1 + 1) * L := by ring
      · have hsum : S t.toNNReal F = S (t - τ / 2).toNNReal F1 := by
          have hts : t.toNNReal = (t - τ / 2).toNNReal + (τ / 2).toNNReal := by
            rw [← Real.toNNReal_add hr0.le hs0.le]
            congr 1
            ring
          rw [hF1, ← hS.add, hts]
        rw [hsum]
        exact h6

theorem integral_gibbsW_eq_one {Φ : Torus d → ℝ} {L : ℝ}
    (hΦ : TorusLipschitzWith L Φ) : ∫ x, WeightedGenerator.gibbsW Φ x ∂haar d = 1 := by
  have hc := torusLipschitz_continuous hΦ
  obtain ⟨M, hM⟩ := exists_bound_continuous hc
  obtain ⟨h1, -⟩ := WeightedGenerator.normConst_bounds hc hM
  have hZ : (∫ y, Real.exp (-Φ y) ∂haar d) ≠ 0 := (lt_of_lt_of_le (Real.exp_pos _) h1).ne'
  unfold WeightedGenerator.gibbsW
  rw [integral_div]
  exact div_self hZ

/-- **LIP007 output.**  Let `Φ` be Lipschitz, `w = gibbsW Φ`, and `b` the logarithmic gradient of `w`.
There are a generator and semigroup `(Lg, S)` of the weighted form (LIP005) and a bounded measurable
representative `b'` of `b` (`‖b'‖ ≤ L_Φ`) such that, for every Lipschitz `f`:

* on every interval `(0, T)` with `16 L_Φ² T ≤ π`, the fixed point `v` of the Duhamel map
  (`‖v‖ ≤ 2 L`) has `∇ u(t) = v(t, ·)` continuous for the Duhamel potential `u(t)`, which has a
  `C¹` representative with gradient `v(t, ·)` and equals `S t f` in `L²(w m)`;
* for every `t > 0` (any finite horizon), `S t f` has a `C¹` representative with gradient bounded
  by `2 ^ (⌈2 t / τ⌉₊ + 1) L`, `τ = π / (16 L_Φ² + 1)`. -/
theorem bounded_drift_mild_solution_with_continuous_gradient {Φ : Torus d → ℝ} {LΦ : ℝ}
    (hd : 0 < d) (hL : 0 ≤ LΦ) (hΦ : TorusLipschitzWith LΦ Φ) {b : Torus d → Tangent d}
    (hb : IsWeakGradient (fun x => Real.log (WeightedGenerator.gibbsW Φ x)) b) :
    ∃ (Lg : Hw d (WeightedGenerator.gibbsW Φ) →ₗ.[ℝ] Hw d (WeightedGenerator.gibbsW Φ))
      (S : ℝ≥0 → Hw d (WeightedGenerator.gibbsW Φ) →L[ℝ] Hw d (WeightedGenerator.gibbsW Φ)),
      IsWeightedSemigroup (WeightedGenerator.gibbsW Φ) Lg S ∧
      ∃ b' : Torus d → Tangent d, Measurable b' ∧ (∀ x, ‖b' x‖ ≤ LΦ) ∧ b' =ᵐ[haar d] b ∧
        ∀ L : ℝ, 0 ≤ L → ∀ f : Torus d → ℝ, TorusLipschitzWith L f →
          (∃ F : Hw d (WeightedGenerator.gibbsW Φ),
            ((F : Hw d (WeightedGenerator.gibbsW Φ)) : Torus d → ℝ) =ᵐ[
              wMeasure d (WeightedGenerator.gibbsW Φ)] f) ∧
          (∀ T : ℝ, 0 < T → 16 * LΦ ^ 2 * T ≤ π →
            ∃ v : ℝ × Torus d → Tangent d, Measurable v ∧ (∀ p, ‖v p‖ ≤ 2 * L) ∧
              ∀ t ∈ Ioo 0 T, IsWeakGradient (duhamelPotential b' f v t) (fun x => v (t, x)) ∧
                Continuous (fun x => v (t, x)) ∧
                ∃ ũ : Torus d → ℝ, IsC1Periodic ũ ∧ ũ =ᵐ[haar d] duhamelPotential b' f v t ∧
                  (∀ x j, coordPartial j ũ x = v (t, x) j) ∧
                  ∀ F : Hw d (WeightedGenerator.gibbsW Φ),
                    ((F : Hw d (WeightedGenerator.gibbsW Φ)) : Torus d → ℝ) =ᵐ[
                      wMeasure d (WeightedGenerator.gibbsW Φ)] f →
                    ũ =ᵐ[wMeasure d (WeightedGenerator.gibbsW Φ)]
                      ((S t.toNNReal F : Hw d (WeightedGenerator.gibbsW Φ)) : Torus d → ℝ)) ∧
          (∀ t : ℝ, 0 < t → ∀ F : Hw d (WeightedGenerator.gibbsW Φ),
            ((F : Hw d (WeightedGenerator.gibbsW Φ)) : Torus d → ℝ) =ᵐ[
              wMeasure d (WeightedGenerator.gibbsW Φ)] f →
            ∃ ũ : Torus d → ℝ, IsC1Periodic ũ ∧
              (∃ G : Torus d → Tangent d,
                (∀ x, ‖G x‖ ≤ 2 ^ (⌈2 * t / (π / (16 * LΦ ^ 2 + 1))⌉₊ + 1) * L) ∧
                ∀ x j, coordPartial j ũ x = G x j) ∧
              ũ =ᵐ[wMeasure d (WeightedGenerator.gibbsW Φ)]
                ((S t.toNNReal F : Hw d (WeightedGenerator.gibbsW Φ)) : Torus d → ℝ)) := by
  obtain ⟨-, -, -, -, Lg, S, hsa, -, hdomiff, -, hform, hS0, hadd, hsymm, hcont, hder, -, -, -⟩ :=
    WeightedGenerator.closed_weighted_form_and_generator_domain hL hΦ hb
  have hS : IsWeightedSemigroup (WeightedGenerator.gibbsW Φ) Lg S :=
    ⟨hsa, hdomiff, hform, hS0, hadd, hsymm, hcont, hder⟩
  refine ⟨Lg, S, hS, ?_⟩
  obtain ⟨c, C, hwd0⟩ := WeightedGenerator.gibbs_wdata hL hΦ
  have hbae := WeightedGenerator.log_gibbs_grad hL hΦ hb
  have hbd := ae_norm_smoothGrad_le hL hΦ
  set b' : Torus d → Tangent d := fun x =>
    if ‖smoothGrad Φ x‖ ≤ LΦ then -smoothGrad Φ x else 0 with hb'
  have hb'm : Measurable b' := by
    refine Measurable.ite (measurableSet_le measurable_smoothGrad.norm measurable_const)
      measurable_smoothGrad.neg measurable_const
  have hb'B : ∀ x, ‖b' x‖ ≤ LΦ := fun x => by
    by_cases h : ‖smoothGrad Φ x‖ ≤ LΦ
    · simp only [hb', h, ↓reduceIte, norm_neg]
    · simp only [hb', h, ↓reduceIte, norm_zero]; exact hL
  have hb'ae : (fun x => -smoothGrad Φ x) =ᵐ[haar d] b' := by
    filter_upwards [hbd] with x hx
    simp only [hb', hx, ↓reduceIte]
  have hb'b : b' =ᵐ[haar d] b := (hb'ae.symm).trans hbae.symm
  have hW := WeightedGenerator.wdata_congr_b hwd0 hb'ae
  have hint := integral_gibbsW_eq_one hΦ
  refine ⟨b', hb'm, hb'B, hb'b, fun L hL0 f hf => ?_⟩
  have hfm : MemLp f 2 (wMeasure d (WeightedGenerator.gibbsW Φ)) := by
    have hwb : ∀ᵐ x ∂haar d, c ≤ WeightedGenerator.gibbsW Φ x ∧
        WeightedGenerator.gibbsW Φ x ≤ C := Eventually.of_forall hW.bound
    exact (memLp_wMeasure_iff hW.pos hwb).mpr
      ((continuous_of_torusLipschitz hL0 hf).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  refine ⟨⟨hfm.toLp f, MemLp.coeFn_toLp hfm⟩, fun T hT hTB => ?_, fun t ht F hF => ?_⟩
  · exact mild_step hd hT hL0 hW hint hb'm hb'B hTB hS hf
  · set τ : ℝ := π / (16 * LΦ ^ 2 + 1) with hτ
    have hτ0 : 0 < τ := by positivity
    have hτB : 16 * LΦ ^ 2 * τ ≤ π := by
      rw [hτ, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    have hk : t < τ + (⌈2 * t / τ⌉₊ : ℕ) * (τ / 2) := by
      have h1 : 2 * t / τ ≤ ⌈2 * t / τ⌉₊ := Nat.le_ceil _
      have h2 : 2 * t ≤ ⌈2 * t / τ⌉₊ * τ := by
        rw [div_le_iff₀ hτ0] at h1; exact h1
      nlinarith
    exact mild_restart hd hτ0 hW hint hb'm hb'B hτB hS ⌈2 * t / τ⌉₊ L hL0 f hf t ht hk F hF

end DGPS.Lipschitz
