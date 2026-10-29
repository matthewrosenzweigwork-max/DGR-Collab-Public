import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

Scalar distributional-time FTC WITH the prescribed continuous trace.

Let `g` be continuous on `[a,b]` (the actual continuous compact-test pairing of
the supplied trajectory) and let `D` be a proper interval-integrable function
which is the distributional derivative of `g` on `(a,b)` against smooth tests
compactly supported in `(a,b)`. Then `g r = g a + ∫ a..r, D` for EVERY
`r ∈ [a,b]`, including both endpoints.

Route: the primitive `G` of `D` is absolutely continuous (native), its
derivative is `D` almost everywhere (native Lebesgue differentiation), and AC
integration by parts gives `∫ G θ' = -∫ D θ`. Hence `h = g - G` has vanishing
distributional derivative. A smooth du Bois-Reymond lemma (proved here: every
test minus a fixed unit-mass bump multiple is the derivative of a test) and
the native smooth fundamental lemma give `h = const` almost everywhere on
`(a,b)`; continuity of `h` upgrades this to every point of `[a,b]`.

Neither continuity of `g` nor the distributional identity can be dropped:
`source_scalar_trace_needs_continuity` gives a one-point modification with zero
distributional derivative violating the every-time identity, and the Cantor
function (recorded in EXACT_REVIEW.md, not formalized) shows that continuity
plus an almost-everywhere derivative does not suffice without the
distributional identity. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology Interval ContDiff
namespace DGRHS.Commutator

/-- `D` is the distributional derivative of `g` on `(a,b)`, tested against smooth
functions compactly supported inside `(a,b)`. -/
def SourceScalarDistributionalDerivOn (g D : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
    ∫ x in a..b, g x * deriv θ x = -∫ x in a..b, D x * θ x

lemma source_compact_subset_Ioo {a b : ℝ} (hab : a < b) {K : Set ℝ} (hK : IsCompact K)
    (hKs : K ⊆ Ioo a b) : ∃ c d, a < c ∧ c ≤ d ∧ d < b ∧ K ⊆ Icc c d := by
  rcases K.eq_empty_or_nonempty with hK0 | hne
  · refine ⟨(a + b) / 2, (a + b) / 2, by linarith, le_rfl, by linarith, ?_⟩
    rw [hK0]
    exact empty_subset _
  · exact ⟨sInf K, sSup K, (hKs (hK.sInf_mem hne)).1,
      csInf_le_csSup hne hK.bddBelow hK.bddAbove, (hKs (hK.sSup_mem hne)).2,
      fun x hx => ⟨csInf_le hK.bddBelow hx, le_csSup hK.bddAbove hx⟩⟩

lemma source_test_eq_zero_of_notMem {θ : ℝ → ℝ} {a b x : ℝ} (hs : tsupport θ ⊆ Ioo a b)
    (hx : x ∉ Ioo a b) : θ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))

/-- The primitive of a mean-zero test supported in `(a,b)` is a test supported in
`(a,b)` whose derivative is the given test. -/
lemma source_primitive_test {a b : ℝ} (hab : a < b) («ω» : ℝ → ℝ) (hω : ContDiff ℝ ∞ «ω»)
    (hωc : HasCompactSupport «ω») (hωs : tsupport «ω» ⊆ Ioo a b)
    (hω0 : ∫ x in a..b, «ω» x = 0) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..x, «ω» t) ∧
      HasCompactSupport (fun x => ∫ t in a..x, «ω» t) ∧
      tsupport (fun x => ∫ t in a..x, «ω» t) ⊆ Ioo a b ∧
      deriv (fun x => ∫ t in a..x, «ω» t) = «ω» := by
  set ψ : ℝ → ℝ := fun x => ∫ t in a..x, «ω» t with hψdef
  have hd (x : ℝ) : HasDerivAt ψ («ω» x) x :=
    intervalIntegral.integral_hasDerivAt_right (hω.continuous.intervalIntegrable a x)
      hω.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hω.continuous.continuousAt
  have hderiv : deriv ψ = «ω» := funext fun x => (hd x).deriv
  have hcd : ContDiff ℝ ∞ ψ := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨fun x => (hd x).differentiableAt, by rw [hderiv]; exact hω⟩
  obtain ⟨c, d, hac, hcd', hdb, hK⟩ := source_compact_subset_Ioo hab hωc hωs
  have hsuppω : support «ω» ⊆ Icc c d := (subset_tsupport «ω»).trans hK
  have hzero (x : ℝ) (hx : x ∉ Icc c d) : ψ x = 0 := by
    rcases not_and_or.mp hx with hx | hx
    · have hxc : x < c := not_le.mp hx
      calc ψ x = ∫ t in a..x, (0 : ℝ) := by
            refine intervalIntegral.integral_congr (fun t ht => ?_)
            have ht' : t < c := lt_of_le_of_lt (show t ≤ max a x from ht.2) (max_lt hac hxc)
            exact notMem_support.mp (fun hts => absurd (hsuppω hts).1 (not_le.mpr ht'))
        _ = 0 := by simp
    · have hxd : d < x := not_le.mp hx
      have h1 : ∫ t in a..x, «ω» t = ∫ t, «ω» t :=
        intervalIntegral.integral_eq_integral_of_support_subset
          (hsuppω.trans (fun t ht => ⟨lt_of_lt_of_le hac ht.1, ht.2.trans hxd.le⟩))
      have h2 : ∫ t in a..b, «ω» t = ∫ t, «ω» t :=
        intervalIntegral.integral_eq_integral_of_support_subset
          (hsuppω.trans (fun t ht => ⟨lt_of_lt_of_le hac ht.1, ht.2.trans hdb.le⟩))
      show ∫ t in a..x, «ω» t = 0
      rw [h1, ← h2, hω0]
  have hsuppψ : support ψ ⊆ Icc c d := fun x hx => by
    by_contra h
    exact hx (hzero x h)
  refine ⟨hcd, HasCompactSupport.intro isCompact_Icc hzero, ?_, hderiv⟩
  exact (closure_minimal hsuppψ isClosed_Icc).trans
    (fun t ht => ⟨lt_of_lt_of_le hac ht.1, lt_of_le_of_lt ht.2 hdb⟩)

/-- Smooth du Bois-Reymond lemma on a closed interval, for a function continuous
on the closed interval: vanishing distributional derivative implies constancy at
EVERY point of `[a,b]`. -/
theorem source_duBoisReymond {a b : ℝ} (hab : a < b) (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc a b))
    (h0 : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
      ∫ x in a..b, h x * deriv θ x = 0) :
    ∀ x ∈ Icc a b, h x = h a := by
  -- one fixed unit-mass smooth bump strictly inside `(a,b)`
  obtain ⟨B0, hB0out⟩ : ∃ B : ContDiffBump ((a + b) / 2), B.rOut = (b - a) / 4 :=
    ⟨⟨(b - a) / 8, (b - a) / 4, div_pos (by linarith) (by norm_num), by linarith⟩, rfl⟩
  set θ0 : ℝ → ℝ := B0.normed volume with hθ0def
  have hθ0 : ContDiff ℝ ∞ θ0 := B0.contDiff_normed (n := ⊤)
  have hθ0c : HasCompactSupport θ0 := B0.hasCompactSupport_normed
  have hθ0s : tsupport θ0 ⊆ Ioo a b := by
    rw [hθ0def, B0.tsupport_normed_eq, hB0out, Real.closedBall_eq_Icc]
    intro t ht
    have h1 : (a + b) / 2 - (b - a) / 4 ≤ t := ht.1
    have h2 : t ≤ (a + b) / 2 + (b - a) / 4 := ht.2
    exact ⟨by linarith, by linarith⟩
  have hθ0supp : support θ0 ⊆ Ioc a b := (subset_tsupport θ0).trans
    (hθ0s.trans Ioo_subset_Ioc_self)
  have hθ0int : ∫ x in a..b, θ0 x = 1 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset hθ0supp, hθ0def]
    exact B0.integral_normed
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab.le
  have hcontI {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) : IntervalIntegrable f volume a b :=
    ContinuousOn.intervalIntegrable (by rwa [hIcc])
  set c : ℝ := ∫ x in a..b, h x * θ0 x with hc
  -- every test integrates `h - c` to zero
  have key : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioo a b →
      ∫ x in a..b, (h x - c) * χ x = 0 := by
    intro χ hχ hχc hχs
    set s : ℝ := ∫ x in a..b, χ x with hs
    set «ω» : ℝ → ℝ := fun x => χ x - s * θ0 x with hωdef
    have hω : ContDiff ℝ ∞ «ω» := hχ.sub (contDiff_const.mul hθ0)
    have hKc : IsCompact (tsupport χ ∪ tsupport θ0) := hχc.isCompact.union hθ0c.isCompact
    have hωz (x : ℝ) (hx : x ∉ tsupport χ ∪ tsupport θ0) : «ω» x = 0 := by
      have h1 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hx (Or.inl h'))
      have h2 : θ0 x = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hx (Or.inr h'))
      simp only [hωdef, h1, h2, mul_zero, sub_zero]
    have hωc : HasCompactSupport «ω» := HasCompactSupport.intro hKc hωz
    have hωs : tsupport «ω» ⊆ Ioo a b := by
      refine (closure_minimal (fun x hx => ?_) hKc.isClosed).trans (union_subset hχs hθ0s)
      by_contra h'
      exact hx (hωz x h')
    have hχcont : Continuous χ := hχ.continuous
    have hθcont : Continuous θ0 := hθ0.continuous
    have hω0 : ∫ x in a..b, «ω» x = 0 := by
      simp only [hωdef]
      rw [intervalIntegral.integral_sub (hχcont.intervalIntegrable a b)
        ((hθcont.intervalIntegrable a b).const_mul s),
        intervalIntegral.integral_const_mul, hθ0int, mul_one, ← hs, sub_self]
    obtain ⟨hψ, hψc, hψs, hψd⟩ := source_primitive_test hab «ω» hω hωc hωs hω0
    have hz := h0 _ hψ hψc hψs
    rw [hψd] at hz
    have hhχ : IntervalIntegrable (fun x => h x * χ x) volume a b :=
      hcontI (hh.mul hχcont.continuousOn)
    have hhθ' : IntervalIntegrable (fun x => h x * (s * θ0 x)) volume a b :=
      hcontI (hh.mul (continuous_const.mul hθcont).continuousOn)
    have hexp : ∫ x in a..b, h x * «ω» x =
        (∫ x in a..b, h x * χ x) - s * ∫ x in a..b, h x * θ0 x := by
      simp only [hωdef, mul_sub]
      rw [intervalIntegral.integral_sub hhχ hhθ']
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      show h x * (s * θ0 x) = s * (h x * θ0 x)
      ring
    have htarget : ∫ x in a..b, (h x - c) * χ x =
        (∫ x in a..b, h x * χ x) - c * s := by
      simp only [sub_mul]
      rw [intervalIntegral.integral_sub hhχ ((hχcont.intervalIntegrable a b).const_mul c),
        intervalIntegral.integral_const_mul, ← hs]
    rw [htarget]
    rw [hexp, ← hc] at hz
    have hcs : c * s = s * c := mul_comm c s
    linarith
  -- almost-everywhere constancy on the open interval
  have hloc : LocallyIntegrableOn (fun x => h x - c) (Ioo a b) volume :=
    ((hh.mono Ioo_subset_Icc_self).sub continuousOn_const).locallyIntegrableOn
      measurableSet_Ioo
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgs => by
      have hsub : support (fun x => g x • (h x - c)) ⊆ Ioc a b := by
        intro x hx
        have hgx : g x ≠ 0 := fun h' => hx (by simp [h'])
        exact Ioo_subset_Ioc_self (hgs (subset_tsupport g hgx))
      rw [← intervalIntegral.integral_eq_integral_of_support_subset hsub]
      have := key g hg hgc hgs
      simpa only [smul_eq_mul, mul_comm] using this)
  have hae' : (fun x => h x - c) =ᵐ[volume.restrict (Ioo a b)] (fun _ => (0 : ℝ)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    exact hae
  have hEqIoo : EqOn (fun x => h x - c) (fun _ => (0 : ℝ)) (Ioo a b) :=
    Measure.eqOn_Ioo_of_ae_eq volume hae' ((hh.mono Ioo_subset_Icc_self).sub continuousOn_const)
      continuousOn_const
  have hEqIcc : EqOn (fun x => h x - c) (fun _ => (0 : ℝ)) (Icc a b) :=
    hEqIoo.of_subset_closure (hh.sub continuousOn_const) continuousOn_const
      Ioo_subset_Icc_self (closure_Ioo hab.ne).ge
  intro x hx
  have h1 := hEqIcc hx
  have h2 := hEqIcc (left_mem_Icc.mpr hab.le)
  simp only at h1 h2
  linarith

/-- The AC primitive of a proper derivative integrates against test derivatives
as a distributional primitive. -/
lemma source_primitive_distributional {a b : ℝ} (hab : a < b) (D : ℝ → ℝ)
    (hD : IntervalIntegrable D volume a b) (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hθs : tsupport θ ⊆ Ioo a b) :
    ∫ x in a..b, (∫ u in a..x, D u) * deriv θ x = -∫ x in a..b, D x * θ x := by
  have hGac : AbsolutelyContinuousOnInterval (fun x => ∫ u in a..x, D u) a b :=
    hD.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hθac : AbsolutelyContinuousOnInterval θ a b :=
    (hθ.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 θ).contDiffOn.absolutelyContinuousOnInterval
  have hθa : θ a = 0 := source_test_eq_zero_of_notMem hθs (fun h => lt_irrefl a h.1)
  have hθb : θ b = 0 := source_test_eq_zero_of_notMem hθs (fun h => lt_irrefl b h.2)
  rw [hGac.integral_mul_deriv_eq_deriv_mul hθac, hθa, hθb]
  have hderiv : ∫ x in a..b, deriv (fun x => ∫ u in a..x, D u) x * θ x =
      ∫ x in a..b, D x * θ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hD.ae_hasDerivAt_integral] with x hx hxI
    have hd := hx (uIoc_subset_uIcc hxI) a left_mem_uIcc
    rw [hd.deriv]
  rw [hderiv]
  ring

/-- **Scalar distributional FTC with the prescribed continuous trace.**
Every-time identity, including both endpoints, from continuity on the closed
interval and a proper distributional derivative on the open interval. -/
theorem source_scalar_trace_eq_primitive {a b : ℝ} (hab : a ≤ b) (g D : ℝ → ℝ)
    (hg : ContinuousOn g (Icc a b)) (hD : IntervalIntegrable D volume a b)
    (hdist : SourceScalarDistributionalDerivOn g D a b) :
    ∀ r ∈ Icc a b, g r = g a + ∫ u in a..r, D u := by
  rcases hab.eq_or_lt with rfl | hlt
  · intro r hr
    have : r = a := le_antisymm hr.2 hr.1
    subst this
    simp
  have hGcont : ContinuousOn (fun x => ∫ u in a..x, D u) (Icc a b) := by
    have := (hD.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)).continuousOn
    rwa [uIcc_of_le hab] at this
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hzero : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
      ∫ x in a..b, (g x - ∫ u in a..x, D u) * deriv θ x = 0 := by
    intro θ hθ hθc hθs
    have hθ' : Continuous (deriv θ) := hθ.continuous_deriv (by exact_mod_cast le_top)
    have hgI : IntervalIntegrable (fun x => g x * deriv θ x) volume a b :=
      ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hg.mul hθ'.continuousOn)
    have hGI : IntervalIntegrable (fun x => (∫ u in a..x, D u) * deriv θ x) volume a b :=
      ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hGcont.mul hθ'.continuousOn)
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub hgI hGI, hdist θ hθ hθc hθs,
      source_primitive_distributional hlt D hD θ hθ hθs]
    ring
  have hconst := source_duBoisReymond hlt (fun x => g x - ∫ u in a..x, D u)
    (hg.sub hGcont) hzero
  intro r hr
  have h1 := hconst r hr
  simp only [intervalIntegral.integral_same, sub_zero] at h1
  linarith

/-- The distributional derivative may be replaced by any function agreeing with it
on the closed interval. -/
lemma SourceScalarDistributionalDerivOn.congr_right {g D D' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : SourceScalarDistributionalDerivOn g D a b) (hDD : EqOn D D' (Icc a b)) :
    SourceScalarDistributionalDerivOn g D' a b := by
  intro θ hθ hθc hθs
  rw [h θ hθ hθc hθs]
  congr 1
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [uIcc_of_le hab] at hr
  simp only [hDD hr]

/-- Converse direction: an every-time primitive identity gives the distributional
derivative. -/
lemma source_scalar_distributional_of_primitive {a b : ℝ} (hab : a ≤ b) (g D : ℝ → ℝ)
    (hD : IntervalIntegrable D volume a b)
    (he : ∀ r ∈ Icc a b, g r = g a + ∫ u in a..r, D u) :
    SourceScalarDistributionalDerivOn g D a b := by
  intro θ hθ hθc hθs
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hcongr : ∫ x in a..b, g x * deriv θ x =
      ∫ x in a..b, (g a + ∫ u in a..x, D u) * deriv θ x := by
    refine intervalIntegral.integral_congr (fun r hr => ?_)
    rw [uIcc_of_le hab] at hr
    simp only [he r hr]
  have hθ' : Continuous (deriv θ) := hθ.continuous_deriv (by exact_mod_cast le_top)
  have hθa : θ a = 0 := source_test_eq_zero_of_notMem hθs (fun h' => lt_irrefl _ h'.1)
  have hθb : θ b = 0 := source_test_eq_zero_of_notMem hθs (fun h' => lt_irrefl _ h'.2)
  have hconst : ∫ x in a..b, deriv θ x = 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hθ.differentiable (by simp)) x)
      (hθ'.intervalIntegrable a b), hθa, hθb, sub_self]
  have hGcont : ContinuousOn (fun x => ∫ u in a..x, D u) (uIcc a b) :=
    (hD.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)).continuousOn
  have hGI : IntervalIntegrable (fun x => (∫ u in a..x, D u) * deriv θ x) volume a b := by
    have hGint : IntervalIntegrable (fun x => ∫ u in a..x, D u) volume a b :=
      hGcont.intervalIntegrable
    exact hGint.mul_continuousOn hθ'.continuousOn
  rw [hcongr]
  simp only [add_mul]
  rw [intervalIntegral.integral_add ((hθ'.intervalIntegrable a b).const_mul (g a)) hGI,
    intervalIntegral.integral_const_mul, hconst, mul_zero, zero_add,
    source_primitive_distributional hlt D hD θ hθ hθs]

/-- The continuity hypothesis cannot be removed: a one-point modification has
zero distributional derivative and zero initial value but violates the
every-time primitive identity at the modified time. -/
theorem source_scalar_trace_needs_continuity :
    ∃ g : ℝ → ℝ, SourceScalarDistributionalDerivOn g (fun _ => 0) 0 1 ∧ g 0 = 0 ∧
      g (1/2) ≠ g 0 + ∫ u in (0:ℝ)..(1/2), (fun _ : ℝ => (0:ℝ)) u := by
  refine ⟨fun x => if x = 1/2 then 1 else 0, ?_, by norm_num, by norm_num⟩
  intro θ _ _ _
  have h1 : ∫ x in (0:ℝ)..1, (if x = 1/2 then (1:ℝ) else 0) * deriv θ x = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ)) ?_]
    · simp
    · filter_upwards [volume.ae_ne (1/2 : ℝ)] with x hx _
      simp only [if_neg hx, zero_mul]
  simp only [zero_mul, intervalIntegral.integral_zero, neg_zero]
  exact h1

end DGRHS.Commutator
