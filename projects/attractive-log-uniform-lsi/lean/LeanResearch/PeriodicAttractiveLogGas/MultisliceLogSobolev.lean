import LeanResearch.PeriodicAttractiveLogGas.MultislicePoincare
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv

/-! Ordinary multislice entropy, source 2737–2750. Salez (2021), Section 3,
uses the color-region entropy chain and Lee–Yau (1998), Section 4.
This development does not treat the cited binary LSI or either induction
as an axiom. The final multislice LSI is still an open proof obligation. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.MultisliceLogSobolev
open MultislicePoincare FibreEntropy

/-- The same ordinary finite entropy as the frozen finite-measure convention. -/
def uniformEntropy {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  uniformAverage (fun x => f x * Real.log (f x)) -
    uniformAverage f * Real.log (uniformAverage f)

theorem uniformEntropy_eq_finiteEntropy {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    uniformEntropy f = finiteEntropy (fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹) f := by
  simp only [uniformEntropy, uniformAverage, finiteEntropy, ← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_comm]

section Conditioning
variable {Ω A : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]

/-- Exact entropy chain, retaining zero-mass coordinate values and zero means.
The conditional entropy is an actual uniform fibre entropy, not a premise. -/
theorem coordinate_entropy_chain (X : Ω → A) (f : Ω → ℝ) :
    uniformEntropy f =
      (∑ a, marginalWeight X a * uniformEntropy
        (fun x : CoordinateFibre X a => f x.val)) +
      finiteEntropy (marginalWeight X) (conditionalAverage X f) := by
  unfold uniformEntropy finiteEntropy
  rw [average_conditioning X (fun x => f x * Real.log (f x)), average_conditioning X f]
  simp only [mul_sub, Finset.sum_sub_distrib, conditionalAverage]
  ring

end Conditioning

/-- Genuine reverse-L2 coupling for nonnegative observables, including zero
means. This is the finite Jensen step used in both cited entropy recursions. -/
theorem reverse_sqrt_uniform {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    (Real.sqrt (uniformAverage f) - Real.sqrt (uniformAverage g))^2 ≤
      uniformAverage (fun x => (Real.sqrt (f x) - Real.sqrt (g x))^2) := by
  have h := reverse_sqrt_average (fun x => Real.sqrt (f x)) (fun x => Real.sqrt (g x))
  simpa only [Real.sq_sqrt (hf _), Real.sq_sqrt (hg _), uniformAverage] using h

/-- A literal finite equivalence supplies both uniform marginals of the
coupling; no uniform-law assertion is an input. -/
theorem reverse_sqrt_uniform_equiv {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (e : Ω ≃ Λ) (f : Ω → ℝ) (g : Λ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y) :
    (Real.sqrt (uniformAverage f) - Real.sqrt (uniformAverage g))^2 ≤
      uniformAverage (fun x => (Real.sqrt (f x) - Real.sqrt (g (e x)))^2) := by
  have h := reverse_sqrt_uniform f (fun x => g (e x)) hf (fun x => hg (e x))
  rw [uniformAverage_equiv e g] at h
  exact h

theorem uniformEntropy_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    uniformEntropy (fun _ : Ω => c) = 0 := by
  simp only [uniformEntropy, uniformAverage_const, sub_self]

open MeshCells LabelOccupations DiscreteOccupationIdentities FibreProjection
variable {J N : ℕ} {t : ℝ}

/-- A color actually seen in a word has a positive literal occupation count. -/
theorem occupation_pos_at (η : LabelVector J N) (i : Fin N) :
    0 < occupation η (η i) := by
  classical
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩

/-- Deleting zero-count colors and retaining at most one color leaves one
actual word; the proof also handles the empty-particle configuration. -/
theorem fibre_subsingleton_of_one_colour (m : OccupationState J N t) (a₀ : MeshIndex J)
    (honly : ∀ a, 0 < m.val a → a = a₀) : Subsingleton (Fibre m) := by
  constructor
  intro η ζ
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have hη : occupation η.val.val = m.val := congrArg Subtype.val η.property
  have hζ : occupation ζ.val.val = m.val := congrArg Subtype.val ζ.property
  have hpη := occupation_pos_at η.val.val i
  have hpζ := occupation_pos_at ζ.val.val i
  rw [hη] at hpη
  rw [hζ] at hpζ
  exact (honly _ hpη).trans (honly _ hpζ).symm

/-- Exact agreement with the frozen source uniform-fibre entropy. -/
theorem entropy_on_actual_fibre (F : LabelState J N t → ℝ) (m : OccupationState J N t) :
    uniformEntropy (fun η : Fibre m => F η.val) = uniformFibreEntropy F m := rfl

/-- The singleton ordinary-entropy endpoint, without evaluating an empty
minimum of positive counts or invoking any logarithmic Sobolev premise. -/
theorem uniformFibreEntropy_one_colour (F : LabelState J N t → ℝ)
    (m : OccupationState J N t) (a₀ : MeshIndex J)
    (honly : ∀ a, 0 < m.val a → a = a₀) : uniformFibreEntropy F m = 0 := by
  let : Subsingleton (Fibre m) := fibre_subsingleton_of_one_colour m a₀ honly
  let ξ : Fibre m := ⟨labelOfState m, profile_labelOfState m⟩
  let : Nonempty (Fibre m) := ⟨ξ⟩
  have he : (fun η : Fibre m => F η.val) = fun _ => F ξ.val :=
    funext fun η => congrArg (fun ζ : Fibre m => F ζ.val) (Subsingleton.elim η ξ)
  rw [← entropy_on_actual_fibre, he, uniformEntropy_const]


/-! The two-point scalar input is reproved here. The formulas follow the
Lee--Yau Lemma 2 calculus route checked in the separate v105 review.
At equal weights the sharp coefficient is defined by its genuine limit,
not by totalized division of the off-diagonal formula. -/
section BinaryCalculus
open Set Filter
open scoped Topology

def binaryMass (p a : ℝ) : ℝ := p*a^2+(1-p)
def binaryH (p a : ℝ) : ℝ := p*a^2*Real.log (a^2)-binaryMass p a*Real.log (binaryMass p a)
def binaryHp (p a : ℝ) : ℝ := 2*p*a*(2*Real.log a-Real.log (binaryMass p a))
def binaryK (p a : ℝ) : ℝ := (p*a+(1-p))*Real.log (binaryMass p a)-2*p*a*Real.log a
def binaryKp (p a : ℝ) : ℝ := p*Real.log (binaryMass p a)-2*p*Real.log a+
  2*p*(1-p)*(a-1)/binaryMass p a
def binaryKpp (p a : ℝ) : ℝ := 2*p*(1-p)*(a-1)*((1-p)-p*a^2)/(a*(binaryMass p a)^2)

theorem binaryMass_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (a : ℝ) :
    0 < binaryMass p a := by
  unfold binaryMass
  have h := mul_nonneg hp (sq_nonneg a)
  linarith

theorem hasDerivAt_binaryMass (p a : ℝ) : HasDerivAt (binaryMass p) (2*p*a) a := by
  convert (((hasDerivAt_id a).pow 2).const_mul p).add_const (1-p) using 1 <;>
    first | rfl | (dsimp; ring)

theorem hasDerivAt_binaryH {p a : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (ha : 0 < a) :
    HasDerivAt (binaryH p) (binaryHp p a) a := by
  have hsq : HasDerivAt (fun x : ℝ => x^2) (2*a) a := by
    convert (hasDerivAt_id a).pow 2 using 1 <;> first | rfl | (dsimp; ring)
  have hlog : HasDerivAt (fun x : ℝ => x*Real.log x) (Real.log (a^2)+1) (a^2) :=
    Real.hasDerivAt_mul_log (pow_ne_zero 2 ha.ne')
  have h₁ := (hlog.comp (h := fun x : ℝ => x^2) a hsq).const_mul p
  have h₂ := (Real.hasDerivAt_mul_log (binaryMass_pos hp hp1 a).ne').comp a
    (hasDerivAt_binaryMass p a)
  convert h₁.sub h₂ using 1
  · funext x
    dsimp only [binaryH, Pi.sub_apply, Function.comp_apply]
    ring
  · dsimp only [binaryHp, id_eq]
    rw [Real.log_pow]
    norm_num
    ring

theorem hasDerivAt_binaryK {p a : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (ha : 0 < a) :
    HasDerivAt (binaryK p) (binaryKp p a) a := by
  have hS := binaryMass_pos hp hp1 a
  have h₁ := (((hasDerivAt_id a).const_mul p).add_const (1-p)).mul
    ((hasDerivAt_binaryMass p a).log hS.ne')
  have h₂ := ((hasDerivAt_id a).const_mul (2*p)).mul
    ((hasDerivAt_id a).log ha.ne')
  convert h₁.sub h₂ using 1
  · rfl
  · dsimp only [binaryKp, id_eq]
    field_simp [ha.ne', hS.ne']
    dsimp only [binaryMass]
    ring

theorem hasDerivAt_binaryKp {p a : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (ha : 0 < a) :
    HasDerivAt (binaryKp p) (binaryKpp p a) a := by
  have hS := binaryMass_pos hp hp1 a
  have h₁ := ((hasDerivAt_binaryMass p a).log hS.ne').const_mul p
  have h₂ := ((hasDerivAt_id a).log ha.ne').const_mul (2*p)
  have h₃ := (((hasDerivAt_id a).sub_const 1).const_mul (2*p*(1-p))).div
    (hasDerivAt_binaryMass p a) hS.ne'
  convert (h₁.sub h₂).add h₃ using 1
  · rfl
  · dsimp only [binaryKpp, id_eq]
    field_simp [ha.ne', hS.ne']
    dsimp only [binaryMass]
    ring

/-- The derivative whose sign locates the sharp binary entropy quotient. -/
theorem hasDerivAt_binaryQuotient {p a : ℝ} (hp : 0 ≤ p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a ≠ 1) :
    HasDerivAt (fun x => binaryH p x/(x-1)^2) (2*binaryK p a/(a-1)^3) a := by
  have h := (hasDerivAt_binaryH hp hp1 ha).div
    (((hasDerivAt_id a).sub_const 1).pow 2) (pow_ne_zero 2 (sub_ne_zero.mpr ha1))
  convert h using 1
  · rfl
  · dsimp only [binaryHp, binaryH, binaryK, Pi.pow_apply, id_eq]
    rw [Real.log_pow]
    norm_num
    field_simp [sub_ne_zero.mpr ha1]
    dsimp only [binaryMass]
    ring

@[simp] theorem binaryMass_one (p : ℝ) : binaryMass p 1 = 1 := by
  unfold binaryMass
  ring

@[simp] theorem binaryH_one (p : ℝ) : binaryH p 1 = 0 := by
  simp only [binaryH, binaryMass_one, one_pow, Real.log_one, mul_zero, sub_self]

@[simp] theorem binaryHp_one (p : ℝ) : binaryHp p 1 = 0 := by
  simp only [binaryHp, binaryMass_one, Real.log_one, mul_zero, sub_self]

@[simp] theorem binaryK_one (p : ℝ) : binaryK p 1 = 0 := by
  simp only [binaryK, binaryMass_one, Real.log_one, mul_zero, sub_self]

@[simp] theorem binaryKp_one (p : ℝ) : binaryKp p 1 = 0 := by
  simp only [binaryKp, binaryMass_one, Real.log_one, mul_zero, sub_self, zero_div, add_zero]

theorem binaryMass_ratio {p : ℝ} (hp : p ≠ 0) : binaryMass p ((1-p)/p) = (1-p)/p := by
  unfold binaryMass
  field_simp
  ring

theorem binaryK_ratio {p : ℝ} (hp : p ≠ 0) : binaryK p ((1-p)/p) = 0 := by
  unfold binaryK
  rw [binaryMass_ratio hp]
  field_simp
  ring


/-- The derivative needed at the removable quotient singularity. -/
def binaryHpp (p a : ℝ) : ℝ :=
  2*p*(2*Real.log a-Real.log (binaryMass p a))+
    2*p*a*(2/a-(2*p*a)/binaryMass p a)

theorem hasDerivAt_binaryHp {p a : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (ha : 0 < a) :
    HasDerivAt (binaryHp p) (binaryHpp p a) a := by
  have hS := binaryMass_pos hp hp1 a
  have hlog := (((hasDerivAt_id a).log ha.ne').const_mul 2).sub
    ((hasDerivAt_binaryMass p a).log hS.ne')
  convert ((hasDerivAt_id a).const_mul (2*p)).mul hlog using 1
  · rfl
  · dsimp only [binaryHpp, id_eq, Pi.sub_apply]
    ring

@[simp] theorem binaryHpp_one (p : ℝ) : binaryHpp p 1 = 4*p*(1-p) := by
  simp only [binaryHpp, binaryMass_one, Real.log_one, mul_zero, sub_self, div_one, zero_add]
  ring

theorem continuousAt_binaryHpp_one {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    ContinuousAt (binaryHpp p) 1 := by
  have hS := (hasDerivAt_binaryMass p 1).continuousAt
  have hlogS := hS.log (binaryMass_pos hp hp1 1).ne'
  have hlog : ContinuousAt (fun a : ℝ => Real.log a) 1 :=
    continuousAt_id.log (by norm_num)
  have hinv : ContinuousAt (fun a : ℝ => (2 : ℝ)/a) 1 :=
    continuousAt_const.div continuousAt_id (by norm_num)
  exact ((hlog.const_mul 2).sub hlogS).const_mul (2*p) |>.add
    (((continuousAt_id.const_mul (2*p)).mul
      (hinv.sub ((continuousAt_id.const_mul (2*p)).div hS (binaryMass_pos hp hp1 1).ne'))))

/-- A concave arc with nonnegative first endpoint and zero second endpoint
is nonnegative between them; this replaces a critical-point existence detour. -/
theorem concave_nonneg_between {K : ℝ → ℝ} {s r a : ℝ}
    (hK : ConcaveOn ℝ (Ici s) K) (hsr : s < r) (hs : 0 ≤ K s) (hr : K r = 0)
    (ha : s ≤ a) (har : a ≤ r) : 0 ≤ K a := by
  have hd : 0 < r-s := sub_pos.mpr hsr
  have hA : 0 ≤ (r-a)/(r-s) := div_nonneg (sub_nonneg.mpr har) hd.le
  have hB : 0 ≤ (a-s)/(r-s) := div_nonneg (sub_nonneg.mpr ha) hd.le
  have hsum : (r-a)/(r-s)+(a-s)/(r-s) = 1 := by field_simp; ring
  have harg : ((r-a)/(r-s))*s+((a-s)/(r-s))*r = a := by field_simp; ring
  have h := hK.2 (by simp : s ∈ Ici s) (by simpa only [mem_Ici] using hsr.le : r ∈ Ici s) hA hB hsum
  simp only [smul_eq_mul, harg, hr, mul_zero, add_zero] at h
  exact (mul_nonneg hA hs).trans h

/-- Concavity supplies the exact sign after the second zero as well. -/
theorem concave_nonpos_after {K : ℝ → ℝ} {s r a : ℝ}
    (hK : ConcaveOn ℝ (Ici s) K) (hsr : s < r) (hs : 0 ≤ K s) (hr : K r = 0)
    (ha : r ≤ a) : K a ≤ 0 := by
  have hsa : s < a := hsr.trans_le ha
  have hd : 0 < a-s := sub_pos.mpr hsa
  have hA : 0 ≤ (a-r)/(a-s) := div_nonneg (sub_nonneg.mpr ha) hd.le
  have hB : 0 < (r-s)/(a-s) := div_pos (sub_pos.mpr hsr) hd
  have hsum : (a-r)/(a-s)+(r-s)/(a-s) = 1 := by field_simp; ring
  have harg : ((a-r)/(a-s))*s+((r-s)/(a-s))*a = r := by field_simp; ring
  have h := hK.2 (by simp : s ∈ Ici s) (by simpa only [mem_Ici] using hsa.le : a ∈ Ici s) hA hB.le hsum
  simp only [smul_eq_mul, harg, hr] at h
  have hfirst := mul_nonneg hA hs
  by_contra hh
  have hlast := mul_pos hB (lt_of_not_ge hh)
  linarith only [h, hfirst, hlast]

/-- The square-root transition point is an actual positive root of q-p*a². -/
theorem binary_transition {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 1/2) :
    1 ≤ Real.sqrt ((1-p)/p) ∧
      p*(Real.sqrt ((1-p)/p))^2 = 1-p := by
  have hr : 1 ≤ (1-p)/p := (le_div_iff₀ hp).mpr (by linarith)
  have hs := Real.sq_sqrt (le_trans zero_le_one hr)
  constructor
  · have hn := Real.sqrt_nonneg ((1-p)/p)
    nlinarith only [hs, hr, hn]
  · rw [hs]
    field_simp

theorem binaryKpp_nonpos_left {p a : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1/2)
    (ha : 0 < a) (ha1 : a ≤ 1) : binaryKpp p a ≤ 0 := by
  have hq : 0 ≤ 1-p := by linarith
  have hsq : a^2 ≤ 1 := by nlinarith only [ha, ha1]
  have hmul := mul_le_mul_of_nonneg_left hsq hp
  have hlast : 0 ≤ (1-p)-p*a^2 := by linarith
  unfold binaryKpp
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr ha1)) hlast)
    (mul_nonneg ha.le (sq_nonneg _))


/-- The removable entropy quotient value, by two genuine applications of
l'Hopital. No quotient value at the totalized zero denominator is substituted. -/
theorem binaryQuotient_limit {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    Tendsto (fun a => binaryH p a/(a-1)^2) (𝓝[≠] (1 : ℝ)) (𝓝 (2*p*(1-p))) := by
  have hpos' : ∀ᶠ a in 𝓝 (1 : ℝ), 0 < a :=
    isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Ioi 0)
  have hpos : ∀ᶠ a in 𝓝[≠] (1 : ℝ), 0 < a :=
    hpos'.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ a in 𝓝[≠] (1 : ℝ), a ≠ 1 := eventually_mem_nhdsWithin
  have hHp : Tendsto (binaryHp p) (𝓝[≠] (1 : ℝ)) (𝓝 0) := by
    simpa only [binaryHp_one] using
      ((hasDerivAt_binaryHp hp hp1 (by norm_num : (0 : ℝ) < 1)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  have hH : Tendsto (binaryH p) (𝓝[≠] (1 : ℝ)) (𝓝 0) := by
    simpa only [binaryH_one] using
      ((hasDerivAt_binaryH hp hp1 (by norm_num : (0 : ℝ) < 1)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  have hd₁ (a : ℝ) : HasDerivAt (fun x : ℝ => 2*(x-1)) 2 a := by
    convert ((hasDerivAt_id a).sub_const 1).const_mul 2 using 1 <;> first | rfl | norm_num
  have hd₂ (a : ℝ) : HasDerivAt (fun x : ℝ => (x-1)^2) (2*(a-1)) a := by
    convert ((hasDerivAt_id a).sub_const 1).pow 2 using 1 <;> first | rfl | (dsimp; ring)
  have hden₁ : Tendsto (fun a : ℝ => 2*(a-1)) (𝓝[≠] (1 : ℝ)) (𝓝 0) := by
    simpa using (hd₁ 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hden₂ : Tendsto (fun a : ℝ => (a-1)^2) (𝓝[≠] (1 : ℝ)) (𝓝 0) := by
    simpa using (hd₂ 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hsecond : Tendsto (fun a => binaryHpp p a/2) (𝓝[≠] (1 : ℝ)) (𝓝 (2*p*(1-p))) := by
    have hh : Tendsto (fun a => binaryHpp p a/2) (𝓝[≠] (1 : ℝ))
        (𝓝 (binaryHpp p 1/2)) :=
      ((continuousAt_binaryHpp_one hp hp1).tendsto.div_const 2).mono_left nhdsWithin_le_nhds
    have he : binaryHpp p 1/2 = 2*p*(1-p) := by rw [binaryHpp_one]; ring
    simpa only [he] using hh
  have hfirst : Tendsto (fun a => binaryHp p a/(2*(a-1)))
      (𝓝[≠] (1 : ℝ)) (𝓝 (2*p*(1-p))) :=
    HasDerivAt.lhopital_zero_nhdsNE
      (hpos.mono fun a ha => hasDerivAt_binaryHp hp hp1 ha)
      (Eventually.of_forall hd₁) (Eventually.of_forall fun _ => by norm_num) hHp hden₁ hsecond
  exact HasDerivAt.lhopital_zero_nhdsNE
    (hpos.mono fun a ha => hasDerivAt_binaryH hp hp1 ha)
    (Eventually.of_forall hd₂)
    (hne.mono fun a ha => mul_ne_zero (by norm_num) (sub_ne_zero.mpr ha)) hH hden₂ hfirst

/-- The left-side K' sign is obtained from its actual second derivative. -/
theorem binaryKp_nonneg_left {p a : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1/2)
    (ha : 0 < a) (ha1 : a ≤ 1) : 0 ≤ binaryKp p a := by
  have hp1 : p < 1 := by linarith
  have hanti : AntitoneOn (binaryKp p) (Ioc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
    · intro x hx
      exact (hasDerivAt_binaryKp hp hp1 hx.1).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_binaryKp hp hp1 (interior_subset hx).1).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hasDerivAt_binaryKp hp hp1 (interior_subset hx).1).deriv]
      exact binaryKpp_nonpos_left hp hp2 (interior_subset hx).1 (interior_subset hx).2
  have hh := hanti (show a ∈ Ioc (0 : ℝ) 1 from ⟨ha, ha1⟩)
    (show (1 : ℝ) ∈ Ioc (0 : ℝ) 1 from ⟨zero_lt_one, le_rfl⟩) ha1
  simpa only [binaryKp_one] using hh

theorem binaryK_nonpos_left {p a : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1/2)
    (ha : 0 < a) (ha1 : a ≤ 1) : binaryK p a ≤ 0 := by
  have hp1 : p < 1 := by linarith
  have hmono : MonotoneOn (binaryK p) (Ioc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
    · intro x hx
      exact (hasDerivAt_binaryK hp hp1 hx.1).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_binaryK hp hp1 (interior_subset hx).1).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hasDerivAt_binaryK hp hp1 (interior_subset hx).1).deriv]
      exact binaryKp_nonneg_left hp hp2 (interior_subset hx).1 (interior_subset hx).2
  have hh := hmono (show a ∈ Ioc (0 : ℝ) 1 from ⟨ha, ha1⟩)
    (show (1 : ℝ) ∈ Ioc (0 : ℝ) 1 from ⟨zero_lt_one, le_rfl⟩) ha1
  simpa only [binaryK_one] using hh


theorem binaryKpp_nonneg_middle {p a : ℝ} (hp : 0 < p) (hp2 : p ≤ 1/2)
    (ha : 1 ≤ a) (has : a ≤ Real.sqrt ((1-p)/p)) : 0 ≤ binaryKpp p a := by
  have hq : 0 ≤ 1-p := by linarith
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hsq : p*a^2 ≤ p*(Real.sqrt ((1-p)/p))^2 := by gcongr
  rw [(binary_transition hp hp2).2] at hsq
  unfold binaryKpp
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr ha))
    (sub_nonneg.mpr hsq)) (mul_nonneg (by linarith) (sq_nonneg _))

theorem binaryKpp_nonpos_right {p a : ℝ} (hp : 0 < p) (hp2 : p ≤ 1/2)
    (has : Real.sqrt ((1-p)/p) ≤ a) : binaryKpp p a ≤ 0 := by
  have hs := binary_transition hp hp2
  have ha : 1 ≤ a := hs.1.trans has
  have hq : 0 ≤ 1-p := by linarith
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hsq : p*(Real.sqrt ((1-p)/p))^2 ≤ p*a^2 := by gcongr
  rw [hs.2] at hsq
  unfold binaryKpp
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) (sub_nonneg.mpr ha))
      (sub_nonpos.mpr hsq)) (mul_nonneg (by linarith) (sq_nonneg _))

theorem binaryKp_nonneg_middle {p a : ℝ} (hp : 0 < p) (hp2 : p ≤ 1/2)
    (ha : 1 ≤ a) (has : a ≤ Real.sqrt ((1-p)/p)) : 0 ≤ binaryKp p a := by
  have hp1 : p < 1 := by linarith
  have hs := (binary_transition hp hp2).1
  have hmono : MonotoneOn (binaryKp p) (Icc 1 (Real.sqrt ((1-p)/p))) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx
      exact (hasDerivAt_binaryKp hp.le hp1 (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_binaryKp hp.le hp1
        (by linarith [(interior_subset hx).1])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hasDerivAt_binaryKp hp.le hp1 (by linarith [(interior_subset hx).1])).deriv]
      exact binaryKpp_nonneg_middle hp hp2 (interior_subset hx).1 (interior_subset hx).2
  have hh := hmono (show (1 : ℝ) ∈ Icc 1 (Real.sqrt ((1-p)/p)) from ⟨le_rfl, hs⟩)
    (show a ∈ Icc 1 (Real.sqrt ((1-p)/p)) from ⟨ha, has⟩) ha
  simpa only [binaryKp_one] using hh

theorem binaryK_nonneg_middle {p a : ℝ} (hp : 0 < p) (hp2 : p ≤ 1/2)
    (ha : 1 ≤ a) (has : a ≤ Real.sqrt ((1-p)/p)) : 0 ≤ binaryK p a := by
  have hp1 : p < 1 := by linarith
  have hs := (binary_transition hp hp2).1
  have hmono : MonotoneOn (binaryK p) (Icc 1 (Real.sqrt ((1-p)/p))) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx
      exact (hasDerivAt_binaryK hp.le hp1 (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_binaryK hp.le hp1
        (by linarith [(interior_subset hx).1])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hasDerivAt_binaryK hp.le hp1 (by linarith [(interior_subset hx).1])).deriv]
      exact binaryKp_nonneg_middle hp hp2 (interior_subset hx).1 (interior_subset hx).2
  have hh := hmono (show (1 : ℝ) ∈ Icc 1 (Real.sqrt ((1-p)/p)) from ⟨le_rfl, hs⟩)
    (show a ∈ Icc 1 (Real.sqrt ((1-p)/p)) from ⟨ha, has⟩) ha
  simpa only [binaryK_one] using hh

theorem binaryK_concave_right {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 1/2) :
    ConcaveOn ℝ (Ici (Real.sqrt ((1-p)/p))) (binaryK p) := by
  have hp1 : p < 1 := by linarith
  have hs := (binary_transition hp hp2).1
  have hpos (x : ℝ) (hx : x ∈ Ici (Real.sqrt ((1-p)/p))) : 0 < x := by
    have hh : Real.sqrt ((1-p)/p) ≤ x := by simpa only [mem_Ici] using hx
    linarith
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_binaryK hp.le hp1 (hpos x hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_binaryK hp.le hp1 (hpos x (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_binaryKp hp.le hp1 (hpos x (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact binaryKpp_nonpos_right hp hp2 (by simpa only [mem_Ici] using interior_subset hx)

/-- The complete unbalanced sign pattern follows from actual derivatives
and concavity; there is no assumed location or uniqueness of a critical point. -/
theorem binaryK_unbalanced_signs {p : ℝ} (hp : 0 < p) (hp2 : p < 1/2) :
    (∀ a, 1 ≤ a → a ≤ (1-p)/p → 0 ≤ binaryK p a) ∧
      (∀ a, (1-p)/p ≤ a → binaryK p a ≤ 0) := by
  have hr : 1 < (1-p)/p := (lt_div_iff₀ hp).mpr (by linarith)
  have hsq := Real.sq_sqrt (le_trans zero_le_one hr.le)
  have hs := Real.sqrt_nonneg ((1-p)/p)
  have hs1 : 1 < Real.sqrt ((1-p)/p) := by nlinarith only [hr, hsq, hs]
  have hsr : Real.sqrt ((1-p)/p) < (1-p)/p := by nlinarith only [hs1, hsq]
  have hKs := binaryK_nonneg_middle hp hp2.le hs1.le le_rfl
  have hKr := binaryK_ratio hp.ne'
  have hc := binaryK_concave_right hp hp2.le
  constructor
  · intro a ha har
    by_cases has : a ≤ Real.sqrt ((1-p)/p)
    · exact binaryK_nonneg_middle hp hp2.le ha has
    · exact concave_nonneg_between hc hsr hKs hKr (le_of_not_ge has) har
  · intro a ha
    exact concave_nonpos_after hc hsr hKs hKr ha

/-- At equal weights K is nonpositive on both sides of one. The distinct
balanced analysis is necessary because the unbalanced ratio equals one. -/
theorem binaryK_balanced_nonpos {a : ℝ} (ha : 0 < a) : binaryK (1/2) a ≤ 0 := by
  by_cases ha1 : a ≤ 1
  · exact binaryK_nonpos_left (by norm_num) le_rfl ha ha1
  have ha1' : 1 ≤ a := le_of_not_ge ha1
  have hs : Real.sqrt ((1-(1/2 : ℝ))/(1/2)) = 1 := by norm_num
  have hpos (x : ℝ) (hx : x ∈ Ici (1 : ℝ)) : 0 < x := by
    have hh : 1 ≤ x := by simpa only [mem_Ici] using hx
    linarith
  have hpanti : AntitoneOn (binaryKp (1/2)) (Ici (1 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
    · intro x hx
      exact (hasDerivAt_binaryKp (by norm_num) (by norm_num)
        (hpos x hx)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_binaryKp (by norm_num) (by norm_num)
        (hpos x (interior_subset hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hasDerivAt_binaryKp (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
        (hpos x (interior_subset hx))).deriv]
      apply binaryKpp_nonpos_right (by norm_num) le_rfl
      simpa only [hs, mem_Ici] using (interior_subset hx)
  have hkp (x : ℝ) (hx : 1 ≤ x) : binaryKp (1/2) x ≤ 0 := by
    have hh := hpanti (by simp : (1 : ℝ) ∈ Ici 1) hx hx
    simpa only [binaryKp_one] using hh
  have hanti : AntitoneOn (binaryK (1/2)) (Ici (1 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
    · intro x hx
      exact (hasDerivAt_binaryK (by norm_num) (by norm_num)
        (hpos x hx)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_binaryK (by norm_num) (by norm_num)
        (hpos x (interior_subset hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hasDerivAt_binaryK (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
        (hpos x (interior_subset hx))).deriv]
      exact hkp x (by simpa only [mem_Ici] using interior_subset hx)
  have hh := hanti (by simp : (1 : ℝ) ∈ Ici 1) ha1' ha1'
  simpa only [binaryK_one] using hh


/-- The entropy quotient increases up to its removable point from the left. -/
theorem binaryQuotient_mono_left {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1/2) :
    MonotoneOn (fun a => binaryH p a/(a-1)^2) (Ioo (0 : ℝ) 1) := by
  have hp1 : p < 1 := by linarith
  have hd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :=
    hasDerivAt_binaryQuotient hp hp1 hx.1 (ne_of_lt hx.2)
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hh := interior_subset hx
    rw [(hd x hh).deriv]
    apply div_nonneg_of_nonpos
    · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
        (binaryK_nonpos_left hp hp2 hh.1 hh.2.le)
    · have he : (x-1)^3 = (x-1)^2*(x-1) := by ring
      rw [he]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith [hh.2])

theorem binaryQuotient_mono_middle {p : ℝ} (hp : 0 < p) (hp2 : p < 1/2) :
    MonotoneOn (fun a => binaryH p a/(a-1)^2) (Ioc 1 ((1-p)/p)) := by
  have hp1 : p < 1 := by linarith
  have hd (x : ℝ) (hx : x ∈ Ioc 1 ((1-p)/p)) :=
    hasDerivAt_binaryQuotient hp.le hp1 (by linarith [hx.1]) (ne_of_gt hx.1)
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 1 ((1-p)/p))
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hh := interior_subset hx
    rw [(hd x hh).deriv]
    apply div_nonneg
    · exact mul_nonneg (by norm_num) ((binaryK_unbalanced_signs hp hp2).1 x hh.1.le hh.2)
    · exact pow_nonneg (sub_nonneg.mpr hh.1.le) 3

theorem binaryQuotient_anti_right {p : ℝ} (hp : 0 < p) (hp2 : p < 1/2) :
    AntitoneOn (fun a => binaryH p a/(a-1)^2) (Ici ((1-p)/p)) := by
  have hp1 : p < 1 := by linarith
  have hr : 1 < (1-p)/p := (lt_div_iff₀ hp).mpr (by linarith)
  have hgt (x : ℝ) (hx : x ∈ Ici ((1-p)/p)) : 1 < x := by
    have hh : (1-p)/p ≤ x := by simpa only [mem_Ici] using hx
    linarith
  have hd (x : ℝ) (hx : x ∈ Ici ((1-p)/p)) :=
    hasDerivAt_binaryQuotient hp.le hp1 (by linarith [hgt x hx]) (ne_of_gt (hgt x hx))
  apply antitoneOn_of_deriv_nonpos (convex_Ici ((1-p)/p))
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hh := interior_subset hx
    have hx1 := hgt x hh
    rw [(hd x hh).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
        ((binaryK_unbalanced_signs hp hp2).2 x (by simpa only [mem_Ici] using hh))
    · positivity

theorem binaryQuotient_anti_balanced :
    AntitoneOn (fun a => binaryH (1/2) a/(a-1)^2) (Ioi (1 : ℝ)) := by
  have hd (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :=
    hasDerivAt_binaryQuotient (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
      (by linarith [show 1 < x from hx]) (ne_of_gt hx)
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 1)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hh : 1 < x := interior_subset hx
    rw [(hd x hh).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
        (binaryK_balanced_nonpos (by linarith))
    · positivity

/-- The limiting value controls the whole interval to the left of one. -/
theorem binaryQuotient_le_limit {p a : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1/2)
    (ha : 0 < a) (ha1 : a < 1) : binaryH p a/(a-1)^2 ≤ 2*p*(1-p) := by
  have hlim : Tendsto (fun x => binaryH p x/(x-1)^2) (𝓝[<] (1 : ℝ))
      (𝓝 (2*p*(1-p))) := (binaryQuotient_limit hp (by linarith)).mono_left
        (nhdsWithin_mono 1 (fun x hx => ne_of_lt hx))
  have hgt' : ∀ᶠ x in 𝓝 (1 : ℝ), a < x := isOpen_Ioi.mem_nhds ha1
  have hgt : ∀ᶠ x in 𝓝[<] (1 : ℝ), a < x := hgt'.filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ x in 𝓝[<] (1 : ℝ), x < 1 := eventually_mem_nhdsWithin
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [hgt, hlt] with x hax hx1
  exact binaryQuotient_mono_left hp hp2 ⟨ha, ha1⟩ ⟨ha.trans hax, hx1⟩ hax.le

/-- The right-side limiting value is below the actual unbalanced maximum. -/
theorem binaryQuotient_limit_le_ratio {p : ℝ} (hp : 0 < p) (hp2 : p < 1/2) :
    2*p*(1-p) ≤ binaryH p ((1-p)/p)/((1-p)/p-1)^2 := by
  have hr : 1 < (1-p)/p := (lt_div_iff₀ hp).mpr (by linarith)
  have hlim : Tendsto (fun x => binaryH p x/(x-1)^2) (𝓝[>] (1 : ℝ))
      (𝓝 (2*p*(1-p))) := (binaryQuotient_limit hp.le (by linarith)).mono_left
        (nhdsWithin_mono 1 (fun x hx => ne_of_gt hx))
  have hlt' : ∀ᶠ x in 𝓝 (1 : ℝ), x < (1-p)/p := isOpen_Iio.mem_nhds hr
  have hlt : ∀ᶠ x in 𝓝[>] (1 : ℝ), x < (1-p)/p := hlt'.filter_mono nhdsWithin_le_nhds
  have hgt : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x := eventually_mem_nhdsWithin
  apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
  filter_upwards [hlt, hgt] with x hxr hx1
  exact binaryQuotient_mono_middle hp hp2 ⟨hx1, hxr.le⟩ ⟨hr, le_rfl⟩ hxr.le

/-- The global quotient maximum is attained at the unequal-weight ratio. -/
theorem binaryQuotient_le_ratio {p a : ℝ} (hp : 0 < p) (hp2 : p < 1/2)
    (ha : 0 < a) (ha1 : a ≠ 1) :
    binaryH p a/(a-1)^2 ≤ binaryH p ((1-p)/p)/((1-p)/p-1)^2 := by
  have hr : 1 < (1-p)/p := (lt_div_iff₀ hp).mpr (by linarith)
  by_cases haL : a < 1
  · exact (binaryQuotient_le_limit hp.le hp2.le ha haL).trans
      (binaryQuotient_limit_le_ratio hp hp2)
  have haR : 1 < a := lt_of_le_of_ne (le_of_not_gt haL) (Ne.symm ha1)
  by_cases har : a ≤ (1-p)/p
  · exact binaryQuotient_mono_middle hp hp2 ⟨haR, har⟩ ⟨hr, le_rfl⟩ har
  · exact binaryQuotient_anti_right hp hp2 (by simp) (le_of_not_ge har) (le_of_not_ge har)

/-- At equal weights the true removable value, not the totalized quotient at
one, is the maximum. -/
theorem binaryQuotient_le_balanced {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    binaryH (1/2) a/(a-1)^2 ≤ 1/2 := by
  by_cases haL : a < 1
  · have hh := binaryQuotient_le_limit (by norm_num : (0 : ℝ) ≤ 1/2) le_rfl ha haL
    norm_num at hh ⊢
    exact hh
  have haR : 1 < a := lt_of_le_of_ne (le_of_not_gt haL) (Ne.symm ha1)
  have hlim : Tendsto (fun x => binaryH (1/2) x/(x-1)^2) (𝓝[>] (1 : ℝ)) (𝓝 (1/2)) := by
    have hh : Tendsto (fun x => binaryH (1/2) x/(x-1)^2) (𝓝[>] (1 : ℝ))
        (𝓝 (2*(1/2)*(1-(1/2)))) :=
      (binaryQuotient_limit (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)).mono_left
        (nhdsWithin_mono 1 (fun x hx => ne_of_gt hx))
    norm_num at hh ⊢
    exact hh
  have hlt' : ∀ᶠ x in 𝓝 (1 : ℝ), x < a := isOpen_Iio.mem_nhds haR
  have hlt : ∀ᶠ x in 𝓝[>] (1 : ℝ), x < a := hlt'.filter_mono nhdsWithin_le_nhds
  have hgt : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x := eventually_mem_nhdsWithin
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [hlt, hgt] with x hxa hx1
  exact binaryQuotient_anti_balanced hx1 haR hxa.le


/-- Evaluation at the genuine unequal-weight maximizer. -/
theorem binaryQuotient_ratio_value {p : ℝ} (hp : 0 < p) (hp2 : p < 1/2) :
    binaryH p ((1-p)/p)/((1-p)/p-1)^2 =
      p*(1-p)*Real.log ((1-p)/p)/(1-2*p) := by
  have hd : 1-2*p ≠ 0 := by linarith
  have hr : 1 < (1-p)/p := (lt_div_iff₀ hp).mpr (by linarith)
  apply (div_eq_iff (pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt hr)))).mpr
  have he : (1-p)/p-1 = (1-2*p)/p := by field_simp; ring
  unfold binaryH
  rw [binaryMass_ratio hp.ne', Real.log_pow, he, div_pow]
  norm_num
  field_simp [hp.ne', hd]
  ring

/-- Sharp coefficient relative to the unweighted squared difference. -/
def binarySharp (p : ℝ) : ℝ :=
  if p = 1/2 then 1/2 else p*(1-p)*Real.log ((1-p)/p)/(1-2*p)

theorem binaryH_le_sharp_pos {p a : ℝ} (hp : 0 < p) (hp2 : p ≤ 1/2)
    (ha : 0 < a) : binaryH p a ≤ binarySharp p*(a-1)^2 := by
  by_cases ha1 : a = 1
  · subst a
    simp only [binaryH_one, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, le_refl]
  have hs : 0 < (a-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr ha1)
  apply (div_le_iff₀ hs).mp
  by_cases hpE : p = 1/2
  · subst p
    simpa only [binarySharp, ite_eq_left] using binaryQuotient_le_balanced ha ha1
  · have hplt : p < 1/2 := lt_of_le_of_ne hp2 hpE
    simpa only [binaryQuotient_ratio_value hp hplt, binarySharp, ite_eq_right hpE]
      using binaryQuotient_le_ratio hp hplt ha ha1

theorem continuous_binaryH (p : ℝ) : Continuous (binaryH p) := by
  have h₁ := (Real.continuous_mul_log.comp (continuous_id.pow 2)).const_mul p
  have hS : Continuous (fun a : ℝ => p*a^2+(1-p)) :=
    ((continuous_id.pow 2).const_mul p).add continuous_const
  have h₂ := Real.continuous_mul_log.comp hS
  convert h₁.sub h₂ using 1
  funext a
  dsimp only [binaryH, binaryMass, Pi.sub_apply, Pi.pow_apply, Function.comp_apply, id_eq]
  ring

/-- Zero input is obtained from continuity of x log x, including its actual
value at zero; positivity is not imposed on the final normalized input. -/
theorem binaryH_le_sharp {p a : ℝ} (hp : 0 < p) (hp2 : p ≤ 1/2)
    (ha : 0 ≤ a) : binaryH p a ≤ binarySharp p*(a-1)^2 := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst a
    have hleft : Tendsto (binaryH p) (𝓝[>] (0 : ℝ)) (𝓝 (binaryH p 0)) :=
      (continuous_binaryH p).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hright : Tendsto (fun x : ℝ => binarySharp p*(x-1)^2) (𝓝[>] (0 : ℝ))
        (𝓝 (binarySharp p*(0-1)^2)) :=
      ((((continuous_id.sub continuous_const).pow 2).const_mul (binarySharp p)).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto hleft hright
    have he : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := eventually_mem_nhdsWithin
    exact he.mono fun x hx => binaryH_le_sharp_pos hp hp2 hx
  · exact binaryH_le_sharp_pos hp hp2 hpos


/-- Scalar comparison used to obtain the exact Lee--Yau universal coefficient. -/
def logComparison (u : ℝ) : ℝ :=
  u*(2-Real.log (1-u^2))-Real.log (1+u)+Real.log (1-u)

theorem hasDerivAt_logComparison {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    HasDerivAt logComparison (-Real.log (1-u^2)) u := by
  have hm : 0 < 1-u := by linarith
  have hp : 0 < 1+u := by linarith
  have hs : 0 < 1-u^2 := by nlinarith
  have hsq : HasDerivAt (fun x : ℝ => 1-x^2) (-2*u) u := by
    convert ((hasDerivAt_id u).pow 2).const_sub 1 using 1 <;> first | rfl | (dsimp; ring)
  have h₁ := (hasDerivAt_id u).mul ((hsq.log hs.ne').const_sub 2)
  have h₂ := (((hasDerivAt_id u).const_add 1).log hp.ne')
  have h₃ := (((hasDerivAt_id u).const_sub 1).log hm.ne')
  convert (h₁.sub h₂).add h₃ using 1
  · rfl
  · dsimp only [id_eq]
    field_simp [hm.ne', hp.ne', hs.ne']
    ring

theorem logComparison_nonneg {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    0 ≤ logComparison u := by
  have hmono : MonotoneOn logComparison (Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro x hx
      exact (hasDerivAt_logComparison hx.1 hx.2).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_logComparison (interior_subset hx).1
        (interior_subset hx).2).differentiableAt.differentiableWithinAt
    · intro x hx
      have hh := interior_subset hx
      rw [(hasDerivAt_logComparison hh.1 hh.2).deriv]
      have hs : 0 < 1-x^2 := by nlinarith only [hh.1, hh.2]
      have hl := Real.log_le_sub_one_of_pos hs
      nlinarith only [hl, sq_nonneg x]
  have hh := hmono (show (0 : ℝ) ∈ Ico 0 1 by norm_num) ⟨hu, hu1⟩ hu
  simpa only [logComparison, zero_mul, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    Real.log_one, sub_self] using hh

/-- The sharper elementary logarithmic comparison, before replacing its
universal constant by the exact 1/log(2) used in the cited proof. -/
theorem log_ratio_le {p : ℝ} (hp : 0 < p) (hp2 : p < 1/2) :
    Real.log ((1-p)/p)/(1-2*p) ≤ 2-Real.log (4*p*(1-p)) := by
  have hq : 0 < 1-p := by linarith
  have hu : 0 ≤ 1-2*p := by linarith
  have hu1 : 1-2*p < 1 := by linarith
  have hh := logComparison_nonneg hu hu1
  unfold logComparison at hh
  have he₁ : 1-(1-2*p)^2 = 4*p*(1-p) := by ring
  have he₂ : 1+(1-2*p) = 2*(1-p) := by ring
  have he₃ : 1-(1-2*p) = 2*p := by ring
  have hl₂ : Real.log (2*(1-p)) = Real.log 2+Real.log (1-p) :=
    Real.log_mul (by norm_num) hq.ne'
  have hl₃ : Real.log (2*p) = Real.log 2+Real.log p :=
    Real.log_mul (by norm_num) hp.ne'
  rw [he₁, he₂, he₃, hl₂, hl₃] at hh
  apply (div_le_iff₀ (by linarith : 0 < 1-2*p)).mpr
  rw [Real.log_div hq.ne' hp.ne']
  nlinarith only [hh]

/-- Exact universal binary constant comparison, including equal weights. -/
theorem binarySharp_le_universal {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 1/2) :
    binarySharp p ≤ -(p*(1-p))*Real.log (p*(1-p))/Real.log 2 := by
  have hq : 0 < 1-p := by linarith
  have hpq : 0 < p*(1-p) := mul_pos hp hq
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2le : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h4 : Real.log (4*p*(1-p)) = 2*Real.log 2+Real.log (p*(1-p)) := by
    rw [show 4*p*(1-p) = 2^2*(p*(1-p)) by ring,
      Real.log_mul (by norm_num) hpq.ne', Real.log_pow]
    norm_num
  have hz : 0 ≤ -Real.log (4*p*(1-p)) := by
    have hpos : 0 < 4*p*(1-p) := by positivity
    have hh := Real.log_le_sub_one_of_pos hpos
    nlinarith [sq_nonneg (2*p-1)]
  have hbase : binarySharp p ≤ p*(1-p)*(2-Real.log (4*p*(1-p))) := by
    by_cases he : p = 1/2
    · subst p
      norm_num [binarySharp]
    · have hlt : p < 1/2 := lt_of_le_of_ne hp2 he
      have hh := mul_le_mul_of_nonneg_left (log_ratio_le hp hlt) hpq.le
      simpa only [binarySharp, ite_eq_right he, mul_div_assoc] using hh
  apply hbase.trans
  apply (le_div_iff₀ h2).mpr
  have hh := mul_nonneg hz (sub_nonneg.mpr h2le)
  have hh' := mul_nonneg hpq.le hh
  rw [h4] at hh'
  rw [h4]
  nlinarith only [hh']


/-- Ordinary two-point square-root entropy, with zero-log-zero totalization. -/
def binaryEntropy (p a b : ℝ) : ℝ :=
  p*a^2*Real.log (a^2)+(1-p)*b^2*Real.log (b^2)-
    (p*a^2+(1-p)*b^2)*Real.log (p*a^2+(1-p)*b^2)

theorem binaryEntropy_scale {p a b : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 ≤ a) (hb : 0 < b) :
    binaryEntropy p a b = b^2*binaryH p (a/b) := by
  have hq : 0 < 1-p := by linarith
  have hb₂ : b^2 ≠ 0 := pow_ne_zero 2 hb.ne'
  have hS : 0 < p*a^2+(1-p)*b^2 := by positivity
  have he : binaryMass p (a/b) = (p*a^2+(1-p)*b^2)/b^2 := by
    unfold binaryMass
    field_simp
  unfold binaryEntropy binaryH
  rw [he, div_pow, Real.log_div hS.ne' hb₂]
  rcases eq_or_lt_of_le ha with heq | ha
  · subst a
    simp only [zero_pow (by decide : 2 ≠ 0), zero_div, mul_zero, zero_mul, zero_add]
    rw [Real.log_mul hq.ne' hb₂]
    field_simp
    ring
  · rw [Real.log_div (pow_ne_zero 2 ha.ne') hb₂]
    field_simp
    ring

theorem binaryEntropy_le_half_pos {p a b : ℝ} (hp : 0 < p) (hp2 : p ≤ 1/2)
    (ha : 0 ≤ a) (hb : 0 < b) :
    binaryEntropy p a b ≤ -(p*(1-p))*Real.log (p*(1-p))/Real.log 2*(a-b)^2 := by
  rw [binaryEntropy_scale hp (by linarith) ha hb]
  have hh := mul_le_mul_of_nonneg_left (binaryH_le_sharp hp hp2 (div_nonneg ha hb.le))
    (sq_nonneg b)
  have he : b^2*(binarySharp p*(a/b-1)^2) = binarySharp p*(a-b)^2 := by
    field_simp
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (binarySharp_le_universal hp hp2) (sq_nonneg _))

theorem continuous_binaryEntropy_right (p a : ℝ) : Continuous (binaryEntropy p a) := by
  have h₁ : Continuous (fun b : ℝ => (1-p)*(b^2*Real.log (b^2))) :=
    (Real.continuous_mul_log.comp (continuous_id.pow 2)).const_mul (1-p)
  have hS : Continuous (fun b : ℝ => p*a^2+(1-p)*b^2) :=
    continuous_const.add ((continuous_id.pow 2).const_mul (1-p))
  have h₂ := Real.continuous_mul_log.comp hS
  have hh := (h₁.const_add (p*a^2*Real.log (a^2))).sub h₂
  convert hh using 1
  funext b
  dsimp only [binaryEntropy, Pi.sub_apply, Function.comp_apply]
  ring

/-- Both zero-input faces are retained in the half-weight reduction. -/
theorem binaryEntropy_le_half {p a b : ℝ} (hp : 0 < p) (hp2 : p ≤ 1/2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    binaryEntropy p a b ≤ -(p*(1-p))*Real.log (p*(1-p))/Real.log 2*(a-b)^2 := by
  rcases eq_or_lt_of_le hb with heq | hb
  · subst b
    have hleft : Tendsto (binaryEntropy p a) (𝓝[>] (0 : ℝ)) (𝓝 (binaryEntropy p a 0)) :=
      (continuous_binaryEntropy_right p a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hc : Continuous (fun b : ℝ =>
        -(p*(1-p))*Real.log (p*(1-p))/Real.log 2*(a-b)^2) :=
      ((continuous_const.sub continuous_id).pow 2).const_mul _
    have hright : Tendsto (fun b : ℝ =>
        -(p*(1-p))*Real.log (p*(1-p))/Real.log 2*(a-b)^2) (𝓝[>] (0 : ℝ))
        (𝓝 (-(p*(1-p))*Real.log (p*(1-p))/Real.log 2*(a-0)^2)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto hleft hright
    have he : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := eventually_mem_nhdsWithin
    exact he.mono fun x hx => binaryEntropy_le_half_pos hp hp2 ha hx
  · exact binaryEntropy_le_half_pos hp hp2 ha hb

theorem binaryEntropy_symm (p a b : ℝ) : binaryEntropy (1-p) b a = binaryEntropy p a b := by
  unfold binaryEntropy
  rw [show 1-(1-p) = p by ring,
    show (1-p)*b^2+p*a^2 = p*a^2+(1-p)*b^2 by ring]
  ring

/-- The full ordinary binary inequality with the exact Lee--Yau constant.
The probability endpoints and zero function values are included. -/
theorem binaryEntropy_le {p a b : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    binaryEntropy p a b ≤ -(p*(1-p))*Real.log (p*(1-p))/Real.log 2*(a-b)^2 := by
  rcases eq_or_lt_of_le hp with heq | hp
  · subst p
    simp only [binaryEntropy, zero_mul, sub_zero, one_mul, zero_add, sub_self, neg_zero,
      zero_div, le_refl]
  rcases eq_or_lt_of_le hp1 with heq | hp1
  · subst p
    simp only [binaryEntropy, one_mul, sub_self, zero_mul, add_zero, neg_zero,
      zero_div, le_refl]
  by_cases hp2 : p ≤ 1/2
  · exact binaryEntropy_le_half hp hp2 ha hb
  have hq : 0 < 1-p := by linarith
  have hq2 : 1-p ≤ 1/2 := by linarith
  have hh := binaryEntropy_le_half hq hq2 hb ha
  rw [binaryEntropy_symm, show (1-p)*(1-(1-p)) = p*(1-p) by ring] at hh
  simpa only [show (b-a)^2 = (a-b)^2 by ring] using hh

/-- The scalar inequality in the density variables used by finite entropy. -/
theorem twoPoint_entropy_le {p u v : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    p*u*Real.log u+(1-p)*v*Real.log v-
      (p*u+(1-p)*v)*Real.log (p*u+(1-p)*v) ≤
      -(p*(1-p))*Real.log (p*(1-p))/Real.log 2*(Real.sqrt u-Real.sqrt v)^2 := by
  have hh := binaryEntropy_le hp hp1 (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)
  simpa only [binaryEntropy, Real.sq_sqrt hu, Real.sq_sqrt hv] using hh

end BinaryCalculus

end PeriodicAttractiveLogGas.MultisliceLogSobolev
