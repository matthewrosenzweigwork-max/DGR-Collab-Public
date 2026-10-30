import DGPS.Examples.PolynomialSpeciesDeficitTaylor
import DGPS.Frontier.STR029.T59

/-! Coordinate-power division for the ACTUAL physical reduced deficit.
This project-specific adapter uses the existing stock-Taylor/parametric-integral
implementation of T59. The zero-jet hypotheses below are factual derivative
identities, NOT a differentiated value-error estimate. Their discharge from the
actual same-graph coefficient producer is a separate remaining obligation. -/

noncomputable section
open Filter Topology Set NormedSpace MeasureTheory
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- Literal independent coefficient order: amplitude A,B, rate alpha, tilt sigma. -/
abbrev PolynomialScaledCoefficients := ℝ × ℝ × ℝ × ℝ

local instance : NormedAddCommGroup (PolynomialScaledCoefficients →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (PolynomialScaledCoefficients →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (PolynomialScaledCoefficients →L[ℝ] PolynomialScaledCoefficients →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (PolynomialScaledCoefficients →L[ℝ] PolynomialScaledCoefficients →L[ℝ] ℝ) := inferInstance

def polynomialScaledParameters (p : ℝ × PolynomialScaledCoefficients) : PolynomialRangeParameters :=
  (p.1 * p.2.1, p.1 * p.2.2.1, (p.1, p.1 ^ 4 * p.2.2.2.2), p.1 ^ 2 * p.2.2.2.1)

/-- UNDIVIDED physical value: the actual a0 normalization remains inside the deficit. -/
def polynomialScaledDeficit (ψ : PolynomialRangeParameters → E_STR02969)
    (p : ℝ × PolynomialScaledCoefficients) : ℝ :=
  polynomialReducedDeficit ψ (polynomialScaledParameters p)

private def coeffEncode (c : PolynomialScaledCoefficients) : Fin 4 → ℝ :=
  ![c.1, c.2.1, c.2.2.1, c.2.2.2]
private def coeffDecode (z : Fin 4 → ℝ) : PolynomialScaledCoefficients := (z 0, z 1, z 2, z 3)
private theorem coeffDecode_encode (c : PolynomialScaledCoefficients) : coeffDecode (coeffEncode c)=c := rfl

private def encodedValue (ψ : PolynomialRangeParameters → E_STR02969)
    (q : ℝ × (Fin 4 → ℝ)) : ℝ := polynomialScaledDeficit ψ (q.1, coeffDecode q.2)

/-- The actual fourth Taylor integral, with physical a0 UNDIVIDED. -/
def polynomialScaledDeficitFactor (ψ : PolynomialRangeParameters → E_STR02969)
    (p : ℝ × PolynomialScaledCoefficients) : ℝ :=
  quotientRemainder_STR02959 (encodedValue ψ) p.1 (coeffEncode p.2)

theorem polynomialScaledDeficitFactor_integral (ψ : PolynomialRangeParameters → E_STR02969)
    (h : ℝ) (c : PolynomialScaledCoefficients) :
    polynomialScaledDeficitFactor ψ (h,c) = (1 / (Nat.factorial 3 : ℝ)) *
      ∫ t in (0:ℝ)..1, (1-t)^3 * iteratedDeriv 4
        (fun s : ℝ => polynomialScaledDeficit ψ (s,c)) (t*h) := rfl

private theorem scaled_smooth : ContDiff ℝ ∞ polynomialScaledParameters := by
  unfold polynomialScaledParameters
  fun_prop

/-- Actual smoothness comes from the SAME graph's real reduced deficit, without
selected-root differentiation or an independent smooth value model. -/
theorem polynomialScaledDeficit_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffOn ℝ ∞ (polynomialScaledDeficit ψ) (polynomialScaledParameters ⁻¹' U) :=
  (polynomialReducedDeficit_smooth hψ).comp scaled_smooth.contDiffOn (fun _ hp => hp)

private theorem encode_smooth : ContDiff ℝ ∞ coeffEncode := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun c : PolynomialScaledCoefficients => c.1); fun_prop
  · change ContDiff ℝ ∞ (fun c : PolynomialScaledCoefficients => c.2.1); fun_prop
  · change ContDiff ℝ ∞ (fun c : PolynomialScaledCoefficients => c.2.2.1); fun_prop
  · change ContDiff ℝ ∞ (fun c : PolynomialScaledCoefficients => c.2.2.2); fun_prop

private theorem decode_smooth : ContDiff ℝ ∞ coeffDecode := by
  unfold coeffDecode
  fun_prop

private theorem compact_slice_uniform {Y : Type*} [PseudoMetricSpace Y]
    (F : ℝ × PolynomialScaledCoefficients → Y)
    (hF : ∀ c, ContinuousAt F ((0:ℝ),c)) {K : Set PolynomialScaledCoefficients}
    (hK : IsCompact K) :
    TendstoUniformlyOn (fun h c => F (h,c)) (fun c => F (0,c)) (𝓝 (0:ℝ)) K := by
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  have hev : ∀ᶠ h in 𝓝 (0:ℝ), ∀ c ∈ K, dist (F (h,c)) (F (0,c))<ε := by
    apply hK.eventually_forall_of_forall_eventually
    intro c _
    have hq : Continuous (fun p : ℝ × PolynomialScaledCoefficients => ((0:ℝ),p.2)) := by fun_prop
    have h2 : ContinuousAt (fun p : ℝ × PolynomialScaledCoefficients => F (0,p.2)) (0,c) :=
      (hF c).comp (x := ((0:ℝ),c)) hq.continuousAt
    exact ((hF c).dist h2).eventually_lt continuousAt_const (by simpa using hε)
  filter_upwards [hev] with h hh c hc
  simpa only [dist_comm] using hh c hc

private theorem coefficient_derivatives_contDiffAt (F : ℝ × PolynomialScaledCoefficients → ℝ)
    (p : ℝ × PolynomialScaledCoefficients) (hF : ContDiffAt ℝ ∞ F p) :
    ContDiffAt ℝ ∞ (fun q : ℝ × PolynomialScaledCoefficients =>
      fderiv ℝ (fun c => F (q.1,c)) q.2) p ∧
    ContDiffAt ℝ ∞ (fun q : ℝ × PolynomialScaledCoefficients =>
      fderiv ℝ (fderiv ℝ (fun c => F (q.1,c))) q.2) p := by
  let q := fun z : (ℝ × PolynomialScaledCoefficients) × PolynomialScaledCoefficients => (z.1.1,z.2)
  have hq : ContDiff ℝ ∞ q := by dsimp only [q]; fun_prop
  have hq0 : q (p,p.2)=p := rfl
  have huncurry : ContDiffAt ℝ ∞ (Function.uncurry
      (fun (z : ℝ × PolynomialScaledCoefficients) (c : PolynomialScaledCoefficients) => F (z.1,c))) (p,p.2) := by
    have ht := hF.comp (p,p.2) hq.contDiffAt
    exact ht
  have hD : ContDiffAt ℝ ∞ (fun z : ℝ × PolynomialScaledCoefficients =>
      fderiv ℝ (fun c => F (z.1,c)) z.2) p :=
    ContDiffAt.fderiv huncurry contDiffAt_snd (by simp)
  have huncurryD : ContDiffAt ℝ ∞ (Function.uncurry
      (fun (z : ℝ × PolynomialScaledCoefficients) (c : PolynomialScaledCoefficients) =>
        fderiv ℝ (fun w => F (z.1,w)) c)) (p,p.2) := by
    have ht := hD.comp (p,p.2) hq.contDiffAt
    exact ht
  exact ⟨hD, ContDiffAt.fderiv huncurryD contDiffAt_snd (by simp)⟩

/-- Smooth local integral division and genuine uniform C2 coefficient convergence.
Only factual origin h-jets are supplied. In particular no desired derivative
remainder, factor, C2 convergence or selected-reference regularity is a premise.
This adapter is CONDITIONAL until the actual coefficient producer discharges
these jets for the SAME graph. -/
private theorem local_factor_of_origin_jets
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters)∈U)
    (hψ : ContDiffOn ℝ ∞ ψ U)
    (hjet : ∀ c : PolynomialScaledCoefficients, ∀ j : ℕ, j≤3 →
      iteratedDeriv j (fun h : ℝ => polynomialScaledDeficit ψ (h,c)) 0=0) :
    ∃ O : Set (ℝ × PolynomialScaledCoefficients), IsOpen O ∧
      (∀ c, ((0:ℝ),c)∈O) ∧
      ContDiffOn ℝ ∞ (polynomialScaledDeficitFactor ψ) O ∧
      (∀ h c, (h,c)∈O → polynomialScaledDeficit ψ (h,c)=h^4*polynomialScaledDeficitFactor ψ (h,c)) ∧
      (∀ c, polynomialScaledDeficitFactor ψ (0,c)=
        iteratedDeriv 4 (fun h : ℝ => polynomialScaledDeficit ψ (h,c)) 0 / (Nat.factorial 4 : ℝ)) := by
  classical
  let decode := fun q : ℝ × (Fin 4 → ℝ) => (q.1,coeffDecode q.2)
  let encode := fun p : ℝ × PolynomialScaledCoefficients => (p.1,coeffEncode p.2)
  have hd : ContDiff ℝ ∞ decode := contDiff_fst.prodMk (decode_smooth.comp contDiff_snd)
  have he : ContDiff ℝ ∞ encode := contDiff_fst.prodMk (encode_smooth.comp contDiff_snd)
  let Ω := (fun q => polynomialScaledParameters (decode q)) ⁻¹' U
  have hΩ : IsOpen Ω := hU.preimage (scaled_smooth.comp hd).continuous
  have hG : ContDiffOn ℝ ∞ (encodedValue ψ) Ω :=
    (polynomialScaledDeficit_smooth hψ).comp hd.contDiffOn (fun _ hp => hp)
  have h0 : ∀ z : Fin 4 → ℝ, ((0:ℝ),z)∈Ω := by
    intro z
    change polynomialScaledParameters (0,coeffDecode z)∈U
    simpa only [polynomialScaledParameters, zero_mul, zero_pow (by norm_num : (4:ℕ)≠0),
      zero_pow (by norm_num : (2:ℕ)≠0)] using (show ((0,0,(0,0),0) : PolynomialRangeParameters) ∈ U from h0U)
  have hj : ∀ j : ℕ, j≤3 → ∀ z ∈ (Set.univ : Set (Fin 4 → ℝ)),
      iteratedDeriv j (fun h => encodedValue ψ (h,z)) 0=0 :=
    fun j hj z _ => hjet (coeffDecode z) j hj
  choose W hWo hW0 _ _ hWC hWval hWzero using fun z : Fin 4 → ℝ =>
    str029_59_smooth_division_coordinate_power (U:=Set.univ) hΩ hG
      (fun z _ => h0 z) hj (z₀:=z) (Set.mem_univ z)
  let O₄ := ⋃ z, W z
  have hO₄ : IsOpen O₄ := isOpen_iUnion hWo
  have h0O₄ : ∀ z : Fin 4 → ℝ, ((0:ℝ),z)∈O₄ := fun z => mem_iUnion.2 ⟨z,hW0 z⟩
  have hC₄ : ContDiffOn ℝ ∞ (fun q : ℝ × (Fin 4 → ℝ) =>
      quotientRemainder_STR02959 (encodedValue ψ) q.1 q.2) O₄ := by
    apply contDiffOn_of_locally_contDiffOn
    intro p hp
    obtain ⟨z,hz⟩ := mem_iUnion.1 hp
    exact ⟨W z,hWo z,hz,(hWC z).mono Set.inter_subset_right⟩
  let O := encode ⁻¹' O₄
  have hO : IsOpen O := hO₄.preimage he.continuous
  have h0O : ∀ c : PolynomialScaledCoefficients, ((0:ℝ),c)∈O := fun c => h0O₄ (coeffEncode c)
  have hC : ContDiffOn ℝ ∞ (polynomialScaledDeficitFactor ψ) O := by
    change ContDiffOn ℝ ∞ ((fun q : ℝ × (Fin 4 → ℝ) => quotientRemainder_STR02959 (encodedValue ψ) q.1 q.2) ∘ encode) O
    exact hC₄.comp he.contDiffOn (fun _ hp => hp)
  refine ⟨O,hO,h0O,hC,?_,?_⟩
  · intro h c hp
    by_cases hh : h=0
    · subst h
      have hz := hjet c 0 (by norm_num)
      simpa only [iteratedDeriv_zero, zero_pow (by norm_num : (4:ℕ)≠0),zero_mul] using hz
    · obtain ⟨z,hz⟩ := mem_iUnion.1 hp
      have hv := hWval z h (coeffEncode c) hz (Set.mem_univ _) hh
      change polynomialScaledDeficitFactor ψ (h,c)=polynomialScaledDeficit ψ (h,c)/h^4 at hv
      calc
        polynomialScaledDeficit ψ (h,c) = polynomialScaledDeficitFactor ψ (h,c)*h^4 :=
          ((eq_div_iff (pow_ne_zero 4 hh)).1 hv).symm
        _ = h^4*polynomialScaledDeficitFactor ψ (h,c) := mul_comm _ _
  · intro c
    have hv := hWzero (coeffEncode c) (coeffEncode c) (hW0 (coeffEncode c)) (Set.mem_univ _)
    exact hv

theorem polynomialScaledDeficit_factor_of_origin_jets
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters)∈U)
    (hψ : ContDiffOn ℝ ∞ ψ U)
    (hjet : ∀ c : PolynomialScaledCoefficients, ∀ j : ℕ, j≤3 →
      iteratedDeriv j (fun h : ℝ => polynomialScaledDeficit ψ (h,c)) 0=0) :
    ∃ O : Set (ℝ × PolynomialScaledCoefficients), IsOpen O ∧
      (∀ c, ((0:ℝ),c)∈O) ∧
      ContDiffOn ℝ ∞ (polynomialScaledDeficitFactor ψ) O ∧
      (∀ h c, (h,c)∈O → polynomialScaledDeficit ψ (h,c)=h^4*polynomialScaledDeficitFactor ψ (h,c)) ∧
      (∀ c, polynomialScaledDeficitFactor ψ (0,c)=
        iteratedDeriv 4 (fun h : ℝ => polynomialScaledDeficit ψ (h,c)) 0 / (Nat.factorial 4 : ℝ)) ∧
      ∀ K : Set PolynomialScaledCoefficients, IsCompact K →
        TendstoUniformlyOn (fun h c => polynomialScaledDeficitFactor ψ (h,c))
          (fun c => polynomialScaledDeficitFactor ψ (0,c)) (𝓝 (0:ℝ)) K ∧
        TendstoUniformlyOn (fun h c => fderiv ℝ (fun z => polynomialScaledDeficitFactor ψ (h,z)) c)
          (fderiv ℝ (fun z => polynomialScaledDeficitFactor ψ (0,z))) (𝓝 (0:ℝ)) K ∧
        TendstoUniformlyOn (fun h c => fderiv ℝ (fderiv ℝ (fun z => polynomialScaledDeficitFactor ψ (h,z))) c)
          (fderiv ℝ (fderiv ℝ (fun z => polynomialScaledDeficitFactor ψ (0,z)))) (𝓝 (0:ℝ)) K := by
  obtain ⟨O,hO,h0O,hC,hval,hzero⟩ := local_factor_of_origin_jets hU h0U hψ hjet
  refine ⟨O,hO,h0O,hC,hval,hzero,?_⟩
  intro K hK
  have hc (c : PolynomialScaledCoefficients) : ContDiffAt ℝ ∞ (polynomialScaledDeficitFactor ψ) (0,c) :=
    hC.contDiffAt (hO.mem_nhds (h0O c))
  refine ⟨compact_slice_uniform _ (fun c => (hc c).continuousAt) hK,?_,?_⟩
  · exact compact_slice_uniform _ (fun c => (coefficient_derivatives_contDiffAt _ _ (hc c)).1.continuousAt) hK
  · exact compact_slice_uniform _ (fun c => (coefficient_derivatives_contDiffAt _ _ (hc c)).2.continuousAt) hK

end DGPS.Examples.PolynomialSpecies
