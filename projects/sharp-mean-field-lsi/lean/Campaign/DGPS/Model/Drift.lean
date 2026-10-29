import DGPS.Foundations.AbsoluteDensity
import DGPS.Foundations.PeriodicSmoothing
import DGPS.Model.Data

/-!
# Weak-drift action without domain substitution (DEF009)

INTERFACES/definitions.md §2, common_lemmas.md DEF009, 02_NORMALIZATION_AND_DEFINITIONS.md §2.

For fixed interaction data `A : InteractionData d` and **every** absolute-admissible density `ρ`
(`AbsoluteDensity d`, with no restriction of the competitor type) the potential
`V + W * (ρ m)` is the continuous function
`x ↦ V x + ∫ W x y d(ρ m)(y)` (`interactionPotential`), obtained by integrating the continuous
representative of `W` against `ρ m`.

`AbsoluteDrift A` is a provider assigning to every absolute density a measurable vector field
`force ρ` which is an `L¹(m; ℝ^d)` weak gradient of `interactionPotential A ρ`, tested against all
smooth periodic functions (`IsWeakGradientLp 1`, the `p = 1` instance of the weak-gradient
predicate of FOU002; the gradient is not required to be in `L²`, because the force in the rough
`W^{1,1}` models is only `L^p`). The structure is a provider interface: it is constructed from each
model's regularity theorem; no derivative is defaulted to zero (the zero field is a provider only
for the zero data, `AbsoluteDrift.zero`).

Uniqueness: an `L¹` weak gradient is unique a.e. (`IsWeakGradientLp.ae_eq_of_one`, via the
periodic mollifier: `∂ⱼ (moll n u) = moll n gⱼ` determines `moll n gⱼ`, and `moll n gⱼ → gⱼ`
in `L¹`). Hence any two providers agree a.e. (`absoluteDrift_unique`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS

variable {d : ℕ}

/-- The potential `V + W * (ρ m)`: `x ↦ V x + ∫ W x y d(ρ m)(y)` (DEF009), for the continuous
data representatives of `V` and `W` and an arbitrary absolute-admissible density `ρ`. -/
noncomputable def interactionPotential (A : InteractionData d) (ρ : AbsoluteDensity d) :
    Torus d → ℝ :=
  fun x => A.V x + ∫ y, A.W x y ∂(densityMeasure ρ : Measure (Torus d))

/-- The potential written against Haar measure: `V x + ∫ ρ(y) W(x,y) dm(y)`. -/
theorem interactionPotential_eq (A : InteractionData d) (ρ : AbsoluteDensity d) (x : Torus d) :
    interactionPotential A ρ x = A.V x + ∫ y, ρ.density y * A.W x y ∂haar d := by
  unfold interactionPotential
  congr 1
  rw [densityMeasure_coe]
  rw [integral_withDensity_eq_integral_toReal_smul₀]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [AbsoluteDensity.density, ENNReal.toReal_ofReal (sq_nonneg _)]
  · exact (ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

/-- An `L¹` weak gradient is unique a.e.: two integrable `L¹` weak gradients (tested against all
smooth periodic functions) of the same function agree a.e. -/
theorem IsWeakGradientLp.ae_eq_of_one {u : Torus d → ℝ} {g g' : Torus d → Tangent d}
    (hg : IsWeakGradientLp 1 u g) (hg' : IsWeakGradientLp 1 u g') : g =ᵐ[haar d] g' := by
  have hj : ∀ j : Fin d, (fun x => g x j) =ᵐ[haar d] fun x => g' x j := by
    intro j
    have h1 := memLp_coord_of_memLp hg.memLp_grad j
    have h2 := memLp_coord_of_memLp hg'.memLp_grad j
    have hm : ∀ n, SharpLSI.moll n (fun x => g x j) = SharpLSI.moll n (fun x => g' x j) := fun n =>
      (hg.coordPartial_moll le_rfl n j).symm.trans (hg'.coordPartial_moll le_rfl n j)
    have t1 := tendsto_eLpNorm_moll_sub (p := 1) le_rfl ENNReal.one_ne_top h1
    have t2 := tendsto_eLpNorm_moll_sub (p := 1) le_rfl ENNReal.one_ne_top h2
    have hle : ∀ n, eLpNorm (fun y => g y j - g' y j) 1 (haar d) ≤
        eLpNorm (fun y => SharpLSI.moll n (fun x => g x j) y - g y j) 1 (haar d) +
        eLpNorm (fun y => SharpLSI.moll n (fun x => g' x j) y - g' y j) 1 (haar d) := by
      intro n
      have hsub : (fun y => g y j - g' y j) =
          (fun y => -(SharpLSI.moll n (fun x => g x j) y - g y j)) +
          (fun y => SharpLSI.moll n (fun x => g' x j) y - g' y j) := by
        funext y
        have := congrFun (hm n) y
        simp only [Pi.add_apply, this]; ring
      have hmm1 : MemLp (fun y => SharpLSI.moll n (fun x => g x j) y - g y j) 1 (haar d) :=
        (memLp_moll n le_rfl ENNReal.one_ne_top h1).sub h1
      have hmm2 : MemLp (fun y => SharpLSI.moll n (fun x => g' x j) y - g' y j) 1 (haar d) :=
        (memLp_moll n le_rfl ENNReal.one_ne_top h2).sub h2
      rw [hsub]
      refine (eLpNorm_add_le le_rfl).trans ?_
      have hn : eLpNorm (fun y => -(SharpLSI.moll n (fun x => g x j) y - g y j)) 1 (haar d) =
          eLpNorm (fun y => SharpLSI.moll n (fun x => g x j) y - g y j) 1 (haar d) :=
        eLpNorm_neg (fun y => SharpLSI.moll n (fun x => g x j) y - g y j) 1 (haar d)
      rw [hn]
    have hlim : Tendsto (fun _ : ℕ => eLpNorm (fun y => g y j - g' y j) 1 (haar d)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using t1.add t2) (fun _ => zero_le) hle
    have h0 : eLpNorm (fun y => g y j - g' y j) 1 (haar d) = 0 :=
      tendsto_nhds_unique (tendsto_const_nhds) hlim
    have := (eLpNorm_eq_zero_iff (p := 1) one_ne_zero).mp h0
    filter_upwards [this] with x hx
    simpa [sub_eq_zero] using hx
  filter_upwards [ae_all_iff.mpr hj] with x hx
  ext j
  exact hx j

/-- Weak-drift provider (DEF009): for fixed interaction data `A`, an assignment to **every**
absolute-admissible density `ρ` of a measurable vector field `force ρ` which is an `L¹(m; ℝ^d)`
weak gradient of `V + W * (ρ m)` (`interactionPotential A ρ`), tested against all smooth periodic
functions. No `L²` bound on `force ρ` (hence no finite-dissipation restriction on competitors) and
no restriction of the competitor type is part of the structure; it is constructed from each
model's regularity theorem. -/
structure AbsoluteDrift (A : InteractionData d) where
  force : AbsoluteDensity d → Torus d → Tangent d
  measurable_force : ∀ ρ, Measurable (force ρ)
  weak_gradient : ∀ ρ, IsWeakGradientLp 1 (interactionPotential A ρ) (force ρ)

end DGPS

namespace DGPS.AbsoluteDrift

variable {d : ℕ} {A : InteractionData d}

/-- The force of a provider is integrable. -/
theorem integrable_force (b : AbsoluteDrift A) (ρ : AbsoluteDensity d) :
    Integrable (b.force ρ) (haar d) :=
  (b.weak_gradient ρ).memLp_grad.integrable le_rfl

/-- Any `L¹` weak gradient of `V + W * (ρ m)` agrees a.e. with the provider's force. -/
theorem ae_eq_of_isWeakGradient (b : AbsoluteDrift A) (ρ : AbsoluteDensity d)
    {g : Torus d → Tangent d} (hg : IsWeakGradientLp 1 (interactionPotential A ρ) g) :
    b.force ρ =ᵐ[haar d] g :=
  (b.weak_gradient ρ).ae_eq_of_one hg

/-- Zero interaction data is served by the zero force (an actual weak gradient: the potential is
identically zero). -/
noncomputable def zero (d : ℕ) : AbsoluteDrift (InteractionData.zero d) where
  force := fun _ _ => 0
  measurable_force := fun _ => measurable_const
  weak_gradient := fun ρ => by
    have hpot : interactionPotential (InteractionData.zero d) ρ = fun _ => 0 := by
      funext x; simp [interactionPotential, InteractionData.zero]
    rw [hpot]
    exact ⟨memLp_const 0, memLp_const 0, fun φ _ j => by simp⟩

end DGPS.AbsoluteDrift

namespace DGPS

variable {d : ℕ} {A : InteractionData d}

/-- DEF009 uniqueness: any two weak-drift providers for the same interaction data agree a.e. on
every absolute-admissible density, so the force (and the rate built from it) does not depend on
the provider. -/
theorem absoluteDrift_unique (b b' : AbsoluteDrift A) (ρ : AbsoluteDensity d) :
    b.force ρ =ᵐ[haar d] b'.force ρ :=
  b.ae_eq_of_isWeakGradient ρ (b'.weak_gradient ρ)

end DGPS
