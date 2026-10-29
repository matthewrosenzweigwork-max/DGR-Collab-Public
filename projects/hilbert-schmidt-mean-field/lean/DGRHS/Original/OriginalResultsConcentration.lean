import Batteries.Tactic.Alias
import DGRHS.Attractive.CanonicalArraySamples
import DGRHS.Concentration.MasterEnvelope
import DGRHS.Concentration.MasterTail
import DGRHS.Concentration.MasterUniform
import DGRHS.Concentration.SourceAffineComparison
import DGRHS.Decoupling.Moment
import DGRHS.Gaussian.FeatureRateFactory
import DGRHS.Gaussian.GaussianLogCutoffInterpolation
import DGRHS.Gaussian.GaussianRieszInterpolatedMoment
import DGRHS.Gaussian.LogPhysicalConvolution
import DGRHS.Gaussian.SourceRepulsiveLogRateOneBody
import DGRHS.Kernel.PositiveDefiniteDiagonalBound
import DGRHS.Kernel.PositiveDefiniteKernelCentering

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). Source-facing export suite, area: Concentration.

Each `alias` creates a new declaration with EXACTLY the type of an existing
root declaration (no premise added or removed). The source label, lines and the
row disposition from reports/DISPOSITIONS_253.json are recorded beside it; a
row marked SOURCE_DISCREPANCY or UNRESOLVED exports only the valid corrected or
partial statement named in that row's qualification, never the printed
auxiliary claim. Target bytes/status are bound by the gate records cited in the
disposition, not by this file. -/

/-- rem:oneBodyExpIntegrability (source 600–602); row disposition REUSED. -/
alias DGRHS.Original.rem_oneBodyExpIntegrability.Gaussian_logPhysicalPotential_proper_bounds := DGRHS.Gaussian.logPhysicalPotential_proper_bounds

/-- rem:oneBodyExpIntegrability (source 600–602); row disposition REUSED. -/
alias DGRHS.Original.rem_oneBodyExpIntegrability.SourceRepulsiveLogRate_physicalPotential_memLp_two := DGRHS.SourceRepulsiveLogRate.physicalPotential_memLp_two

/-- prop:UstatTail (source 1068–1082); row disposition FOUNDATIONAL_IMPORT. -/
alias DGRHS.Original.prop_UstatTail.Concentration_iid_master_tail := DGRHS.Concentration.iid_master_tail

/-- rem:Ustattail (source 1084–1093); row disposition SOURCE_DISCREPANCY. -/
alias DGRHS.Original.rem_Ustattail.Concentration_iid_master_tail := DGRHS.Concentration.iid_master_tail

/-- prop:decoup (source 1097–1104); row disposition FOUNDATIONAL_IMPORT. -/
alias DGRHS.Original.prop_decoup.Decoupling_scalar_even_moment_decoupling := DGRHS.Decoupling.scalar_even_moment_decoupling

/-- rem:decoupMoment (source 1106–1122); row disposition REUSED. -/
alias DGRHS.Original.rem_decoupMoment.Decoupling_scalar_even_moment_decoupling := DGRHS.Decoupling.scalar_even_moment_decoupling

/-- rem:decoupMoment (source 1106–1122); row disposition REUSED. -/
alias DGRHS.Original.rem_decoupMoment.Decoupling_scalar_even_moment_decoupling_symmetric := DGRHS.Decoupling.scalar_even_moment_decoupling_symmetric

/-- rem:decoupMoment (source 1106–1122); row disposition REUSED. -/
alias DGRHS.Original.rem_decoupMoment.Attractive_row_factorial_even_decoupling := DGRHS.Attractive.row_factorial_even_decoupling

/-- prop:masterLayerCake (source 1138–1176); row disposition REUSED. -/
alias DGRHS.Original.prop_masterLayerCake.Concentration_master_uniform_exponential_moment := DGRHS.Concentration.master_uniform_exponential_moment

/-- rem:masterUniform (source 1178–1185); row disposition REUSED. -/
alias DGRHS.Original.rem_masterUniform.Concentration_master_uniform_exponential_envelope := DGRHS.Concentration.master_uniform_exponential_envelope

/-- lem:PDdeterministicDiagonalBound (source 1328–1344); row disposition REUSED. -/
alias DGRHS.Original.lem_PDdeterministicDiagonalBound.Kernel_positiveDefiniteKernel_centering := DGRHS.Kernel.positiveDefiniteKernel_centering

/-- lem:PDdeterministicDiagonalBound (source 1328–1344); row disposition REUSED. -/
alias DGRHS.Original.lem_PDdeterministicDiagonalBound.Kernel_positiveDefiniteKernel_original_diagonal_bound := DGRHS.Kernel.positiveDefiniteKernel_original_diagonal_bound

/-- lem:interpolatedExpMoment (source 1764–1770); row disposition REUSED. -/
alias DGRHS.Original.lem_interpolatedExpMoment.Gaussian_gaussianLogInterpolated_uniform_exponential := DGRHS.Gaussian.gaussianLogInterpolated_uniform_exponential

/-- lem:interpolatedExpMoment (source 1764–1770); row disposition REUSED. -/
alias DGRHS.Original.lem_interpolatedExpMoment.Gaussian_gaussianRieszInterpolated_uniform_exponential := DGRHS.Gaussian.gaussianRieszInterpolated_uniform_exponential

/-- prop:boundedFeatureQuadLaplace (source 1801–1828); row disposition REUSED. -/
alias DGRHS.Original.prop_boundedFeatureQuadLaplace.Gaussian_exists_separable_featureParticleInteraction_rate := DGRHS.Gaussian.exists_separable_featureParticleInteraction_rate

/-- lem:oneBodyReduction (source 2093–2103); row disposition REUSED. -/
alias DGRHS.Original.lem_oneBodyReduction.Concentration_sourceAffinePartition_comparison := DGRHS.Concentration.sourceAffinePartition_comparison
