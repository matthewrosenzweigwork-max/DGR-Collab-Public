import DGRHS.Dynamics.SourceDynamicCovarianceTime
import DGRHS.Dynamics.SourceDynamicGaussian
import DGRHS.Dynamics.SourceDynamicCovarianceInterval
import DGRHS.Dynamics.SourceDynamicLevy

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamicTimeCovariance
#print axioms DGRHS.Dynamics.sourceDynamicTimeCovariance

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_stopped_pair_proper
#print axioms DGRHS.Dynamics.sourceDynamic_stopped_pair_proper

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_stopped_pair_identity
#print axioms DGRHS.Dynamics.sourceDynamic_stopped_pair_identity

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_time_covariance_quadratic
#print axioms DGRHS.Dynamics.sourceDynamic_time_covariance_quadratic

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_time_covariance_posSemidef
#print axioms DGRHS.Dynamics.sourceDynamic_time_covariance_posSemidef

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_initial_secondMoment_posSemidef
#print axioms DGRHS.Dynamics.sourceDynamic_initial_secondMoment_posSemidef

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_total_covariance_posSemidef
#print axioms DGRHS.Dynamics.sourceDynamic_total_covariance_posSemidef

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_gaussian_target
#print axioms DGRHS.Dynamics.sourceDynamic_gaussian_target

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_interval_covariance
#print axioms DGRHS.Dynamics.sourceDynamic_interval_covariance

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_total_interval_covariance_posSemidef
#print axioms DGRHS.Dynamics.sourceDynamic_total_interval_covariance_posSemidef

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_finite_charFun
#print axioms DGRHS.Dynamics.sourceDynamic_finite_charFun

set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_scalar_characteristic_clt
#print axioms DGRHS.Dynamics.sourceDynamic_scalar_characteristic_clt
