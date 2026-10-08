module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicGaussianProcess
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGlobalCovariance
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGlobalCoordinates
public import Mathlib.Probability.BrownianMotion.Basic
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem bakryBrownianGlobalProcess_isBrownian :
    IsBrownianReal bakryBrownianGlobalProcess bakryBrownianGlobalMeasure := by
  have hL := bakryBrownianDyadicCompletedPath_memLp_of_original bakryBrownianDyadicPath_memLp_two
  have hC := bakryBrownianDyadicCompletedPath_covariance_of_original bakryBrownianDyadicPath_covariance
  have hM := bakryBrownianDyadicCompletedPath_mean_of_original bakryBrownianDyadicPath_mean
  have hG := bakryBrownianGlobalProcess_isGaussian_of_unit
    (bakryBrownianDyadicCompletedPath_isGaussian_of_original bakryBrownianDyadicPath_isGaussianProcess)
  refine ⟨hG.isPreBrownianReal_of_covariance
    (bakryBrownianGlobalProcess_mean_of_unit hL hM) ?_,?_⟩
  · intro s t hst
    rw [bakryBrownianGlobalProcess_covariance_of_unit hL hC,min_eq_left]
    exact_mod_cast hst
  · exact ae_of_all _ bakryBrownianGlobalProcess_continuous

theorem bakryBrownianCoordinate_isBrownian (ι : Type*) [Fintype ι] :
    ∀ i, IsBrownianReal (bakryBrownianCoordinateProcess ι i) (bakryBrownianCoordinateMeasure ι) :=
  bakryBrownianCoordinate_isBrownian_of_scalar ι bakryBrownianGlobalProcess_isBrownian

#print axioms bakryBrownianGlobalProcess_isBrownian
#print axioms bakryBrownianCoordinate_isBrownian
end
end GinibrePoincare
