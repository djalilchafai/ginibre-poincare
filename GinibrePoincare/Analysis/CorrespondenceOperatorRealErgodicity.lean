module
public import GinibrePoincare.Analysis.CorrespondenceOperatorErgodicity
@[expose] public section
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
/-- Strong convergence of the unrestricted real diffusion to its actual mean. -/
theorem correspondenceOperatorRealEvolution_ergodic {n : ℕ} (hn : 0<n)
    (u : GinibreFullValueL2 n) :
    Tendsto (fun t : ℝ≥0 => correspondenceOperatorRealEvolution n hn t u) atTop
      (𝓝 (ginibreRealConstantL2 n hn (∫z,u z∂ginibreMeasure n))) := by
  have hm : (∫z,ginibreFullComplexOfReal n u z∂ginibreMeasure n) =
      ((∫z,u z∂ginibreMeasure n : ℝ):ℂ) := by
    rw [integral_congr_ae (ginibreFullComplexOfReal_ae n u), integral_complex_ofReal]
  have h := (ginibreFullComplexRe n).continuous.tendsto _ |>.comp
    (correspondenceOperatorEvolution_ergodic hn (ginibreFullComplexOfReal n u))
  rw [hm] at h
  have hc : ginibreFullComplexRe n (ginibreFullConstant n hn
      ((∫z,u z∂ginibreMeasure n : ℝ):ℂ)).val =
      ginibreRealConstantL2 n hn (∫z,u z∂ginibreMeasure n) :=
    by
      have hh : ginibreFullComplexRe n (ginibreFullConstant n hn
          ((∫z,u z∂ginibreMeasure n : ℝ):ℂ)).val =
          ginibreRealConstantL2 n hn (((∫z,u z∂ginibreMeasure n : ℝ):ℂ).re) :=
        ginibreFullConstant_re n hn _
      simpa using hh
  rw [hc] at h
  exact h
#print axioms correspondenceOperatorRealEvolution_ergodic
end
end GinibrePoincare
