module

public import GinibrePoincare.Analysis.GinibreDrivenPathOU

@[expose] public section

/-! # Continuous linear projections of actual OU convolutions -/
open MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

 theorem drivenOUPath_continuousLinearMap (L : E →L[ℝ] F) (κ : ℝ) (x : E)
    (N : ℝ → E) (hN : Continuous N) (t : ℝ) :
    L (drivenOUPath κ x N t) = drivenOUPath κ (L x) (fun s => L (N s)) t := by
  have hc : Continuous (fun s : ℝ => Real.exp (κ * s) • N s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul hN
  simp only [drivenOUPath, drivenOUCorrection, map_add, map_smul, map_sub]
  rw [← L.intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
  simp only [map_smul]

end
end GinibrePoincare
