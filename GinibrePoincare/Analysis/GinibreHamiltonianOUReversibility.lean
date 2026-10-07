module

public import GinibrePoincare.Analysis.GinibreOUTransitionSemigroup

@[expose] public section

/-! Exact Gaussian OU density balance; no reversibility is assumed. -/
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem gaussianOU_pdf_balance (a : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (hvar : a^2+2*(v : ℝ)=1) (x y : ℝ) :
    gaussianPDFReal 0 (1/2) x*gaussianPDFReal (a*x) v y =
      gaussianPDFReal 0 (1/2) y*gaussianPDFReal (a*y) v x := by
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have he : -x^2-(y-a*x)^2/(2*(v : ℝ)) =
      -y^2-(x-a*y)^2/(2*(v : ℝ)) := by
    field_simp
    nlinarith [sq_nonneg x,sq_nonneg y,show (x^2-y^2)*(a^2+2*(v : ℝ)-1)=0 by rw [hvar]; ring]
  simp only [gaussianPDFReal,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,sub_zero]
  have hx : -x^2/(2*(1/2 : ℝ))= -x^2 := by ring
  have hy : -y^2/(2*(1/2 : ℝ))= -y^2 := by ring
  rw [hx,hy]
  calc
    _ = (1/Real.sqrt (2*Real.pi*(1/2 : ℝ)))*(1/Real.sqrt (2*Real.pi*(v : ℝ)))*
        Real.exp (-x^2-(y-a*x)^2/(2*(v : ℝ))) := by rw [show -x^2-(y-a*x)^2/(2*(v : ℝ)) = -x^2+(-(y-a*x)^2/(2*(v : ℝ))) by ring,Real.exp_add]; ring
    _ = (1/Real.sqrt (2*Real.pi*(1/2 : ℝ)))*(1/Real.sqrt (2*Real.pi*(v : ℝ)))*
        Real.exp (-y^2-(x-a*y)^2/(2*(v : ℝ))) := by rw [he]
    _ = _ := by rw [show -y^2-(x-a*y)^2/(2*(v : ℝ)) = -y^2+(-(x-a*y)^2/(2*(v : ℝ))) by ring,Real.exp_add]; ring

end
end GinibrePoincare
