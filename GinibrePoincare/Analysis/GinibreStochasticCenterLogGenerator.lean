module

public import GinibrePoincare.Analysis.GinibreHamiltonianRadialGenerator
public import GinibrePoincare.Analysis.FiniteDimensionalItoScalarChain
public import GinibrePoincare.Analysis.GinibreStochasticLampertiGenerator
public import GinibrePoincare.Analysis.SumRadiusCoordinates

@[expose] public section

/-! Actual center-radius gradient and logarithmic generator. The logarithm is
used only away from zero; no regularity at a zero center is asserted. -/
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000

theorem ginibre_fderiv_centerSquared (n : ℕ) (z v : Configuration n) :
    fderiv ℝ (ginibreCenterSquared n) z v =
      2*(coordinateSum z).re*(coordinateSum v).re+
        2*(coordinateSum z).im*(coordinateSum v).im := by
  let R : Configuration n →L[ℝ] ℝ := Complex.reCLM.comp (coordinateSumCLM n)
  let I : Configuration n →L[ℝ] ℝ := Complex.imCLM.comp (coordinateSumCLM n)
  have he : ginibreCenterSquared n = fun x => R x*R x+I x*I x := by
    funext x
    simp [ginibreCenterSquared, Complex.normSq_apply, R, I, pow_two]
  rw [he]
  have hd := (((R.hasFDerivAt (x := z)).mul (R.hasFDerivAt (x := z))).add ((I.hasFDerivAt (x := z)).mul (I.hasFDerivAt (x := z)))).fderiv
  change (fderiv ℝ (⇑R*⇑R+⇑I*⇑I) z) v = _
  rw [hd]
  simp [R, I, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  <;> ring

theorem ginibre_centerSquared_gradient_normSq (n : ℕ) (z : Configuration n) :
    realGradientNormSq (ginibreCenterSquared n) z = 4*(n : ℝ)*ginibreCenterSquared n z := by
  unfold realGradientNormSq
  simp_rw [ginibre_fderiv_centerSquared]
  have hr (j : Fin n) : coordinateSum (realCoordinateDirection j : Configuration n)=1 := by
    simp [realCoordinateDirection, coordinateDirection, coordinateSum]
  have hi (j : Fin n) : coordinateSum (imaginaryCoordinateDirection j : Configuration n)=Complex.I := by
    simp [imaginaryCoordinateDirection, coordinateDirection, coordinateSum]
  simp_rw [hr, hi]
  simp [ginibreCenterSquared, Complex.normSq_apply]
  <;> ring

theorem ginibre_deriv_deriv_log {r : ℝ} (hr : 0 < r) :
    deriv (deriv Real.log) r = -(r^2)⁻¹ := by
  have he : deriv Real.log =ᶠ[nhds r] (fun x => x⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hr.ne'] with x hx
    exact (Real.hasDerivAt_log hx).deriv
  simpa [one_div] using ((hasDerivAt_id r).inv hr.ne' |>.congr_of_eventuallyEq he).deriv

theorem ginibreRealPaperSpeedGenerator_log_centerSquared {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (hpos : 0 < ginibreCenterSquared n z) :
    ginibreRealPaperSpeedGenerator n α (fun x => Real.log (ginibreCenterSquared n x)) z =
      -(4*α/(n : ℝ)) := by
  have hf : ContDiffAt ℝ 2 (ginibreCenterSquared n) z :=
    ((contDiff_ginibreCenterSquared n).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffAt
  rw [ginibreRealPaperSpeedGenerator_scalar_comp α (ginibreCenterSquared n) Real.log z hf
      (Real.contDiffAt_log.mpr hpos.ne'), (Real.hasDerivAt_log hpos.ne').deriv,
    ginibre_deriv_deriv_log hpos, ginibreRealPaperSpeedGenerator_centerSquared hn α z hz,
    ginibre_centerSquared_gradient_normSq]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp
  <;> ring
end
end GinibrePoincare
