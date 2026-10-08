module

public import GinibrePoincare.Analysis.MatrixGaussianPoincare
public import GinibrePoincare.Analysis.MatrixSpectralLiftLSITransport
public import GinibrePoincare.Analysis.MatrixSpectralLiftFullEntry
public import GinibrePoincare.Analysis.MatrixSpectralSobolevSpectralWeak
public import GinibrePoincare.Analysis.MatrixSpectralLiftEntryLp
public import GinibrePoincare.Analysis.MatrixSpectralSobolevWeakDomain

@[expose] public section

/-! # The Gaussian matrix route to the overlap variance inequality

Theorem 1.13: spectral pushforward, actual Gaussian matrix Poincaré inequality,
and the exact entry-gradient/overlap identity. The Ginibre Poincaré inequality
and the overlap lower-bound comparison are not invoked.
-/
open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000

/-- The paper's matrix H¹ hypothesis yields the overlap variance bound directly
from the actual Gaussian matrix Poincaré inequality. -/
theorem matrixSpectralLift_H1_gaussian_poincare {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (p : MatrixGaussianSobolevPair n) (hp : p ∈ matrixGaussianH1Completion n)
    (hv : (p.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] matrixSymmetricLift n F)
    (hd : ∀ i, (p.2 i : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
      (fun A => fderiv ℝ (matrixSymmetricLift n F) A (matrixRealCoordinates n (Pi.single i 1)))) :
    smoothGinibreVariance n F ≤
      (2/(n:ℝ))*∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  have hpi := matrixGaussianH1Completion_poincare n hn p hp
  have hvar : matrixGaussianL2Variance n p.1 = smoothGinibreVariance n F := by
    rw [matrixGaussianL2Variance_integral]
    have hv2 : (fun A => p.1 A^2) =ᵐ[matrixGaussianMeasure n]
        (fun A => matrixSymmetricLift n F A^2) := hv.mono fun _ h => congrArg (fun v : ℝ => v^2) h
    rw [integral_congr_ae hv, integral_congr_ae hv2]
    change (∫ A, F (matrixMeasurableEigenvalues n A)^2 ∂matrixGaussianMeasure n) -
      (∫ A, F (matrixMeasurableEigenvalues n A) ∂matrixGaussianMeasure n)^2 = _
    rw [matrixSpectralLift_integral hn F hF.continuous.measurable hsym,
      matrixSpectralLift_square_integral hn F hF.continuous.measurable hsym]
    letI := ginibreMeasure_isProbabilityMeasure hn
    have hFL : MemLp F 2 (ginibreMeasure n) :=
      (matrixSpectralLift_memLp_two_iff hn F hF.continuous.measurable hsym).mp
        ((Lp.memLp p.1).ae_eq hv)
    have hi := hFL.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    unfold smoothGinibreVariance smoothGinibreMean
    rw [show (fun z => (F z-(∫ x, F x ∂ginibreMeasure n))^2) =
      (fun z => F z^2 - 2*(∫ x, F x ∂ginibreMeasure n)*F z +
        (∫ x, F x ∂ginibreMeasure n)^2) by funext z; ring]
    rw [integral_add (f := fun z => F z^2 - 2*(∫ x, F x ∂ginibreMeasure n)*F z)
      (g := fun _ => (∫ x, F x ∂ginibreMeasure n)^2)
      (hFL.integrable_sq.sub (hi.const_mul _)) (integrable_const _),
      integral_sub hFL.integrable_sq (hi.const_mul _), integral_const_mul, integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    ring
  rw [hvar, matrixSpectralLift_H1_energy F hF hsym p hd] at hpi
  convert hpi using 1 <;> ring

/-- An actual ordinary weak pair for a spectral lift gives the matrix Gaussian
route, with graph membership derived from the ordinary derivative equations. -/
theorem matrixSpectralLift_ordinary_weak_gaussian_poincare {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : Configuration n → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (u : Lp ℝ 2 (matrixEntryGaussianMeasure e))
    (g : Lp (EuclideanSpace ℝ (Fin m × Fin 2)) 2 (matrixEntryGaussianMeasure e))
    (hu : (u : Configuration m → ℝ) =ᵐ[matrixEntryGaussianMeasure e]
      (fun x => matrixSymmetricLift n F (matrixComplexEntryEquiv e x)))
    (hg : (g : Configuration m → EuclideanSpace ℝ (Fin m × Fin 2)) =ᵐ[matrixEntryGaussianMeasure e]
      matrixEntryIntrinsicSpectralGradient e F)
    (hweak : ∀ i : Fin m × Fin 2, ∀ θ : Configuration m → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g x i * θ x) = -(∫ x, u x * fderiv ℝ θ x (ginibreCoordinateDirection i))) :
    smoothGinibreVariance n F ≤
      (2/(n:ℝ))*∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  let q : MatrixGaussianSobolevPair n := (matrixEntryL2ToMatrix hn e u,
    fun i => matrixEntryL2ToMatrix hn e
      ((configurationGradientComponent m ((matrixEntryRealIndexEquiv e).symm i)).compLpL
        2 (matrixEntryGaussianMeasure e) g))
  have hq : q ∈ matrixGaussianH1Completion n := matrixEntry_full_weak_pair_mem_H1Completion hn e u g hweak
  have hpres := (matrixComplexEntryEquiv_gaussian_preserving hn e).symm (matrixEntryMeasurableEquiv e)
  have hv : (q.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] matrixSymmetricLift n F := by
    filter_upwards [matrixEntryL2ToMatrix_ae hn e u, hpres.quasiMeasurePreserving.ae hu] with A hA hB
    change u ((matrixComplexEntryEquiv e).symm A) =
      matrixSymmetricLift n F (matrixComplexEntryEquiv e ((matrixComplexEntryEquiv e).symm A)) at hB
    rw [ContinuousLinearEquiv.apply_symm_apply] at hB
    exact hA.trans hB
  have hd : ∀ i, (q.2 i : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
      (fun A => fderiv ℝ (matrixSymmetricLift n F) A (matrixRealCoordinates n (Pi.single i 1))) := by
    intro i
    let j := (matrixEntryRealIndexEquiv e).symm i
    have hc := (configurationGradientComponent m j).coeFn_compLpL g
    filter_upwards [matrixEntryL2ToMatrix_ae hn e ((configurationGradientComponent m j).compLpL
      2 (matrixEntryGaussianMeasure e) g), hpres.quasiMeasurePreserving.ae hc,
      hpres.quasiMeasurePreserving.ae hg] with A hA hB hC
    change ((configurationGradientComponent m j).compLpL 2 (matrixEntryGaussianMeasure e) g)
      ((matrixComplexEntryEquiv e).symm A) = g ((matrixComplexEntryEquiv e).symm A) j at hB
    change g ((matrixComplexEntryEquiv e).symm A) =
      matrixEntryIntrinsicSpectralGradient e F ((matrixComplexEntryEquiv e).symm A) at hC
    rw [hA, hB]
    have hCj := congrArg (fun v : EuclideanSpace ℝ (Fin m × Fin 2) => v j) hC
    rw [hCj]
    change fderiv ℝ (matrixSymmetricLift n F)
      (matrixComplexEntryEquiv e ((matrixComplexEntryEquiv e).symm A))
      (matrixRealCoordinates n (Pi.single (matrixEntryRealIndexEquiv e j) 1)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact matrixSpectralLift_H1_gaussian_poincare hn F hF hsym q hq hv hd

/-- Finite actual overlap energy supplies the original matrix H¹ domain. -/
theorem matrixSpectralLift_finite_overlap_gaussian_poincare_of_entries {n d : ℕ} (hn : 0 < n)
    (e : Fin (d+1) ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n))
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    smoothGinibreVariance n F ≤
      (2/(n:ℝ))*∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  let V := fun x : Configuration (d+1) => matrixSymmetricLift n F (matrixComplexEntryEquiv e x)
  have hV : MemLp V 2 (matrixEntryGaussianMeasure e) :=
    matrixEntryIntrinsicSpectralValue_memLp hn e F hF.continuous.measurable hsym hFL2
  have hG := matrixEntryIntrinsicSpectralGradient_memLp hn e F hF hsym hE
  let u : Lp ℝ 2 (matrixEntryGaussianMeasure e) := hV.toLp V
  let g : Lp (EuclideanSpace ℝ (Fin (d+1) × Fin 2)) 2 (matrixEntryGaussianMeasure e) :=
    hG.toLp (matrixEntryIntrinsicSpectralGradient e F)
  have hu : (u : Configuration (d+1) → ℝ) =ᵐ[matrixEntryGaussianMeasure e] V := hV.coeFn_toLp
  have hg : (g : Configuration (d+1) → EuclideanSpace ℝ (Fin (d+1) × Fin 2))
      =ᵐ[matrixEntryGaussianMeasure e] matrixEntryIntrinsicSpectralGradient e F := hG.coeFn_toLp
  have hFull : matrixEntryFullSpectralLift e F =ᵐ[matrixEntryGaussianMeasure e] V := by
    filter_upwards [(matrixComplexEntryEquiv_gaussian_preserving hn e).quasiMeasurePreserving.ae
      (matrixFullSymmetricSpectralLift_eq_ae n F hsym)] with x hx
    exact hx
  have huFull := hu.trans hFull.symm
  have huVol : (u : Configuration (d+1) → ℝ) =ᵐ[volume] matrixEntryFullSpectralLift e F :=
    (matrixEntryGaussian_ae_iff_volume hn e _).mp huFull
  have hweak : ∀ i : Fin (d+1) × Fin 2, ∀ θ : Configuration (d+1) → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g x i * θ x) = -(∫ x, u x * fderiv ℝ θ x (ginibreCoordinateDirection i)) := by
    intro i θ hθ hc
    have hgScalar : (fun x => g x i) =ᵐ[matrixEntryGaussianMeasure e]
        (fun x => matrixEntryIntrinsicSpectralGradient e F x i) := by
      filter_upwards [hg] with x hx
      exact congrArg (fun v : EuclideanSpace ℝ (Fin (d+1) × Fin 2) => v i) hx
    have hder := matrixEntryFullSpectralLift_derivative_ae hn e F hF hsym i
    have hgVol : (fun x => g x i) =ᵐ[volume]
        (fun x => fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i)) :=
      (matrixEntryGaussian_ae_iff_volume hn e _).mp (hgScalar.trans hder.symm)
    have ht := matrixFullSpectralLift_coordinate_weak_test n d e F hF hsym i
      (matrixEntryFullSpectralLift_derivative_locallyIntegrable hn e F hF hsym hE i) θ hθ hc
    calc
      _ = ∫ x, fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i) * θ x := by
        apply integral_congr_ae
        filter_upwards [hgVol] with x hx
        exact congrArg (fun v : ℝ => v * θ x) hx
      _ = -(∫ x, matrixEntryFullSpectralLift e F x * fderiv ℝ θ x (ginibreCoordinateDirection i)) := ht
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [huVol] with x hx
        exact congrArg (fun v : ℝ => v * fderiv ℝ θ x (ginibreCoordinateDirection i)) hx.symm
  exact matrixSpectralLift_ordinary_weak_gaussian_poincare hn e F hF hsym u g hu hg hweak

/-- Concrete full finite-overlap Theorem 1.13 variance endpoint by the Gaussian matrix route. -/
theorem matrixSpectralLift_finite_overlap_gaussian_poincare {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n))
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    smoothGinibreVariance n F ≤
      (2/(n:ℝ))*∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  let d := n*n-1
  have hm : 1 ≤ n*n := Nat.succ_le_of_lt (Nat.mul_pos hn hn)
  let e : Fin (d+1) ≃ Fin n × Fin n := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_prod]
    exact Nat.sub_add_cancel hm)
  exact matrixSpectralLift_finite_overlap_gaussian_poincare_of_entries hn e F hF hsym hFL2 hE

#print axioms matrixSpectralLift_H1_gaussian_poincare
#print axioms matrixSpectralLift_finite_overlap_gaussian_poincare
end
end GinibrePoincare
