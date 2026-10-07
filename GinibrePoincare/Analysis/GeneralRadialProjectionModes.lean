module

public import GinibrePoincare.Analysis.GeneralRadialProjectionPhase
public import GinibrePoincare.Analysis.GeneralRadialProjectionCharacters
public import Mathlib.Analysis.Convex.Integral

@[expose] public section

open MeasureTheory Set
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem planarLebesguePhase_comp (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (u : PlanarLebesgueL2) :
    planarLebesguePhase a ha (planarLebesguePhase b hb u) =
      planarLebesguePhase (b * a) (by rw [norm_mul, ha, hb, one_mul]) u := by
  let mpa := measurePreserving_complex_mul_of_norm_one a ha
  let mpb := measurePreserving_complex_mul_of_norm_one b hb
  let mpba := measurePreserving_complex_mul_of_norm_one (b * a)
    (by rw [norm_mul, ha, hb, one_mul])
  change Lp.compMeasurePreserving (fun z : ℂ => a * z) mpa
    (Lp.compMeasurePreserving (fun z : ℂ => b * z) mpb u) =
    Lp.compMeasurePreserving (fun z : ℂ => (b * a) * z) mpba u
  have h := Lp.compMeasurePreserving_comp_apply u mpb mpa
  have he : ((fun z : ℂ => b * z) ∘ (fun z : ℂ => a * z)) =
      (fun z : ℂ => (b * a) * z) := by
    funext z
    exact (mul_assoc b a z).symm
  simpa only [he] using h.symm

def planarRotationCoefficient {T : ℝ} [Fact (0 < T)]
    (u : PlanarLebesgueL2) (k : ℤ) : PlanarLebesgueL2 :=
  fourierCoeff (fun t : AddCircle T =>
    planarLebesguePhase (AddCircle.toCircle t) (Circle.norm_coe _) u) k

theorem planarRotationCoefficient_eigen {T : ℝ} [Fact (0 < T)]
    (u : PlanarLebesgueL2) (k : ℤ) (s : AddCircle T) :
    planarLebesguePhase (AddCircle.toCircle s) (Circle.norm_coe _)
      (planarRotationCoefficient (T := T) u k) =
    fourier k s • planarRotationCoefficient (T := T) u k := by
  unfold planarRotationCoefficient
  apply circle_orbit_fourierCoeff_eigen (fun t : AddCircle T =>
    planarLebesguePhase (AddCircle.toCircle t) (Circle.norm_coe _)) u
  · exact planarLebesguePhase_circle_continuous u
  · intro s t
    rw [planarLebesguePhase_comp]
    have he : (AddCircle.toCircle t : ℂ) * (AddCircle.toCircle s : ℂ) =
        (AddCircle.toCircle (t + s) : ℂ) := congrArg Subtype.val (AddCircle.toCircle_add t s).symm
    simp only [he]

theorem planarRotationCoefficient_mem_bergman {T : ℝ} [Fact (0 < T)]
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a * z) = V z)
    (u : PlanarLebesgueL2) (hu : u ∈ planarBergmanKernel n V hV) (k : ℤ) :
    planarRotationCoefficient (T := T) u k ∈ planarBergmanKernel n V hV := by
  let K := planarBergmanKernelClosed n V hV
  apply (K.toSubmodule.restrictScalars ℝ).convex.integral_mem K.isClosed
  · exact Filter.Eventually.of_forall fun t => K.toSubmodule.smul_mem _
      (planarLebesguePhase_preserves_bergman n V hV hr _ (Circle.norm_coe _) u hu)
  · exact ((planarLebesguePhase_circle_continuous (T := T) u).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).fourier_smul (-k)

end
end GinibrePoincare
