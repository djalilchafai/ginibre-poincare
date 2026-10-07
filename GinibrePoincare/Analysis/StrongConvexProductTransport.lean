module

public import GinibrePoincare.Analysis.StrongConvexRadialTransport
public import GinibrePoincare.Analysis.GaussianPiCoordinates
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ContDiff BigOperators NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I : Type*} [Fintype I] [DecidableEq I]

def coordinateQuantileTransport (T : I → ℝ → ℝ) (x : I → ℝ) : I → ℝ := fun i => T i (x i)

theorem coordinateQuantileTransport_contDiff (T : I → ℝ → ℝ)
    (hT : ∀ i, ContDiff ℝ 1 (T i)) : ContDiff ℝ 1 (coordinateQuantileTransport T) := by
  apply contDiff_pi.mpr
  intro i
  exact (hT i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) i).contDiff

theorem coordinateQuantileTransport_measurePreserving (T : I → ℝ → ℝ)
    (ν : I → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hT : ∀ i, Measurable (T i)) (hmap : ∀ i, (gaussianReal 0 1).map (T i) = ν i) :
    MeasurePreserving (coordinateQuantileTransport T)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) (Measure.pi ν) := by
  exact measurePreserving_pi _ _ (fun i => ⟨hT i, hmap i⟩)

theorem coordinateQuantileTransport_fderiv_direction (T : I → ℝ → ℝ)
    (hT : ∀ i, ContDiff ℝ 1 (T i)) (x : I → ℝ) (i : I) :
    fderiv ℝ (coordinateQuantileTransport T) x (Pi.single i 1) =
      deriv (T i) (x i) • Pi.single i 1 := by
  classical
  have hd (j : I) : DifferentiableAt ℝ (fun x : I → ℝ => T j (x j)) x :=
    (hT j).differentiable (by norm_num) (x j) |>.comp x (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) j).differentiableAt
  rw [show coordinateQuantileTransport T = (fun x j => T j (x j)) from rfl,
    fderiv_pi hd]
  ext j
  simp only [ContinuousLinearMap.pi_apply, Pi.smul_apply, smul_eq_mul]
  change fderiv ℝ (T j ∘ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) j)) x
    (Pi.single i 1) = _
  rw [fderiv_comp x ((hT j).differentiable (by norm_num) (x j))
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) j).differentiableAt,
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) j).hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    fderiv_eq_smul_deriv, smul_eq_mul, Pi.single_apply]
  by_cases h : j = i
  · subst j; simp
  · simp [h]

theorem coordinateQuantileTransport_energy (T : I → ℝ → ℝ)
    (hT : ∀ i, ContDiff ℝ 1 (T i)) (L : ℝ)
    (hb : ∀ i x, |deriv (T i) x| ≤ L)
    (f : (I → ℝ) → ℝ) (hf : Differentiable ℝ f) (x : I → ℝ) :
    directionalEnergy (fun i : I => Pi.single i 1) (f ∘ coordinateQuantileTransport T) x ≤
      L ^ 2 * directionalEnergy (fun i : I => Pi.single i 1) f (coordinateQuantileTransport T x) := by
  rw [directionalEnergy, directionalEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [fderiv_comp x (hf _) ((coordinateQuantileTransport_contDiff T hT).differentiable (by norm_num) x)]
  simp only [ContinuousLinearMap.comp_apply, coordinateQuantileTransport_fderiv_direction T hT,
    map_smul, smul_eq_mul, mul_pow]
  have hL : 0 ≤ L := (abs_nonneg (deriv (T i) (x i))).trans (hb i (x i))
  have hsq : (deriv (T i) (x i)) ^ 2 ≤ L ^ 2 := by
    nlinarith [hb i (x i), sq_abs (deriv (T i) (x i)), abs_nonneg (deriv (T i) (x i))]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

theorem coordinateQuantileTransport_lipschitz (T : I → ℝ → ℝ)
    (hT : ∀ i, ContDiff ℝ 1 (T i)) (L : ℝ≥0)
    (hb : ∀ i x, |deriv (T i) x| ≤ (L : ℝ)) :
    LipschitzWith L (coordinateQuantileTransport T) := by
  have hl (i : I) : LipschitzWith L (T i) := by
    apply lipschitzWith_of_nnnorm_fderiv_le ((hT i).differentiable (by norm_num))
    intro x
    apply NNReal.coe_le_coe.mp
    change ‖fderiv ℝ (T i) x‖ ≤ (L : ℝ)
    rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]
    exact hb i x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
  intro i
  exact ((hl i).dist_le_mul (x i) (y i)).trans
    (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) L.coe_nonneg)

#print axioms coordinateQuantileTransport_lipschitz
#print axioms coordinateQuantileTransport_energy
#print axioms coordinateQuantileTransport_measurePreserving
end
end GinibrePoincare
