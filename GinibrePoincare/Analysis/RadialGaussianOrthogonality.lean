module

public import GinibrePoincare.Analysis.GlobalPhaseAction
public import GinibrePoincare.Analysis.ComplexGaussianProductIntegral

@[expose] public section

/-! # Individual-coordinate angular cancellation for radial tests
Unlike global phase cancellation, this separates all exponent vectors.
It is the angular step in Kostlan's individual-radius factorization.
-/
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- Independent coordinate rotations. -/
def coordinatePhase {n : ℕ} (u : Fin n → ℂ) (z : Configuration n) : Configuration n :=
  fun i => u i * z i

theorem measurePreserving_coordinatePhase_gaussian (n : ℕ) (hn : 0 < n)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    MeasurePreserving (coordinatePhase u) (complexGaussianMeasure n) (complexGaussianMeasure n) := by
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  exact measurePreserving_pi _ _ (fun i => measurePreserving_complexCoordinateGaussian_mul hn (u i) (hu i))

private def coordinatePhaseEquiv (n : ℕ) (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    Configuration n ≃ᵐ Configuration n :=
  MeasurableEquiv.piCongrRight fun i => complexMulMeasurableEquiv (u i) (by
    intro he; have h := hu i; rw [he, norm_zero] at h; norm_num at h)

private theorem coordinatePhaseEquiv_apply (n : ℕ) (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (z : Configuration n) : coordinatePhaseEquiv n u hu z = coordinatePhase u z := rfl

/-- Mixed monomials tested by an arbitrary real function of individual squared radii. -/
def radialMixedIntegrand (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (a b : Fin n → ℕ) (z : Configuration n) : ℂ :=
  (F (fun i => Complex.normSq (z i)) : ℂ) * ∏ i, z i ^ a i * conj (z i) ^ b i

private theorem normSq_unit (u : ℂ) (hu : ‖u‖ = 1) : Complex.normSq u = 1 := by
  rw [← Complex.sq_norm, hu]; norm_num

private theorem radialMixedIntegrand_phase (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (a b : Fin n → ℕ) (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) (z : Configuration n) :
    radialMixedIntegrand n F a b (coordinatePhase u z) =
      (∏ i, u i ^ a i * conj (u i) ^ b i) * radialMixedIntegrand n F a b z := by
  have hr : (fun i => Complex.normSq (coordinatePhase u z i)) = fun i => Complex.normSq (z i) := by
    funext i; simp [coordinatePhase, Complex.normSq_mul, normSq_unit _ (hu i)]
  unfold radialMixedIntegrand
  rw [hr]
  simp only [coordinatePhase, mul_pow, map_mul]
  have hp : (∏ i, (u i ^ a i * z i ^ a i) * (conj (u i) ^ b i * conj (z i) ^ b i)) =
      (∏ i, u i ^ a i * conj (u i) ^ b i) * (∏ i, z i ^ a i * conj (z i) ^ b i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [hp]; ring

/-- Every off-diagonal angular term vanishes, even with a coupled radial test. -/
theorem integral_radialMixedIntegrand_eq_zero (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (a b : Fin n → ℕ) (hab : a ≠ b) :
    (∫ z, radialMixedIntegrand n F a b z ∂complexGaussianMeasure n) = 0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by
    by_contra h; push Not at h; exact hab (funext h)
  obtain ⟨v,hv,hpow⟩ := exists_unit_phase_pow_ne (a i) (b i) hi
  let u : Fin n → ℂ := fun j => if j = i then v else 1
  have hu : ∀ j, ‖u j‖ = 1 := by intro j; dsimp [u]; split_ifs <;> simp [hv]
  have hmp : MeasurePreserving (coordinatePhaseEquiv n u hu)
      (complexGaussianMeasure n) (complexGaussianMeasure n) :=
    measurePreserving_coordinatePhase_gaussian n hn u hu
  have he := hmp.integral_comp' (radialMixedIntegrand n F a b)
  simp_rw [coordinatePhaseEquiv_apply, radialMixedIntegrand_phase n F a b u hu] at he
  rw [integral_const_mul] at he
  have hchar : (∏ j, u j ^ a j * conj (u j) ^ b j) = v ^ a i * conj v ^ b i := by
    calc
      _ = u i ^ a i * conj (u i) ^ b i := by
        apply Finset.prod_eq_single i
        · intro j hj hji; simp [u,hji]
        · simp
      _ = _ := by simp [u]
  rw [hchar] at he
  have hvv : conj v * v = 1 := by
    rw [Complex.conj_mul', hv]; norm_num
  have hcancel : (v ^ a i * conj v ^ b i) * v ^ b i = v ^ a i := by
    rw [mul_assoc, ← mul_pow, hvv, one_pow, mul_one]
  have hz : (v ^ a i - v ^ b i) * (∫ z, radialMixedIntegrand n F a b z ∂complexGaussianMeasure n) = 0 := by
    have hc := congrArg (fun t : ℂ => v ^ b i * t) he
    rw [show v ^ b i * ((v ^ a i * conj v ^ b i) *
        (∫ z, radialMixedIntegrand n F a b z ∂complexGaussianMeasure n)) =
      v ^ a i * (∫ z, radialMixedIntegrand n F a b z ∂complexGaussianMeasure n) by
        rw [← mul_assoc, mul_comm (v ^ b i), hcancel]] at hc
    linear_combination hc
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hpow)

end
end GinibrePoincare
