module

public import GinibrePoincare.Analysis.ComplexGaussianDensity
public import GinibrePoincare.Analysis.MatrixOverlap

@[expose] public section

/-! # Concrete complex Ginibre matrix Gaussian law

Rows are independent product Gaussian vectors; hence all matrix entries are
independent complex Gaussians with real-coordinate variance `(2n)⁻¹`.
The density is identified explicitly with `exp (-n Tr(GG*))`.
-/
open MeasureTheory
open scoped BigOperators ENNReal

namespace GinibrePoincare
noncomputable section

@[reducible] instance ginibreMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℂ))

@[reducible] instance ginibreMatrixMeasureSpace (n : ℕ) :
    MeasureSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (MeasureSpace (Fin n → Fin n → ℂ))

def matrixGaussianProbability (n : ℕ) : ProbabilityMeasure (Matrix (Fin n) (Fin n) ℂ) :=
  ProbabilityMeasure.pi (fun _ : Fin n => complexGaussianProbability n)

def matrixGaussianMeasure (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℂ) :=
  matrixGaussianProbability n

instance matrixGaussianMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (matrixGaussianMeasure n) := by
  unfold matrixGaussianMeasure
  infer_instance

def matrixGaussianDensity (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n) *
    Real.exp (-(n : ℝ) * matrixHSNormSq G))

theorem measurable_matrixGaussianDensity (n : ℕ) : Measurable (matrixGaussianDensity n) := by
  unfold matrixGaussianDensity
  simp only [matrixHSNormSq_eq_sum]
  fun_prop

theorem matrixGaussianDensity_eq_row_product (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ) :
    matrixGaussianDensity n G = ∏ i, complexGaussianDensity n (G i) := by
  unfold matrixGaussianDensity complexGaussianDensity
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul]
    unfold gaussianWeight configurationNormSq
    rw [← Real.exp_sum]
    rw [← Finset.mul_sum, matrixHSNormSq_eq_sum]
  · intro i _
    unfold gaussianWeight
    positivity

/-- The concrete matrix Gaussian is the explicitly normalized
Hilbert--Schmidt Gaussian density. -/
theorem matrixGaussianMeasure_eq_withDensity {n : ℕ} (hn : 0 < n) :
    matrixGaussianMeasure n =
      (volume : Measure (Matrix (Fin n) (Fin n) ℂ)).withDensity (matrixGaussianDensity n) := by
  change (ProbabilityMeasure.pi (fun _ : Fin n => complexGaussianProbability n) :
    Measure (Fin n → Configuration n)) =
      (volume : Measure (Fin n → Configuration n)).withDensity (matrixGaussianDensity n)
  simp only [ProbabilityMeasure.toMeasure_pi]
  rw [show Measure.pi (fun _ : Fin n => (complexGaussianProbability n : Measure (Configuration n))) =
      Measure.pi (fun _ : Fin n => (volume : Measure (Configuration n)).withDensity (complexGaussianDensity n)) by
    congr 1
    funext i
    exact complexGaussianDensityIdentification n hn]
  have hsf : ∀ i : Fin n, SigmaFinite
      ((volume : Measure (Configuration n)).withDensity (complexGaussianDensity n)) := fun i => by
    change SigmaFinite (complexGaussianDensityMeasure n)
    rw [← complexGaussianDensityIdentification n hn]
    infer_instance
  rw [@Measure.pi_withDensity _ _ _ _ (fun _ : Fin n => (volume : Measure (Configuration n)))
    (by intro i; infer_instance) (fun _ : Fin n => complexGaussianDensity n)
    (fun _ => by unfold complexGaussianDensity gaussianWeight configurationNormSq; fun_prop) hsf,
    ← volume_pi]
  congr 1
  funext G
  exact (matrixGaussianDensity_eq_row_product n G).symm

theorem matrixGaussianMeasure_absolutelyContinuous {n : ℕ} (hn : 0 < n) :
    matrixGaussianMeasure n ≪ volume := by
  rw [matrixGaussianMeasure_eq_withDensity hn]
  exact withDensity_absolutelyContinuous _ _

@[simp] theorem matrixGaussianMeasure_univ (n : ℕ) :
    matrixGaussianMeasure n Set.univ = 1 := by simp

/-- Flattening the matrix exposes its independent entry product measure. -/
theorem matrixGaussianMeasure_uncurry_map (n : ℕ) :
    Measure.map (fun G : Matrix (Fin n) (Fin n) ℂ => fun ij : Fin n × Fin n => G ij.1 ij.2)
      (matrixGaussianMeasure n) =
        Measure.pi (fun _ : Fin n × Fin n => (complexCoordinateGaussianProbability n : Measure ℂ)) := by
  change Measure.map (Function.uncurry : (Fin n → Fin n → ℂ) → (Fin n × Fin n → ℂ))
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n =>
      (complexCoordinateGaussianProbability n : Measure ℂ)))) = _
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have hpre : (Function.uncurry : (Fin n → Fin n → ℂ) → (Fin n × Fin n → ℂ)) ⁻¹'
      Set.univ.pi s = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext G
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.uncurry_apply_pair,
      Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem matrixGaussianMeasure_uncurry_preserving (n : ℕ) :
    MeasurePreserving (fun G : Matrix (Fin n) (Fin n) ℂ => fun ij : Fin n × Fin n => G ij.1 ij.2)
      (matrixGaussianMeasure n)
        (Measure.pi (fun _ : Fin n × Fin n => (complexCoordinateGaussianProbability n : Measure ℂ))) :=
  ⟨by change Measurable (Function.uncurry : (Fin n → Fin n → ℂ) → (Fin n × Fin n → ℂ)); fun_prop,
    matrixGaussianMeasure_uncurry_map n⟩

#print axioms matrixGaussianMeasure_eq_withDensity
#print axioms matrixGaussianMeasure_absolutelyContinuous
#print axioms matrixGaussianMeasure_uncurry_map

end
end GinibrePoincare
