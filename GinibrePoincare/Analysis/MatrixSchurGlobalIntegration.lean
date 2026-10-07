module

public import GinibrePoincare.Analysis.MatrixSchurAtlasIntegration
public import GinibrePoincare.Analysis.MatrixVolumeSimpleSpectrum

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000

theorem matrixSchurAtlasChart_continuous {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℂ) : Continuous (matrixSchurAtlasChart C) := by
  have he : matrixSchurAtlasChart C = matrixUnitaryConjugation C ∘
      matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ) :=
    funext fun p => (matrixUnitaryConjugation_apply C _).symm
  rw [he]
  exact (matrixUnitaryConjugation C).continuous.comp
    (matrixSchurExponentialChart_differentiable 0).continuous

theorem matrixSchurAtlasChart_injOn {n : ℕ}
    (C : Matrix.unitaryGroup (Fin n) ℂ) (s : Set (SchurCoordinates n))
    (hi : InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ)) s) :
    InjOn (matrixSchurAtlasChart C) s := by
  intro p hp q hq he
  apply hi hp hq
  apply matrixUnitaryConjugation_injective (C : Matrix (Fin n) (Fin n) ℂ) C.property
  rw [matrixUnitaryConjugation_apply, matrixUnitaryConjugation_apply]
  change matrixSchurAtlasChart C p = matrixSchurAtlasChart C q
  exact he

/-- Global Schur integration obtained from a disjoint measurable flag atlas. The
angular constant is independent of the observable and all triangular entries. -/
theorem matrixSchur_global_integral_of_atlas {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ)) (hV : IsOpen V)
    (hinj : InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ))
      (V ×ˢ matrixSchurSortedUpperDomain n))
    (hopen : IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ |
      (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V})
    (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ)
    (hC : ∀ U : Matrix.unitaryGroup (Fin n) ℂ, ∃ k,
      ((C k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ)) ∈
        matrixUnitaryFlagSaturation n V)
    (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) (hg : Measurable g)
    (hInv : ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) :
    ∫⁻ A, g A =
      (∑' k, ∫⁻ x in matrixSchurAtlasAngularPiece V C k,
        ENNReal.ofReal (matrixSchurAngularDensity n x)) *
      ∫⁻ y in matrixSchurSortedUpperDomain n,
        ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
          g (schurUpperCombination y) := by
  letI : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  let P := fun k => matrixSchurAtlasAngularPiece V C k
  let S := fun k => matrixSchurAtlasChart (C k) '' (P k ×ˢ matrixSchurSortedUpperDomain n)
  have hP : ∀ k, MeasurableSet (P k) :=
    fun k => measurableSet_matrixSchurAtlasAngularPiece V hV C hopen k
  have hi : ∀ k, InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) 0)
      (P k ×ˢ matrixSchurSortedUpperDomain n) := by
    intro k
    apply hinj.mono
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  have hS : ∀ k, MeasurableSet (S k) := by
    intro k
    exact ((hP k).prod (measurableSet_matrixSchurSortedUpperDomain n)).image_of_continuousOn_injOn
      (@matrixSchurAtlasChart_continuous n (C k)).continuousOn
      (@matrixSchurAtlasChart_injOn n (C k) (P k ×ˢ matrixSchurSortedUpperDomain n) (hi k))
  have hcover : (⋃ k, S k) =ᵐ[volume] (Set.univ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    filter_upwards [matrixVolume_charpoly_separable_ae n] with G hG
    obtain ⟨k, p, hp, he⟩ := matrixSchurAtlas_partition_cover V C hC G hG
    change (Matrix.of G ∈ ⋃ k, S k) = True
    apply propext
    exact iff_true_intro (Set.mem_iUnion.mpr ⟨k, ⟨p, hp, he.symm⟩⟩)
  have hc := setLIntegral_congr hcover (f := g)
  rw [setLIntegral_univ] at hc
  rw [← hc, lintegral_iUnion hS (matrixSchurAtlas_partition_pairwise_disjoint V C)]
  have ht : (∑' k, ∫⁻ A in S k, g A) =
      ∑' k, (∫⁻ x in P k, ENNReal.ofReal (matrixSchurAngularDensity n x)) *
        ∫⁻ y in matrixSchurSortedUpperDomain n,
          ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
            g (schurUpperCombination y) := by
    apply tsum_congr
    intro k
    exact matrixSchurAtlas_product_integral (C k) (P k) (hP k) (hi k) g hg hInv
  rw [ht, ENNReal.tsum_mul_right]


/-- Actual global Schur integration, with one angular constant shared by every
measurable unitary-invariant observable. -/
theorem matrixSchur_global_integral (n : ℕ) :
    ∃ c : ℝ≥0∞, ∀ g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable g →
      (∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) →
      ∫⁻ A, g A = c * ∫⁻ y in matrixSchurSortedUpperDomain n,
        ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
          g (schurUpperCombination y) := by
  obtain ⟨V, hV, h0, hi, hsource, hden, hopen⟩ := matrixSchurAngularChart_exists n
  obtain ⟨C, hC⟩ := matrixUnitaryFlagSaturation_countable_cover n V h0 hopen
  refine ⟨∑' k, ∫⁻ x in matrixSchurAtlasAngularPiece V C k,
    ENNReal.ofReal (matrixSchurAngularDensity n x), ?_⟩
  intro g hg hInv
  exact matrixSchur_global_integral_of_atlas V hV hi hopen C hC g hg hInv

#print axioms matrixSchur_global_integral_of_atlas
#print axioms matrixSchur_global_integral
end
end GinibrePoincare
