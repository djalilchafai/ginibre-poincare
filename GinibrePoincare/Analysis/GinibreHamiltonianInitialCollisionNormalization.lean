module

public import GinibrePoincare.Analysis.GinibreHamiltonianGaussianCoordinateLaw
public import GinibrePoincare.Analysis.CollisionNull

@[expose] public section

open Set MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

def ginibreCollisionFreeDefault (n : ℕ) : {z : Configuration n // CollisionFree z} :=
  ⟨fun j => (j.val : ℂ), by
    intro i j hij
    apply Fin.ext
    change (i.val : ℂ) = (j.val : ℂ) at hij
    exact_mod_cast hij⟩
local instance ginibreInitialCollisionNormalization_nonempty (n : ℕ) :
    Nonempty {z : Configuration n // CollisionFree z} := ⟨ginibreCollisionFreeDefault n⟩

def ginibreInitialCollisionEmbedding (n : ℕ) :
    MeasurableEmbedding (Subtype.val : {z : Configuration n // CollisionFree z} → Configuration n) :=
  MeasurableEmbedding.subtype_coe (isOpen_collisionFree n).measurableSet

def ginibreInitialCollisionNormalize (n : ℕ) : Configuration n → {z : Configuration n // CollisionFree z} :=
  (ginibreInitialCollisionEmbedding n).invFun

theorem ginibreInitialCollisionNormalize_measurable (n : ℕ) :
    Measurable (ginibreInitialCollisionNormalize n) :=
  (ginibreInitialCollisionEmbedding n).measurable_invFun

theorem ginibreInitialCollisionNormalize_of_free {n : ℕ} (z : Configuration n) (hz : CollisionFree z) :
    ginibreInitialCollisionNormalize n z = ⟨z,hz⟩ :=
  (ginibreInitialCollisionEmbedding n).leftInverse_invFun ⟨z,hz⟩

theorem ginibreGaussian_coordinates_collisionFree_ae {n : ℕ} (hn : 0 < n) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2)),
      CollisionFree (ginibreHamiltonianOUCoordinateAssembly n x) := by
  have hCF : ∀ᵐ z ∂complexGaussianMeasure n, CollisionFree z := by
    rw [ae_iff]
    have he : {z : Configuration n | ¬ CollisionFree z} = collisionSet n := by
      ext z
      simp only [Set.mem_setOf_eq,collisionFree_iff_not_mem_collisionSet,not_not]
    rw [he]
    exact complexGaussianMeasure_collisionSet n
  have hp : MeasurePreserving (ginibreHamiltonianOUCoordinateAssembly n)
      (Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))) (complexGaussianMeasure n) :=
    ⟨(ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable,ginibreGaussian_coordinate_assembly_law hn⟩
  exact hp.quasiMeasurePreserving.ae hCF

#print axioms ginibreGaussian_coordinates_collisionFree_ae
#print axioms ginibreInitialCollisionNormalize_measurable
end
end GinibrePoincare
