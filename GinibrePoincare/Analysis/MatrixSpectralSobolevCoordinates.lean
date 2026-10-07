module

public import GinibrePoincare.Analysis.MatrixSchurEntryVolume
public import GinibrePoincare.Analysis.MatrixGaussianH1Closure
public import GinibrePoincare.Analysis.MatrixSpectralSobolevFullWeightedDomain

@[expose] public section

/-! # Actual entry-coordinate and L² transports for spectral Sobolev domains -/
open MeasureTheory Matrix
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def matrixComplexEntryEquiv {n m : ℕ} (e : Fin m ≃ Fin n × Fin n) :
    Configuration m ≃L[ℝ] MatrixRealSpace n where
  toFun z := fun i j => z (e.symm (i, j))
  invFun A := fun k => A (e k).1 (e k).2
  left_inv z := by funext k; simp
  right_inv A := by funext i j; simp
  map_add' z w := rfl
  map_smul' c z := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def matrixUncurryMeasurableEquiv (n : ℕ) :
    MatrixRealSpace n ≃ᵐ (Fin n × Fin n → ℂ) where
  toFun := Function.uncurry
  invFun := Function.curry
  left_inv A := rfl
  right_inv A := rfl
  measurable_toFun := by
    change Measurable (Function.uncurry : MatrixRealSpace n → (Fin n × Fin n → ℂ))
    fun_prop
  measurable_invFun := by
    change Measurable (Function.curry : (Fin n × Fin n → ℂ) → MatrixRealSpace n)
    fun_prop

theorem matrixComplexEntryEquiv_volume_preserving {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) :
    MeasurePreserving (matrixComplexEntryEquiv e)
      (volume : Measure (Configuration m)) (volume : Measure (MatrixRealSpace n)) := by
  have h₁ := measurePreserving_piCongrLeft
    (fun _ : Fin n × Fin n => (volume : Measure ℂ)) e
  have h₂ := (matrixVolume_uncurry_preserving n).symm (matrixUncurryMeasurableEquiv n)
  convert h₂.comp h₁ using 1
  all_goals try rfl
  funext z i j
  simp [matrixComplexEntryEquiv, matrixUncurryMeasurableEquiv,
    MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

/-- Every actual measure preserving coordinate equivalence yields a genuine
real L² isometry equivalence in the pullback direction. -/
def realL2CoordinatePullbackEquiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) :
    Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℝ e he) (by
    intro F
    refine ⟨Lp.compMeasurePreserving e.symm (he.symm e) F, ?_⟩
    change Lp.compMeasurePreserving e he
      (Lp.compMeasurePreserving e.symm (he.symm e) F) = F
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hi : (e.symm : Y → X) ∘ e = id := by funext x; exact e.symm_apply_apply x
    simp only [hi, Lp.compMeasurePreserving_id_apply])

end
end GinibrePoincare
