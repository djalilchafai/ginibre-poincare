module
public import GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungTranslation

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def dolbeaultCoordinateConvolution {n : ℕ} (j : Fin n) (k : ℂ → ℂ)
    (u : dolbeaultOrdinaryL2 n) : dolbeaultOrdinaryL2 n :=
  ∫ y : ℂ, k y • dolbeaultTranslateL2 j y u

theorem dolbeaultCoordinateConvolution_integrable {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) (u : dolbeaultOrdinaryL2 n) :
    Integrable (fun y : ℂ => k y • dolbeaultTranslateL2 j y u) volume := by
  have hm := hk.aestronglyMeasurable.smul (dolbeaultTranslateL2_continuous j u).aestronglyMeasurable
  apply (hk.norm.mul_const ‖u‖).mono' hm
  exact ae_of_all _ (fun y => by
    change ‖k y • dolbeaultTranslateL2 j y u‖ ≤ _
    rw [norm_smul,dolbeaultTranslateL2_norm])

/-- Genuine coordinate Young bound on ordinary Lebesgue L² in arbitrary dimension. -/
theorem dolbeaultCoordinateConvolution_norm {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (u : dolbeaultOrdinaryL2 n) :
    ‖dolbeaultCoordinateConvolution j k u‖ ≤ (∫ y : ℂ, ‖k y‖)*‖u‖ := by
  unfold dolbeaultCoordinateConvolution
  calc
    _ ≤ ∫ y : ℂ, ‖k y • dolbeaultTranslateL2 j y u‖ := norm_integral_le_integral_norm _
    _ = _ := by simp_rw [norm_smul,dolbeaultTranslateL2_norm]; rw [integral_mul_const]

def dolbeaultCoordinateConvolutionLinear {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) :
    dolbeaultOrdinaryL2 n →ₗ[ℂ] dolbeaultOrdinaryL2 n where
  toFun := dolbeaultCoordinateConvolution j k
  map_add' u v := by
    unfold dolbeaultCoordinateConvolution
    simp only [map_add,smul_add]
    exact integral_add (dolbeaultCoordinateConvolution_integrable j k hk u)
      (dolbeaultCoordinateConvolution_integrable j k hk v)
  map_smul' c u := by
    unfold dolbeaultCoordinateConvolution
    simp only [map_smul,smul_smul]
    simp_rw [mul_comm (k _) c]
    simp_rw [← smul_smul]
    rw [integral_smul]
    rfl

def dolbeaultCoordinateConvolutionCLM {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  (dolbeaultCoordinateConvolutionLinear j k hk).mkContinuous (∫ y : ℂ, ‖k y‖)
    (dolbeaultCoordinateConvolution_norm j k)

/-- Every bounded ordinary-L² test functional commutes with the actual convolution. -/
theorem dolbeaultCoordinateConvolution_pairing {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) (u : dolbeaultOrdinaryL2 n)
    (T : dolbeaultOrdinaryL2 n →L[ℂ] ℂ) :
    T (dolbeaultCoordinateConvolution j k u) =
      ∫ y : ℂ, k y*T (dolbeaultTranslateL2 j y u) := by
  rw [dolbeaultCoordinateConvolution,← T.integral_comp_comm
    (dolbeaultCoordinateConvolution_integrable j k hk u)]
  simp only [map_smul,smul_eq_mul]

#print axioms dolbeaultCoordinateConvolution_integrable
#print axioms dolbeaultCoordinateConvolution_norm
#print axioms dolbeaultCoordinateConvolutionCLM
#print axioms dolbeaultCoordinateConvolution_pairing
end
end GinibrePoincare
