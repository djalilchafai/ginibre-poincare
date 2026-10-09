module
public import GinibrePoincare.Analysis.CorrespondenceCurvatureGradient
@[expose] public section
open Set Filter
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem correspondence_configurationNormSq_hessian {n : ℕ} (z v w : Configuration n) :
    fderiv ℝ (fderiv ℝ configurationNormSq) z v w =
      2*∑ j, (conj (v j)*w j).re := by
  rw [← bochnerDirectionalDerivative_iterated v w configurationNormSq z contDiff_configurationNormSq.contDiffAt]
  have he : bochnerDirectionalDerivative w configurationNormSq =
      fun x : Configuration n => 2*∑ j, (conj (x j)*w j).re := by
    funext x
    exact fderiv_configurationNormSq_apply x w
  rw [he]
  let L : Configuration n →L[ℝ] ℝ :=
    2 • ∑ j, (Complex.reCLM.comp (((ContinuousLinearMap.mul ℝ ℂ).flip (w j)).comp
      (Complex.conjCLE.toContinuousLinearMap.comp
        (ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ))))
  have heL : (fun x : Configuration n => 2*∑ j, (conj (x j)*w j).re) = L := by
    funext x
    simp [L, mul_comm]
  rw [heL]
  unfold bochnerDirectionalDerivative
  rw [L.fderiv]
  simp [L, mul_comm]

theorem correspondence_hamiltonian_interaction_hessian {n : ℕ}
    (z v w : Configuration n) (hz : CollisionFree z) :
    fderiv ℝ (fderiv ℝ (ginibreHamiltonian n)) z v w =
      2*(n : ℝ)*(∑ j, (conj (v j)*w j).re) +
        fderiv ℝ (fderiv ℝ (ginibreInteractionPotential n)) z v w := by
  have hQ := contDiff_configurationNormSq (n := n)
  have hI := ginibreInteractionPotential_contDiffAt n z hz
  have hH : ginibreHamiltonian n =
      fun x => (n : ℝ)*configurationNormSq x + ginibreInteractionPotential n x := by
    funext x
    simp only [ginibreHamiltonian, ginibreInteractionPotential, sub_eq_add_neg]
  have he : fderiv ℝ (ginibreHamiltonian n) =ᶠ[𝓝 z]
      (fun x => (n : ℝ) • fderiv ℝ configurationNormSq x +
        fderiv ℝ (ginibreInteractionPotential n) x) := by
    filter_upwards [(isOpen_collisionFree n).mem_nhds hz] with x hx
    rw [hH]
    have hh := ((hQ.differentiable (by simp)).differentiableAt.hasFDerivAt.fun_const_smul (n : ℝ)).fun_add
      (((ginibreInteractionPotential_contDiffAt n x hx).differentiableAt (by simp)).hasFDerivAt)
    simpa only [Pi.add_apply, smul_eq_mul] using hh.fderiv
  rw [he.fderiv_eq]
  have hQD := (hQ.contDiffAt.fderiv_right (m := ∞) (by simp)).differentiableAt (x := z) (by simp)
  have hID := (hI.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [fderiv_fun_add (hQD.fun_const_smul (n : ℝ)) hID,
    fderiv_fun_const_smul hQD (n : ℝ)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [correspondence_configurationNormSq_hessian]
  ring

#print axioms correspondence_hamiltonian_interaction_hessian
#print axioms correspondence_configurationNormSq_hessian
end
end GinibrePoincare
