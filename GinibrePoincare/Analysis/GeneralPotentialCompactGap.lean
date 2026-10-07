module

public import GinibrePoincare.Analysis.GeneralPotentialVandermondeEnergy
public import GinibrePoincare.Analysis.NonQuadraticPiCompactGraphApproximation

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem piCompactFunctionL2_norm_sq (d : ℕ) (f : Configuration d → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ‖piCompactFunctionL2 d f hf hc‖ ^ 2 = ∫ z, Complex.normSq (f z) := by
  have he : inner ℂ (piCompactFunctionL2 d f hf hc) (piCompactFunctionL2 d f hf hc) =
      ∫ z, inner ℂ ((piCompactFunctionL2 d f hf hc) z) ((piCompactFunctionL2 d f hf hc) z) :=
    L2.inner_def _ _
  rw [inner_self_eq_norm_sq_to_K] at he
  have ha : (piCompactFunctionL2 d f hf hc : Configuration d → ℂ) =ᵐ[volume] f :=
    (hf.memLp_of_hasCompactSupport hc).coeFn_toLp
  rw [integral_congr_ae (by filter_upwards [ha] with z hz; rw [hz])] at he
  have hi (c : ℂ) : inner ℂ c c = (Complex.normSq c : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
    exact congrArg (fun r : ℝ => (r : ℂ)) (Complex.sq_norm c)
  simp_rw [hi] at he
  rw [integral_complex_ofReal] at he
  apply Complex.ofReal_injective
  convert he using 1 <;> simp [Complex.ofReal_pow]

theorem piCompactWeightedDbarGraph_energy {d : ℕ} (n : ℕ) (V : Potential)
    (hV : Continuous V) (g : Configuration (d+1) → ℂ)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    ((List.finRange (d+1)).map (fun i =>
      ‖(piCompactWeightedDbarGraph n V hV g hg hc).2 i‖ ^ 2)).sum =
      ∫ z, ∑ i, Complex.normSq (piComplexDbar i g z * piPotentialHalfWeight (d+1) n V z) := by
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  change (∑ i, ‖piCompactFunctionL2 (d+1)
    (fun z => piComplexDbar i g z * piPotentialHalfWeight (d+1) n V z)
    ((piComplexDbar_continuous i g hg).mul (piPotentialHalfWeight_continuous (d+1) n V hV))
    (piComplexDbar_compact i g hc).mul_right‖ ^ 2) = _
  simp_rw [piCompactFunctionL2_norm_sq]
  rw [integral_finsetSum]
  intro i hi
  exact (Complex.continuous_normSq.comp ((piComplexDbar_continuous i g hg).mul
    (piPotentialHalfWeight_continuous (d+1) n V hV))).integrable_of_hasCompactSupport
      ((piComplexDbar_compact i g hc).mul_right.comp_left Complex.normSq_zero)

theorem potentialVandermonde_compact_projection_gap {d : ℕ}
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hsub : IsRhoSubharmonicPotential ρ V) (hfin : potentialPartition (d+1) V < ⊤)
    (f : Configuration (d+1) → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let g := potentialVandermondeCoefficient (d+1) V (fun z => (f z : ℂ))
    let hg := potentialVandermondeCoefficient_contDiff V _ (Complex.ofRealCLM.contDiff.comp hf)
    let hgc := potentialVandermondeCoefficient_hasCompactSupport V _
      (hc.comp_left (g := Complex.ofReal) Complex.ofReal_zero)
    let x := piCompactWeightedDbarGraph (d+1) V hV.continuous g hg hgc
    ‖x.1 - planarPiBergmanProjection (d+1) V hV x.1‖ ^ 2 ≤
      (1 / (2 * ((d+1 : ℕ) : ℝ) * ρ)) * potentialGradientEnergy (d+1) V f := by
  dsimp only
  have hfc : ContDiff ℝ 1 (fun z => (f z : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcc : HasCompactSupport (fun z => (f z : ℂ)) :=
    hc.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hgap := rhoSubharmonicPotential_pi_full_compact_gap (d+1) (by omega) V ρ hρ hV hsub
    (potentialVandermondeCoefficient (d+1) V (fun z => (f z : ℂ)))
    (potentialVandermondeCoefficient_contDiff V _ hfc)
    (potentialVandermondeCoefficient_hasCompactSupport V _ hcc)
  dsimp only at hgap
  rw [piCompactWeightedDbarGraph_energy] at hgap
  have he := potentialVandermonde_weighted_real_energy (d+1) (by omega) hV.continuous hfin f (hf.differentiable (by norm_num))
  simp only [configurationVolume] at he
  rw [he] at hgap
  convert hgap using 1 <;> ring

end
end GinibrePoincare
