module

public import GinibrePoincare.Analysis.AlternativeBochnerKodairaCutoff

@[expose] public section

/-! # Gaussian adjoint pairing beyond compact tests

This expands the Gaussian integration-by-parts step in (6.8). Radial cutoff
errors are proved to vanish, so the pairing applies to polynomial tests.
-/
open MeasureTheory Filter
open scoped ContDiff ComplexConjugate BigOperators Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem bkAdjoint_cutoff_tendsto {n : ℕ}
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f) (j : Fin n)
    (hA : MemLp (gaussianDbarAdjointTest j f) 2 (complexGaussianMeasure n))
    (hZ : MemLp (fun z => conj (z j) * f z) 2 (complexGaussianMeasure n)) :
    let F := fun m z => (ginibreSpatialCutoff n m z : ℂ) * f z
    let hF : ∀ m, ContDiff ℝ ∞ (F m) := fun m => (Complex.ofRealCLM.contDiff.comp (ginibreSpatialCutoff_smooth n m)).mul hf
    let hcF : ∀ m, HasCompactSupport (F m) := fun m => ((ginibreSpatialCutoff_compact n m).comp_left Complex.ofReal_zero).mul_right (f' := f)
    Tendsto (fun m => gaussianDbarAdjointTestL2 j (F m) ((hF m).of_le (by simp)) (hcF m))
      atTop (𝓝 (hA.toLp (gaussianDbarAdjointTest j f))) := by
  dsimp only
  have hFs (m : ℕ) : ContDiff ℝ ∞ (fun z : Configuration n => (ginibreSpatialCutoff n m z : ℂ) * f z) :=
    (Complex.ofRealCLM.contDiff.comp (ginibreSpatialCutoff_smooth n m)).mul hf
  have hFc (m : ℕ) : HasCompactSupport (fun z : Configuration n => (ginibreSpatialCutoff n m z : ℂ) * f z) :=
    ((ginibreSpatialCutoff_compact n m).comp_left Complex.ofReal_zero).mul_right
  let A := fun m => (gaussianSpatialCutoff_value_memLp (gaussianDbarAdjointTest j f) hA m).toLp
    (fun z => (ginibreSpatialCutoff n m z : ℂ) * gaussianDbarAdjointTest j f z)
  let B := fun m => (gaussianSpatialCutoff_derivativeTerm_memLp (fun z => conj (z j) * f z) hZ m).toLp
    (fun z => ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) * (conj (z j) * f z))
  have he (m : ℕ) : gaussianDbarAdjointTestL2 j
      (fun z => (ginibreSpatialCutoff n m z : ℂ) * f z)
      ((hFs m).of_le (by simp))
      (hFc m) = A m - B m := by
    apply Lp.ext
    filter_upwards [(gaussianDbarAdjointTest_memLp j
        (fun z => (ginibreSpatialCutoff n m z : ℂ) * f z)
        ((hFs m).of_le (by simp))
        (hFc m)).coeFn_toLp,
      Lp.coeFn_sub (A m) (B m),
      (gaussianSpatialCutoff_value_memLp (gaussianDbarAdjointTest j f) hA m).coeFn_toLp,
      (gaussianSpatialCutoff_derivativeTerm_memLp (fun z => conj (z j) * f z) hZ m).coeFn_toLp]
        with z h0 h1 h2 h3
    change (gaussianDbarAdjointTestL2 j
      (fun z => (ginibreSpatialCutoff n m z : ℂ) * f z) ((hFs m).of_le (by simp)) (hFc m) : Configuration n → ℂ) z = _ at h0
    change (A m : Configuration n → ℂ) z = _ at h2
    change (B m : Configuration n → ℂ) z = _ at h3
    rw [h0, h1, Pi.sub_apply, h2, h3]
    exact bkAdjoint_cutoff_product m hf j z
  have hAt := gaussianSpatialCutoff_value_tendsto (gaussianDbarAdjointTest j f) hA
    (gaussianSpatialCutoff_value_memLp (gaussianDbarAdjointTest j f) hA)
  have hBt := gaussianSpatialCutoff_derivativeTerm_tendsto (fun z => conj (z j) * f z) hZ
  simpa only [he, sub_zero] using hAt.sub hBt

/-- Actual Gaussian IBP for arbitrary smooth L² values and polynomial-size
tests. All cutoff boundary terms are proved to vanish. -/
theorem bkGaussian_adjoint_pairing {n : ℕ} (hn : 0 < n) (j : Fin n)
    (f g : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hF : MemLp f 2 (complexGaussianMeasure n))
    (hD : MemLp (dbarComponent f j) 2 (complexGaussianMeasure n))
    (hG : MemLp g 2 (complexGaussianMeasure n))
    (hA : MemLp (gaussianDbarAdjointTest j g) 2 (complexGaussianMeasure n))
    (hZ : MemLp (fun z => conj (z j) * g z) 2 (complexGaussianMeasure n)) :
    inner ℂ (hG.toLp g) (hD.toLp (dbarComponent f j)) =
      inner ℂ (hA.toLp (gaussianDbarAdjointTest j g)) (hF.toLp f) := by
  let G := fun m z => (ginibreSpatialCutoff n m z : ℂ) * g z
  have hGs (m : ℕ) : ContDiff ℝ ∞ (G m) :=
    (Complex.ofRealCLM.contDiff.comp (ginibreSpatialCutoff_smooth n m)).mul hg
  have hGc (m : ℕ) : HasCompactSupport (G m) :=
    ((ginibreSpatialCutoff_compact n m).comp_left Complex.ofReal_zero).mul_right
  have hweak := gaussian_smooth_weak_dbar hn j (hF.toLp f) (hD.toLp (dbarComponent f j)) f
    (hf.of_le (by simp)) hF.coeFn_toLp hD.coeFn_toLp
  have hpair (m : ℕ) := hweak (G m) ((hGs m).of_le (by simp)) (hGc m)
  have hleft : Tendsto (fun m => smoothCompactL2 (G m) ((hGs m).of_le (by simp)) (hGc m))
      atTop (𝓝 (hG.toLp g)) := by
    have he (m : ℕ) : smoothCompactL2 (G m) ((hGs m).of_le (by simp)) (hGc m) =
        (gaussianSpatialCutoff_value_memLp g hG m).toLp (G m) := by
      apply Lp.ext
      exact (smoothCompactL2_coeFn (G m) ((hGs m).of_le (by simp)) (hGc m)).trans
        (gaussianSpatialCutoff_value_memLp g hG m).coeFn_toLp.symm
    simpa only [he] using gaussianSpatialCutoff_value_tendsto g hG
      (gaussianSpatialCutoff_value_memLp g hG)
  have hright := bkAdjoint_cutoff_tendsto g hg j hA hZ
  exact tendsto_nhds_unique ((hleft.inner tendsto_const_nhds).congr (fun m => hpair m))
    (hright.inner tendsto_const_nhds)

/-- The extended pairing with specified actual L² representatives. -/
theorem bkGaussian_adjoint_pairing_representatives {n : ℕ} (hn : 0 < n) (j : Fin n)
    (f g : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (F D G A : Lp ℂ 2 (complexGaussianMeasure n))
    (hF : (F : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] f)
    (hD : (D : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] dbarComponent f j)
    (hG : (G : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] g)
    (hA : (A : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] gaussianDbarAdjointTest j g)
    (hZ : MemLp (fun z => conj (z j) * g z) 2 (complexGaussianMeasure n)) :
    inner ℂ G D = inner ℂ A F := by
  have hfL := (memLp_congr_ae hF).mp (Lp.memLp F)
  have hdL := (memLp_congr_ae hD).mp (Lp.memLp D)
  have hgL := (memLp_congr_ae hG).mp (Lp.memLp G)
  have haL := (memLp_congr_ae hA).mp (Lp.memLp A)
  have heF : hfL.toLp f = F := by apply Lp.ext; exact hfL.coeFn_toLp.trans hF.symm
  have heD : hdL.toLp (dbarComponent f j) = D := by apply Lp.ext; exact hdL.coeFn_toLp.trans hD.symm
  have heG : hgL.toLp g = G := by apply Lp.ext; exact hgL.coeFn_toLp.trans hG.symm
  have heA : haL.toLp (gaussianDbarAdjointTest j g) = A := by apply Lp.ext; exact haL.coeFn_toLp.trans hA.symm
  simpa only [heF, heD, heG, heA] using
    bkGaussian_adjoint_pairing hn j f g hf hg hfL hdL hgL haL hZ

end
end GinibrePoincare

#print axioms GinibrePoincare.bkGaussian_adjoint_pairing

#print axioms GinibrePoincare.bkAdjoint_cutoff_tendsto

#print axioms GinibrePoincare.bkGaussian_adjoint_pairing_representatives
