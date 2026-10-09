module
public import GinibrePoincare.Analysis.CorrespondenceGUESymmetricSpatialApproximation
@[expose] public section
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem gueL2_toLp_dist_eq_sqrt {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (f g : EuclideanSpace ℝ (Fin n) → F) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g)=Real.sqrt (∫x, ‖f x-g x‖^2 ∂μ) := by
  have he : (∫x, ‖f x-g x‖^2 ∂μ)=‖hf.toLp f-hg.toLp g‖^2 := by
    rw [← integral_norm_sq_eq_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp] with x hx hfx hgx
    simp only [hx, Pi.sub_apply, hfx, hgx]
  rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), dist_eq_norm]

theorem gueSymmetric_C1_pair_mem_H1Completion {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : ∀σ x, f (guePermute n σ x)=f x)
    (hv : MemLp f 2 (gueFullMeasure n))
    (hg : MemLp (gradient f) 2 (gueFullMeasure n)) :
    (hv.toLp f, hg.toLp (gradient f))∈gueSymmetricH1Completion n := by
  letI := gueFullMeasure_probability hn
  let μ := gueFullMeasure n
  let F := fun k => gueSymmetricSpatialTruncation n k f
  have hFC k : ContDiff ℝ 1 (F k) := gueSymmetricSpatialTruncation_contDiff n k f hf
  have hFS k : HasCompactSupport (F k) := gueSymmetricSpatialTruncation_compact n k f
  have hFV k : MemLp (F k) 2 μ := (hFC k).continuous.memLp_of_hasCompactSupport (hFS k)
  have hFG k : MemLp (gradient (F k)) 2 μ := by
    have hgc : Continuous (gradient (F k)) :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
        ((hFC k).fderiv_right (m := 0) (by norm_num)).continuous
    exact hgc.memLp_of_hasCompactSupport ((hFS k).fderiv ℝ |>.comp_left
      (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm) (map_zero _))
  have hD i : MemLp (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)) 2 μ := by
    have h := memLp_piLp_iff.mp hg i
    have he : (fun x => (gradient f x) i)=(fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
      funext (fun x => gue_gradient_coordinate f x i)
    rwa [he] at h
  have hDE k i : Integrable (fun x => (fderiv ℝ (F k) x (EuclideanSpace.basisFun (Fin n) ℝ i)-
      fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i))^2) μ := by
    have h := memLp_piLp_iff.mp (hFG k) i
    have he : (fun x => (gradient (F k) x) i)=(fun x => fderiv ℝ (F k) x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
      funext (fun x => gue_gradient_coordinate (F k) x i)
    rw [he] at h
    exact (h.sub (hD i)).integrable_sq
  have htV : Tendsto (fun k => (hFV k).toLp (F k)) atTop (nhds (hv.toLp f)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp_rw [gueL2_toLp_dist_eq_sqrt, Real.norm_eq_abs, sq_abs]
    simpa [F] using (gueSymmetricSpatialTruncation_L2_errors n μ f hf hv 0 (by simp)).1.sqrt
  have htG : Tendsto (fun k => (hFG k).toLp (gradient (F k))) atTop (nhds (hg.toLp (gradient f))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp_rw [gueL2_toLp_dist_eq_sqrt]
    have he k : (∫x, ‖gradient (F k) x-gradient f x‖^2 ∂μ)=
        ∑i,∫x, (fderiv ℝ (F k) x (EuclideanSpace.basisFun (Fin n) ℝ i)-
          fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i))^2 ∂μ := by
      simp only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, gue_gradient_coordinate]
      exact integral_finsetSum _ (fun i hi => hDE k i)
    simp_rw [he]
    have ht := tendsto_finsetSum Finset.univ (fun i hi =>
      (gueSymmetricSpatialTruncation_L2_errors n μ f hf hv (EuclideanSpace.basisFun (Fin n) ℝ i) (hD i)).2)
    simpa [F] using ht.sqrt
  apply isClosed_closure.mem_of_tendsto (htV.prodMk_nhds htG)
  apply Eventually.of_forall
  intro k
  apply subset_closure
  refine ⟨F k, hFC k, hFS k,?_, (hFV k).coeFn_toLp, (hFG k).coeFn_toLp⟩
  intro σ x
  unfold F gueSymmetricSpatialTruncation
  rw [gueSymmetricSpatialCutoff_symmetric, hs]

#print axioms gueSymmetric_C1_pair_mem_H1Completion
end
end GinibrePoincare
