module
public import GinibrePoincare.Analysis.CorrespondenceOperatorZeroGradientLocal
public import GinibrePoincare.Analysis.CorrespondenceOperatorConnected
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Compactness.Lindelof
@[expose] public section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
/-- Every genuine ordinary weak zero-gradient function on the full Ginibre
space is almost everywhere constant. No permutation symmetry is assumed. -/
theorem correspondenceOperator_zero_gradient_constant {n : ℕ} (hn : 0<n)
    (u : GinibreFullValueL2 n) (hu : IsGinibreDistributionalGradient n u 0) :
    ∃ c : ℝ, u=ginibreRealConstantL2 n hn c := by
  classical
  let U : Set (Configuration n) := {z | CollisionFree z}
  have hU : IsOpen U := isOpen_collisionFree n
  have hex (x : U) : ∃ r : ℝ, 0<r ∧ closedBall x.val (3*r)⊆U := by
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hU x.val x.property
    refine ⟨δ/4, by positivity,?_⟩
    intro y hy
    apply hsub
    change dist y x.val<δ
    have hy' : dist y x.val≤3*(δ/4) := hy
    linarith
  choose r hr hball using hex
  choose c hc using (fun x : U => correspondenceOperator_zero_gradient_local_constant
    hn u hu x.val (r x) (hr x) (hball x))
  have hlocal : IsLocallyConstant c := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    have hnhood : {y : U | y.val∈ball x.val (r x)}∈𝓝 x :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds x.val (hr x))
    filter_upwards [hnhood] with y hy
    let E := ball x.val (r x)∩ball y.val (r y)
    have hE : IsOpen E := isOpen_ball.inter isOpen_ball
    have hnon : E.Nonempty := ⟨y.val, hy, mem_ball_self (hr y)⟩
    have hpos : (volume : Measure (Configuration n)) E≠0 := (hE.measure_pos volume hnon).ne'
    have hae : ∀ᵐ z ∂(volume : Measure (Configuration n)).restrict E, c y=c x := by
      filter_upwards [ae_restrict_of_ae (hc x), ae_restrict_of_ae (hc y),
        ae_restrict_mem hE.measurableSet] with z hx hy hz
      exact (hy hz.2).symm.trans (hx hz.1)
    obtain ⟨_, _, hh⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos hae
    exact hh
  haveI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
    (correspondenceOperator_collisionFree_isPathConnected n).isConnected.isPreconnected
  obtain ⟨a, ha⟩ := hlocal.exists_eq_const
  have hca (x : U) : c x=a := congrFun ha x
  let B : U→Set (Configuration n) := fun x => ball x.val (r x)
  have hcover : U⊆⋃ x : U, B x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨S, hSc, hScov⟩ := (show IsLindelof U from IsLindelof.of_coe).elim_countable_subcover
    B (fun _ => isOpen_ball) hcover
  have hae : ∀ᵐ z ∂(volume : Measure (Configuration n)), z∈U→u z=a := by
    have hnull (x : U) : ∀ᵐ z ∂(volume : Measure (Configuration n)).restrict (B x), u z=a := by
      apply (ae_restrict_iff' isOpen_ball.measurableSet).mpr
      filter_upwards [hc x] with z hz hmem
      exact (hz hmem).trans (hca x)
    have hOn : ∀ᵐ z ∂(volume : Measure (Configuration n)).restrict (⋃ x∈S, B x), u z=a :=
      (ae_restrict_biUnion_iff B hSc _).mpr (fun x _ => hnull x)
    have he := (ae_restrict_iff' (MeasurableSet.biUnion hSc (fun _ _ => isOpen_ball.measurableSet))).mp hOn
    filter_upwards [he] with z hz hzu
    exact hz (hScov hzu)
  have hac : ginibreMeasure n≪(volume : Measure (Configuration n)) := by
    rw [ginibreMeasure_eq_real_withDensity hn]
    exact (withDensity_absolutelyContinuous _ _).smul_left _
  refine ⟨a,?_⟩
  apply Lp.ext
  filter_upwards [(Measure.AbsolutelyContinuous.ae_le hac hae), ginibre_ae_collisionFree n hn, ginibreRealConstantL2_ae n hn a]
    with z hz hcf hconst
  exact (hz hcf).trans hconst.symm
#print axioms correspondenceOperator_zero_gradient_constant
end
end GinibrePoincare
