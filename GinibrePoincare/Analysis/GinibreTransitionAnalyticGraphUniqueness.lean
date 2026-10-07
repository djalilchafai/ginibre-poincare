module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticDissipativeUniqueness
public import GinibrePoincare.Analysis.GinibreFullGeneratorEnergy

@[expose] public section

noncomputable section
open Set
namespace GinibrePoincare

/-- Dissipation for differences in the actual real full generator graph. -/
theorem ginibreFullGenerator_real_difference_dissipative {n : ℕ} (hn : 0 < n)
    (u v a b : ginibreFullSymmetricValues n)
    (hu : ginibreFullSymmetricResolvent n hn (u-a)=u)
    (hv : ginibreFullSymmetricResolvent n hn (v-b)=v) :
    inner ℝ (u-v) (a-b) ≤ 0 := by
  have heq : ginibreFullSymmetricResolvent n hn ((u-v)-(a-b))=u-v := by
    have hsub : (u-v)-(a-b)=(u-a)-(v-b) := by abel
    rw [hsub, map_sub, hu, hv]
  have hg : (ginibreFullSymmetricOfReal n (u-v),
      ginibreFullSymmetricOfReal n (a-b)) ∈ (ginibreFullGenerator n hn).graph := by
    rw [ginibreFullGenerator_graph_iff, ← map_sub, ginibreFullComplexResolvent_ofReal, heq]
  obtain ⟨g, _, _, he⟩ := ginibreFullGenerator_real_energy_identity hn _ _ hg
  have hp : 0 ≤ ginibreWeakEnergy n g := mul_nonneg (by positivity) (sq_nonneg _)
  have hi : inner ℝ (u-v) (a-b)=inner ℝ (a-b).val (u-v).val := by
    exact real_inner_comm _ _
  rw [hi]
  linarith

/-- Actual differentiable real generator orbits with the same initial value
coincide, without any assumed identification of semigroups. -/
theorem ginibreFullGenerator_real_orbit_unique {n : ℕ} (hn : 0 < n)
    (x y vx vy : ℝ → ginibreFullSymmetricValues n) (T : ℝ) (hT : 0 ≤ T)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hdx : ∀ s ∈ Ioo 0 T, HasDerivAt x (vx s) s)
    (hdy : ∀ s ∈ Ioo 0 T, HasDerivAt y (vy s) s)
    (hgx : ∀ s ∈ Ioo 0 T, ginibreFullSymmetricResolvent n hn (x s-vx s)=x s)
    (hgy : ∀ s ∈ Ioo 0 T, ginibreFullSymmetricResolvent n hn (y s-vy s)=y s)
    (hinit : x 0=y 0) : ∀ s ∈ Icc 0 T, x s=y s := by
  apply realHilbert_orbit_unique_of_dissipative_derivative x y vx vy T hT hx hy hdx hdy
  · intro s hs
    exact ginibreFullGenerator_real_difference_dissipative hn _ _ _ _ (hgx s hs) (hgy s hs)
  · exact hinit

/-- Orbit uniqueness with the genuine nonnegative paper-speed scaling. -/
theorem ginibreFullGenerator_real_scaled_orbit_unique {n : ℕ} (hn : 0 < n)
    (x y ax ay : ℝ → ginibreFullSymmetricValues n) (c T : ℝ)
    (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hdx : ∀ s ∈ Ioo 0 T, HasDerivAt x (c • ax s) s)
    (hdy : ∀ s ∈ Ioo 0 T, HasDerivAt y (c • ay s) s)
    (hgx : ∀ s ∈ Ioo 0 T, ginibreFullSymmetricResolvent n hn (x s-ax s)=x s)
    (hgy : ∀ s ∈ Ioo 0 T, ginibreFullSymmetricResolvent n hn (y s-ay s)=y s)
    (hinit : x 0=y 0) : ∀ s ∈ Icc 0 T, x s=y s := by
  apply realHilbert_orbit_unique_of_dissipative_derivative x y
    (fun s => c • ax s) (fun s => c • ay s) T hT hx hy hdx hdy
  · intro s hs
    rw [← smul_sub c (ax s) (ay s), real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos hc
      (ginibreFullGenerator_real_difference_dissipative hn _ _ _ _ (hgx s hs) (hgy s hs))
  · exact hinit

/-- Equality on the true full resolvent range extends to all symmetric L². -/
theorem ginibreFullSymmetric_operators_eq_on_resolvent_range {n : ℕ} (hn : 0 < n)
    (P Q : ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n)
    (heq : ∀ u, P (ginibreFullSymmetricResolvent n hn u)=
      Q (ginibreFullSymmetricResolvent n hn u)) : P=Q := by
  apply ContinuousLinearMap.ext
  exact congrFun ((ginibreFullSymmetricResolvent_denseRange n hn).equalizer
    P.continuous Q.continuous (funext heq))

#print axioms ginibreFullSymmetric_operators_eq_on_resolvent_range

#print axioms ginibreFullGenerator_real_scaled_orbit_unique

#print axioms ginibreFullGenerator_real_difference_dissipative
#print axioms ginibreFullGenerator_real_orbit_unique
end GinibrePoincare
