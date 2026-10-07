module

public import GinibrePoincare.Analysis.GinibreFullSemigroupRegularity

@[expose] public section

/-! # Classical positive-time dynamics for arbitrary full L² input -/
open Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every orbit, without an initial domain hypothesis, solves the generator equation
classically at every strictly positive time. -/
theorem resolventCfcOrbit_positive_time_dynamics (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (x : H) {t : ℝ} (ht : 0 < t) :
    ∃ v : H, (resolventCfcOrbit R x t, v) ∈ (resolventGenerator R).graph ∧
      HasDerivAt (resolventCfcOrbit R x) v t := by
  let a : ℝ := t / 2
  have ha : 0 < a := by dsimp [a]; positivity
  let A := Real.toNNReal a
  have hA : 0 < A := Real.toNNReal_pos.mpr ha
  let u := resolventCfcEvolution R A x
  let w := u - resolventCfcSmoothingPreimage R A x
  have hg : (u, w) ∈ (resolventGenerator R).graph :=
    resolventCfcEvolution_smoothing_graph R hR hInj A hA x
  have hd := resolventGenerator_orbit_hasDerivAt R hR hInj hSpec hDense u w hg
    (t := t - a) (by dsimp [a]; linarith)
  have hshift : HasDerivAt (fun s : ℝ => s - a) 1 t := (hasDerivAt_id t).sub_const a
  have hcomp := hd.scomp t hshift
  have hta : t - a = a := by dsimp [a]; ring
  simp only [hta, one_smul] at hcomp
  have heq : resolventCfcOrbit R x =ᶠ[𝓝 t] fun s : ℝ => resolventCfcOrbit R u (s - a) := by
    have hat : a < t := by dsimp [a]; linarith
    have he : ∀ᶠ s : ℝ in 𝓝 t, a < s := isOpen_Ioi.mem_nhds hat
    filter_upwards [he] with s hs
    unfold resolventCfcOrbit
    change resolventCfcEvolution R (Real.toNNReal s) x =
      resolventCfcEvolution R (Real.toNNReal (s - a)) (resolventCfcEvolution R (Real.toNNReal a) x)
    rw [← show Real.toNNReal (s - a) + Real.toNNReal a = Real.toNNReal s from by
      rw [← Real.toNNReal_add (by linarith) ha.le, sub_add_cancel], resolventCfcEvolution_add]
    rfl
  refine ⟨resolventCfcOrbit R w a, ?_, hcomp.congr_of_eventuallyEq heq⟩
  have hpres := resolventCfcEvolution_preserves_generator_graph R hR hInj A u w hg
  have htadd : Real.toNNReal t = A + A := by
    dsimp [A]
    rw [← Real.toNNReal_add ha.le ha.le]
    congr 1
    dsimp [a]
    ring
  change (resolventCfcEvolution R (Real.toNNReal t) x, resolventCfcEvolution R A w) ∈
    (resolventGenerator R).graph
  rw [htadd, resolventCfcEvolution_add]
  exact hpres

/-- Arbitrary actual symmetric Ginibre L² initial data have classical full diffusion
dynamics at each positive time. -/
theorem ginibreFullEvolution_positive_time_dynamics (n : ℕ) (hn : 0 < n)
    (x : ginibreSymmetricL2 n) {t : ℝ} (ht : 0 < t) :
    ∃ v : ginibreSymmetricL2 n,
      (ginibreFullEvolution n hn (Real.toNNReal t) x, v) ∈ (ginibreFullGenerator n hn).graph ∧
      HasDerivAt (fun s : ℝ => ginibreFullEvolution n hn (Real.toNNReal s) x) v t :=
  resolventCfcOrbit_positive_time_dynamics _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) (ginibreFullComplexResolvent_spectrum n hn)
    (ginibreFullComplexResolvent_denseRange n hn) x ht

end
end GinibrePoincare
