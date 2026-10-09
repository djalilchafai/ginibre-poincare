module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultIteration
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Genuine local exactness in every dimension for smooth sources.
Closedness is needed only on the given open neighborhood. -/
theorem localDolbeault_globallySmooth {n : ℕ}
    (Ω : Set (Configuration n)) (hΩ : IsOpen Ω)
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, ContDiff ℝ ∞ (α j))
    (hclosed : ∀ j k p, p ∈ Ω → dbarComponent (α j) k p = dbarComponent (α k) j p)
    (x : Configuration n) (hx : x ∈ Ω) :
    ∃ U : Set (Configuration n), IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      ∃ u : Configuration n → ℂ, ContDiff ℝ ∞ u ∧
        ∀ p ∈ U, ∀ j, dbarComponent u j p = α j p := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  let W : Fin n → Set ℂ := fun j => ball (x j) r
  let V : Fin n → Set ℂ := fun j => ball (x j) (r/4)
  let b : (j : Fin n) → ContDiffBump (x j) := fun _ =>
    { rIn := r/4, rOut := r/2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let χ : Fin n → ℂ → ℂ := fun j z => Complex.ofReal (b j z)
  have hχ (j : Fin n) : ContDiff ℝ ∞ (χ j) :=
    Complex.ofRealCLM.contDiff.comp (b j).contDiff
  have hc (j : Fin n) : HasCompactSupport (χ j) :=
    (b j).hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hχone (j : Fin n) (z : ℂ) (hz : z ∈ V j) : χ j z = 1 := by
    change Complex.ofReal (b j z) = 1
    rw [(b j).one_of_mem_closedBall (ball_subset_closedBall hz), Complex.ofReal_one]
  have hχW (j : Fin n) : tsupport (χ j) ⊆ W j := by
    have hs : tsupport (χ j) ⊆ tsupport (b j) :=
      tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero (b j)
    refine hs.trans ?_
    rw [(b j).tsupport_eq]
    exact closedBall_subset_ball (by change r/2 < r; linarith)
  have hWΩ : dolbeaultCylinder W Finset.univ ⊆ Ω := by
    intro p hp
    apply hball
    apply (dist_pi_lt_iff hr).mpr
    intro j
    exact hp j (Finset.mem_univ j)
  obtain ⟨u, hu, hsol⟩ := smoothClosedForm_coordinate_iteration_on_polydisc α hα W
    (fun _ => isOpen_ball) (fun j k p hp => hclosed j k p (hWΩ hp)) V
    (fun _ => isOpen_ball) χ hχ hc hχone hχW Finset.univ
  let U := dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V Finset.univ
  refine ⟨U, (dolbeaultCylinder_isOpen W (fun _ => isOpen_ball) _).inter
    (dolbeaultCylinder_isOpen V (fun _ => isOpen_ball) _),?_, fun p hp => hWΩ hp.1,
    u, hu, fun p hp j => hsol p hp j (Finset.mem_univ j)⟩
  constructor
  · intro j _; exact mem_ball_self hr
  · intro j _; exact mem_ball_self (by change 0 < r/4; positivity)

/-- Local Dolbeault exactness for genuinely locally smooth forms on an
arbitrary open neighborhood, without a globally smooth input extension. -/
theorem localDolbeault_smooth {n : ℕ}
    (Ω : Set (Configuration n)) (hΩ : IsOpen Ω)
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, ContDiffOn ℝ ∞ (α j) Ω)
    (hclosed : ∀ j k p, p ∈ Ω → dbarComponent (α j) k p = dbarComponent (α k) j p)
    (x : Configuration n) (hx : x ∈ Ω) :
    ∃ U : Set (Configuration n), IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      ∃ u : Configuration n → ℂ, ContDiff ℝ ∞ u ∧
        ∀ p ∈ U, ∀ j, dbarComponent u j p = α j p := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  let b : ContDiffBump x :=
    { rIn := r/2, rOut := 3*r/4, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hbΩ : tsupport b ⊆ Ω := by
    rw [b.tsupport_eq]
    exact (closedBall_subset_ball (by change 3*r/4 < r; linarith)).trans hball
  let β : Fin n → Configuration n → ℂ := fun j p => Complex.ofReal (b p) * α j p
  have hβ (j : Fin n) : ContDiff ℝ ∞ (β j) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ Ω
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p b.contDiffAt).mul
        ((hα j).contDiffAt (hΩ.mem_nhds hp))
    · have hps : p ∉ tsupport b := fun hs => hp (hbΩ hs)
      have he : β j =ᶠ[𝓝 p] (fun _ => 0) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hps] with q hq
        simp only [β, hq, Pi.zero_apply, Complex.ofReal_zero, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have heq (j : Fin n) (p : Configuration n) (hp : p ∈ ball x (r/2)) :
      β j =ᶠ[𝓝 p] α j := by
    filter_upwards [b.eventuallyEq_one_of_mem_ball hp] with q hq
    simp only [β, hq, Pi.one_apply, Complex.ofReal_one, one_mul]
  have hclosedβ (j k : Fin n) (p : Configuration n) (hp : p ∈ ball x (r/2)) :
      dbarComponent (β j) k p = dbarComponent (β k) j p := by
    have hj := finiteComplexDbar_congr_of_eventuallyEq
      (v := realCoordinateDirection k) (w := imaginaryCoordinateDirection k) (heq j p hp)
    have hk := finiteComplexDbar_congr_of_eventuallyEq
      (v := realCoordinateDirection j) (w := imaginaryCoordinateDirection j) (heq k p hp)
    change dbarComponent (β j) k p = dbarComponent (α j) k p at hj
    change dbarComponent (β k) j p = dbarComponent (α k) j p at hk
    rw [hj, hk]
    exact hclosed j k p (hball ((ball_subset_ball (by linarith)) hp))
  obtain ⟨U, hU, hxU, hUb, u, hu, hsol⟩ := localDolbeault_globallySmooth
    (ball x (r/2)) isOpen_ball β hβ hclosedβ x (mem_ball_self (by positivity))
  refine ⟨U, hU, hxU, hUb.trans ((ball_subset_ball (by linarith)).trans hball), u, hu,?_⟩
  intro p hp j
  rw [hsol p hp j]
  exact (heq j p (hUb hp)).self_of_nhds

#print axioms localDolbeault_globallySmooth
#print axioms localDolbeault_smooth
end
end GinibrePoincare
