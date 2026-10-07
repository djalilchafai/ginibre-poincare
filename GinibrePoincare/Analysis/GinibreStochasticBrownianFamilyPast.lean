module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyGaussian
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

@[expose] public section

/-! Every finite independent Brownian family has fresh increments independent of its entire joint past. -/
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_family_increment_independent_past {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) :
    IndepFun (fun ω i => B i (s+t) ω-B i s ω)
      (fun ω (p : ι × Set.Iic s) => B p.1 p.2 ω) P := by
  classical
  let X := fun i ω => B i (s+t) ω-B i s ω
  let Y := fun (p : ι × Set.Iic s) ω => B p.1 p.2 ω
  have hG := ginibreBrownian_family_isGaussianProcess B P hB hind
  have hXY : IsGaussianProcess (Sum.elim X Y) P := by
    apply hG.of_isGaussianProcess
    intro q
    cases q with
    | inl i =>
      refine ⟨{(i,s+t),(i,s)},
        { toFun := fun v => v ⟨(i,s+t), by simp⟩-v ⟨(i,s), by simp⟩
          map_add' := by intros; simp only [Pi.add_apply]; ring
          map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }, ?_⟩
      intro ω
      rfl
    | inr p =>
      refine ⟨{(p.1,(p.2 : ℝ≥0))},
        { toFun := fun v => v ⟨(p.1,(p.2 : ℝ≥0)), by simp⟩
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }, ?_⟩
      intro ω
      rfl
  apply hXY.indepFun_of_covariance_eq_zero
    (fun i => (hB i).aemeasurable (s+t) |>.sub ((hB i).aemeasurable s))
    (fun p => (hB p.1).aemeasurable p.2)
  intro i p
  rcases p with ⟨j,v⟩
  have hXi : MemLp (X i) 2 P :=
    ((hB i).isGaussianProcess.hasGaussianLaw_eval (s+t)).memLp_two.sub
      ((hB i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hYj : MemLp (Y (j,v)) 2 P := ((hB j).isGaussianProcess.hasGaussianLaw_eval v).memLp_two
  by_cases hij : i = j
  · subst j
    have hi := (ginibreBrownian_increment_whole_past_independent (B i) P (hB i) s t).comp
      measurable_id (measurable_pi_apply v)
    exact hi.covariance_eq_zero hXi hYj
  · have hi := (hind.indepFun hij).comp
      (show Measurable (fun p : ℝ≥0 → ℝ => p (s+t)-p s) by fun_prop)
      (measurable_pi_apply (v : ℝ≥0))
    exact hi.covariance_eq_zero hXi hYj

 theorem ginibreBrownian_family_increment_hasLaw {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) :
    HasLaw (fun ω i => B i (s+t) ω-B i s ω)
      (Measure.pi (fun _ : ι => gaussianReal 0 t)) P := by
  have hL (i : ι) : HasLaw (fun ω => B i (s+t) ω-B i s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hi := hind.comp (fun i p => p (s+t)-p s) (fun i => by fun_prop)
  exact hi.hasLaw_pi hL

end
end GinibrePoincare
