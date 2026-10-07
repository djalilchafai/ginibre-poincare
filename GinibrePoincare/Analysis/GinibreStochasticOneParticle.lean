module

public import GinibrePoincare.Analysis.GinibreStochasticOUPath

@[expose] public section

/-! # Actual Brownian-driven one-particle Ginibre paths

Two real Brownian paths give the planar cumulative noise. The explicit
convolution solves the original Ginibre equation globally almost surely.
-/
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Planar noise at the exact Langevin amplitude √(2α). -/
def ginibreOneParticleBrownianNoise {Ω : Type*}
    (Br Bi : ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) (t : ℝ) : Configuration 1 :=
  fun _ => Real.sqrt (2 * α) •
    ((Br t.toNNReal ω : ℂ) + Complex.I * (Bi t.toNNReal ω : ℂ))

/-- Actual one-particle solution, constructed from the Brownian paths. -/
def ginibreOneParticleBrownianPath {Ω : Type*}
    (Br Bi : ℝ≥0 → Ω → ℝ) (α : ℝ) (z : Configuration 1)
    (t : ℝ) (ω : Ω) : Configuration 1 :=
  drivenOUPath (2 * α) z (ginibreOneParticleBrownianNoise Br Bi α ω) t

 theorem ginibreOneParticleBrownianPath_actual {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (α : ℝ) (z : Configuration 1) :
    ∀ᵐ ω ∂P, Continuous (fun t => ginibreOneParticleBrownianPath Br Bi α z t ω) ∧
      ginibreOneParticleBrownianPath Br Bi α z 0 ω = z ∧
      IsGinibreDrivenPath 1 α (ginibreOneParticleBrownianNoise Br Bi α ω)
        (fun t => ginibreOneParticleBrownianPath Br Bi α z t ω) := by
  filter_upwards [hBr.cont, hBi.cont, hBr.eval_zero_ae_eq_zero,
    hBi.eval_zero_ae_eq_zero] with ω hcr hci hzr hzi
  have hN : Continuous (ginibreOneParticleBrownianNoise Br Bi α ω) := by
    apply continuous_pi
    intro j
    exact ((Complex.continuous_ofReal.comp (hcr.comp continuous_real_toNNReal)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (hci.comp continuous_real_toNNReal)))).const_smul (Real.sqrt (2 * α))
  have hzero : ginibreOneParticleBrownianNoise Br Bi α ω 0 = 0 := by
    ext j
    simp [ginibreOneParticleBrownianNoise, hzr, hzi]
  refine ⟨drivenOUPath_continuous (2 * α) z _ hN, ?_,
    ginibreDrivenPath_one_explicit α z _ hN hzero⟩
  simp [ginibreOneParticleBrownianPath, drivenOUPath, hzero]

end
end GinibrePoincare
