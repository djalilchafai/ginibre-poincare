module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianPlanarIncrement
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

@[expose] public section

/-! Independent Brownian coordinates form one genuine joint Gaussian process. -/
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_family_isGaussianProcess {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IsGaussianProcess (fun p : ι × ℝ≥0 => B p.1 p.2) P := by
  classical
  constructor
  intro J
  let T := J.image Prod.snd
  let A := fun i ω (t : T) => B i t ω
  have hA (i : ι) : HasGaussianLaw (A i) P := (hB i).isGaussianProcess.hasGaussianLaw T
  have hiA : iIndepFun A P := hind.comp
    (fun i p => fun t : T => p t) (fun i => by fun_prop)
  have hG := hiA.hasGaussianLaw hA
  let L : (ι → T → ℝ) →L[ℝ] (J → ℝ) :=
    { toFun := fun v j => v j.val.1 ⟨j.val.2, mem_image.mpr ⟨j.val, j.property, rfl⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have h := hG.map L
  convert! h using 1

end
end GinibrePoincare
