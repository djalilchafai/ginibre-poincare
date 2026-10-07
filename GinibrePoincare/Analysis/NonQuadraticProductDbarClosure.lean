module

public import GinibrePoincare.Analysis.NonQuadraticProductDbar

@[expose] public section

/-! # The closed actual product ∂bar graph
The sharp product estimate extends to the genuine graph completion of
finite separated compact tests, with both derivative coordinates retained. -/
open MeasureTheory
open scoped ContDiff InnerProductSpace TensorProduct
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

abbrev PlanarProductDbarGraphSpace :=
  PlanarProductLebesgueL2 × (PlanarProductLebesgueL2 × PlanarProductLebesgueL2)

def planarProductDbarGraphMap (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarProductCompactTensor →ₗ[ℂ] PlanarProductDbarGraphSpace :=
  (planarProductWeightedValue n V hV).prod
    ((planarProductWeightedDbarLeft n V hV).prod (planarProductWeightedDbarRight n V hV))

/-- The genuine closure of the value-and-two-derivatives graph. -/
def planarProductDbarClosedGraph (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    Submodule ℂ PlanarProductDbarGraphSpace :=
  (planarProductDbarGraphMap n V hV).range.topologicalClosure

/-- The exact product Hörmander constant survives closure in the actual
L² value-and-derivative graph, without any new inequality hypothesis. -/
theorem rhoSubharmonicPotential_product_closed_graph_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (x : PlanarProductDbarGraphSpace)
    (hx : x ∈ planarProductDbarClosedGraph n V hV.continuous) :
    ‖x.1 - planarLeftBergmanProjection n V hV (planarRightBergmanProjection n V hV x.1)‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) * (‖x.2.1‖ ^ 2 + ‖x.2.2‖ ^ 2) := by
  let S : Set PlanarProductDbarGraphSpace := {x |
    ‖x.1 - planarLeftBergmanProjection n V hV (planarRightBergmanProjection n V hV x.1)‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) * (‖x.2.1‖ ^ 2 + ‖x.2.2‖ ^ 2)}
  have hc : IsClosed S := isClosed_le
    ((continuous_fst.sub ((planarLeftBergmanProjection n V hV).continuous.comp
      ((planarRightBergmanProjection n V hV).continuous.comp continuous_fst))).norm.pow 2)
    (continuous_const.mul (((continuous_fst.comp continuous_snd).norm.pow 2).add
      ((continuous_snd.comp continuous_snd).norm.pow 2)))
  have hi : ((planarProductDbarGraphMap n V hV.continuous).range : Set PlanarProductDbarGraphSpace) ⊆ S := by
    rintro _ ⟨f, rfl⟩
    exact rhoSubharmonicPotential_product_compact_tensor_gap n hn V ρ hρpos hV hρ f
  exact hc.closure_subset_iff.mpr hi hx
end
end GinibrePoincare
