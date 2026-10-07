module

public import GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare

@[expose] public section

/-! # The norm comparison in Lemma A.2

These are the actual weighted `L²` gradient graph norms. The separate
collision-cutoff closure assertion of Lemma A.2 is not asserted here.
-/
namespace GinibrePoincare
noncomputable section
open MeasureTheory
variable {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]

/-- The ordinary gradient graph norm (1.6), for real or complex values and
their corresponding gradient value space. -/
def ginibreOrdinaryGradientGraphNorm (n : ℕ)
    (u : Lp F 2 (ginibreMeasure n))
    (g : Lp G 2 (ginibreMeasure n)) : ℝ :=
  Real.sqrt (‖u‖ ^ 2 + ‖g‖ ^ 2)

/-- The Dirichlet graph norm (1.21), at arbitrary positive diffusion coefficient. -/
def ginibreDirichletGradientGraphNorm (n : ℕ) (c : ℝ)
    (u : Lp F 2 (ginibreMeasure n))
    (g : Lp G 2 (ginibreMeasure n)) : ℝ :=
  Real.sqrt (‖u‖ ^ 2 + c * ‖g‖ ^ 2)

/-- Lemma A.2's explicit two-sided norm comparison, with
`c = αₙ / βₙ`. It holds on every actual weighted `L²` gradient pair. -/
theorem ginibre_gradient_graph_norm_equivalence (n : ℕ) (c : ℝ) (hc : 0 < c)
    (u : Lp F 2 (ginibreMeasure n))
    (g : Lp G 2 (ginibreMeasure n)) :
    Real.sqrt (min 1 c) * ginibreOrdinaryGradientGraphNorm n u g ≤
      ginibreDirichletGradientGraphNorm n c u g ∧
    ginibreDirichletGradientGraphNorm n c u g ≤
      Real.sqrt (max 1 c) * ginibreOrdinaryGradientGraphNorm n u g := by
  have hu := sq_nonneg ‖u‖
  have hg := sq_nonneg ‖g‖
  have hlo : min 1 c * (‖u‖ ^ 2 + ‖g‖ ^ 2) ≤ ‖u‖ ^ 2 + c * ‖g‖ ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right (min_le_left 1 c) hu
    have h2 := mul_le_mul_of_nonneg_right (min_le_right 1 c) hg
    nlinarith
  have hhi : ‖u‖ ^ 2 + c * ‖g‖ ^ 2 ≤ max 1 c * (‖u‖ ^ 2 + ‖g‖ ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_right (le_max_left 1 c) hu
    have h2 := mul_le_mul_of_nonneg_right (le_max_right 1 c) hg
    nlinarith
  unfold ginibreOrdinaryGradientGraphNorm ginibreDirichletGradientGraphNorm
  constructor
  · rw [← Real.sqrt_mul (by positivity : 0 ≤ min 1 c)]
    exact Real.sqrt_le_sqrt hlo
  · rw [← Real.sqrt_mul (by positivity : 0 ≤ max 1 c)]
    exact Real.sqrt_le_sqrt hhi

/-- Both comparison constants are strictly positive, so the preceding
comparison is an equivalence of norms rather than a degenerate bound. -/
theorem ginibre_gradient_graph_norm_constants_pos (c : ℝ) (hc : 0 < c) :
    0 < Real.sqrt (min 1 c) ∧ 0 < Real.sqrt (max 1 c) := by
  constructor <;> apply Real.sqrt_pos.mpr <;> positivity

#print axioms ginibre_gradient_graph_norm_equivalence
#print axioms ginibre_gradient_graph_norm_constants_pos

end
end GinibrePoincare
