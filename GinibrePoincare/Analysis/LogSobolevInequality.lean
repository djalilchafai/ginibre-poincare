module

public import GinibrePoincare.Analysis.PolynomialEigenfunctions
public import GinibrePoincare.Analysis.GinibreEntropy
public import GinibrePoincare.Analysis.FullRadialLSIReduction

@[expose] public section

/-!
# Unconditional sharp radial logarithmic Sobolev inequality

The entire smooth compact symmetric radial class and its value-gradient
Sobolev completion are covered. The sharp Gaussian input is proved by the
Bernoulli tensorization, binomial CLT and Taylor route, then transported to
the concrete complex block law. No Gaussian inequality remains a hypothesis.
-/

open MeasureTheory
open scoped BigOperators ContDiff

namespace GinibrePoincare

noncomputable section

-- Define entropy
/-- The entropy of f^2 with respect to μ_n. -/
def entropy (n : ℕ) (f : Configuration n → ℝ) : ℝ :=
  ginibreSquareEntropy n f

/-- The paper's Dirichlet form includes the essential `1/n` factor. -/
def dirichletFormLSI (n : ℕ) (f : Configuration n → ℝ) : ℝ :=
  smoothGinibreEnergy n f

-- A function is symmetric if it's invariant under permutations
def IsSymmetricFunctionLSI {n : ℕ} (f : Configuration n → ℝ) : Prop :=
  IsSymmetric f

-- A function is radial if it depends only on the magnitudes |z_1|, ..., |z_n|
def IsRadialFunctionLSI {n : ℕ} (f : Configuration n → ℝ) : Prop :=
  ∃ F : (Fin n → ℝ) → ℝ,
    ∀ z, f z = F (fun i => Complex.normSq (z i))

-- A function is smooth with compact support
def IsSmoothCompactSupportLSI {n : ℕ} (f : Configuration n → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f

-- Radial LSI: Theorem 1.12 of http://arxiv.org/abs/2608.19358v2
structure LogSobolevInequality (n : ℕ) : Prop where
  -- For all symmetric radial smooth compactly supported functions f,
  -- the entropy is bounded by the Dirichlet form
  inequality :
    ∀ (f : Configuration n → ℝ),
      IsSmoothCompactSupportLSI f →
      IsSymmetricFunctionLSI f →
      IsRadialFunctionLSI f →
      entropy n f ≤ dirichletFormLSI n f
  
  -- The unconditional Sobolev completion theorem is `radial_sobolev_lsi`.

/-- The unconditional sharp LSI for the full smooth symmetric radial core. -/
theorem logSobolevInequality_instance (n : ℕ) (hn : n ≥ 1) : LogSobolevInequality n := by
  constructor
  intro f hfc hs hr
  exact radial_core_lsi n hn f ⟨⟨hfc.1, hfc.2, hs⟩, hr⟩

end

end GinibrePoincare
