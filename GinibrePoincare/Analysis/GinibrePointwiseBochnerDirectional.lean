module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Tactic

@[expose] public section

open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def bochnerDirectionalDerivative (v : E) (f : E → ℝ) (x : E) : ℝ := fderiv ℝ f x v

theorem bochnerDirectionalDerivative_contDiffAt (v : E) (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (bochnerDirectionalDerivative v f) x := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem bochnerDirectionalDerivative_contDiff (v : E) (f : E → ℝ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (bochnerDirectionalDerivative v f) := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem bochnerDirectionalDerivative_iterated (u v : E) (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) :
    bochnerDirectionalDerivative u (bochnerDirectionalDerivative v f) x=
      fderiv ℝ (fderiv ℝ f) x u v := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)) (differentiableAt_const v)]
  simp

theorem bochnerDirectionalDerivative_comm (u v : E) (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) :
    bochnerDirectionalDerivative u (bochnerDirectionalDerivative v f) x=
      bochnerDirectionalDerivative v (bochnerDirectionalDerivative u f) x := by
  rw [bochnerDirectionalDerivative_iterated u v f x hf, bochnerDirectionalDerivative_iterated v u f x hf]
  exact (hf.isSymmSndFDerivAt (by simpa using (WithTop.coe_le_coe.mpr (show (2 : ℕ∞)≤⊤ from le_top)))).eq u v

theorem bochnerDirectionalDerivative_add (u : E) (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    bochnerDirectionalDerivative u (fun x => f x+g x) x=
      bochnerDirectionalDerivative u f x+bochnerDirectionalDerivative u g x := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_fun_add hf hg]
  rfl

theorem bochnerDirectionalDerivative_sub (u : E) (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    bochnerDirectionalDerivative u (fun x => f x-g x) x=
      bochnerDirectionalDerivative u f x-bochnerDirectionalDerivative u g x := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_fun_sub hf hg]
  rfl

theorem bochnerDirectionalDerivative_const_mul (u : E) (c : ℝ) (f : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) :
    bochnerDirectionalDerivative u (fun x => c*f x) x=c*bochnerDirectionalDerivative u f x := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_const_mul hf]
  rfl

theorem bochnerDirectionalDerivative_mul (u : E) (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    bochnerDirectionalDerivative u (fun x => f x*g x) x=
      bochnerDirectionalDerivative u f x*g x+f x*bochnerDirectionalDerivative u g x := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem bochnerDirectionalDerivative_sum {ι : Type*} [Fintype ι]
    (u : E) (f : ι → E → ℝ) (x : E) (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    bochnerDirectionalDerivative u (fun x => ∑ i, f i x) x=∑ i, bochnerDirectionalDerivative u (f i) x := by
  unfold bochnerDirectionalDerivative
  rw [fderiv_fun_sum (fun i _ => hf i)]
  simp

#print axioms bochnerDirectionalDerivative_comm
end
end GinibrePoincare
