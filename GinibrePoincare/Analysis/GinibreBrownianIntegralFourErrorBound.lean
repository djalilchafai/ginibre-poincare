module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralInitialCutoff

@[expose] public section

/-! Genuine L² error estimates used to pass initial-time-cutoff stochastic
integrals to a continuous martingale limit. -/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem actualMeanSquare_difference_le_four_errors {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (I S A T J : Ω → ℝ)
    (hI : MemLp I 2 P) (hS : MemLp S 2 P) (hA : MemLp A 2 P)
    (hT : MemLp T 2 P) (hJ : MemLp J 2 P) :
    (∫ ω, (I ω-J ω)^2 ∂P) ≤ 4*((∫ ω, (I ω-S ω)^2 ∂P)+
      (∫ ω, (S ω-A ω)^2 ∂P)+(∫ ω, (A ω-T ω)^2 ∂P)+
      (∫ ω, (T ω-J ω)^2 ∂P)) := by
  have hIS := (hI.sub hS).integrable_sq
  have hSA := (hS.sub hA).integrable_sq
  have hAT := (hA.sub hT).integrable_sq
  have hTJ := (hT.sub hJ).integrable_sq
  have hbound (ω : Ω) : (I ω-J ω)^2 ≤
      4*((I ω-S ω)^2+(S ω-A ω)^2+(A ω-T ω)^2+(T ω-J ω)^2) := by
    nlinarith [sq_nonneg ((I ω-S ω)-(S ω-A ω)),
      sq_nonneg ((I ω-S ω)-(A ω-T ω)), sq_nonneg ((I ω-S ω)-(T ω-J ω)),
      sq_nonneg ((S ω-A ω)-(A ω-T ω)), sq_nonneg ((S ω-A ω)-(T ω-J ω)),
      sq_nonneg ((A ω-T ω)-(T ω-J ω))]
  have hh := integral_mono (hI.sub hJ).integrable_sq
    (((hIS.add hSA).add hAT).add hTJ |>.const_mul 4) hbound
  simp only [Pi.sub_apply] at hIS hSA hAT hTJ hh
  rw [integral_const_mul] at hh
  have he1 := integral_add ((hIS.add hSA).add hAT) hTJ
  have he2 := integral_add (hIS.add hSA) hAT
  have he3 := integral_add hIS hSA
  simp only [Pi.add_apply] at hh he1 he2 he3
  rw [he1, he2, he3] at hh
  exact hh

#print axioms actualMeanSquare_difference_le_four_errors
end
end GinibrePoincare
