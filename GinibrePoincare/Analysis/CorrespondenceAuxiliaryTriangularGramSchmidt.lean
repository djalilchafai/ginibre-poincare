module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- A positive-diagonal triangular reconstruction uniquely determines the
ordinary normalized Gram–Schmidt algorithm. This reusable algebraic lemma
will be applied to the concrete Gaussian monomial/Hermite reconstruction. -/
theorem gramSchmidtNormed_of_positive_triangular
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (f g : ι → E) (hg : Orthonormal ℂ g) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (htri : ∀ i, f i - (c i : ℂ) • g i ∈
      Submodule.span ℂ (g '' Set.Iio i)) :
    InnerProductSpace.gramSchmidtNormed ℂ f = g := by
  classical
  have hinner : ∀ i j, inner ℂ (g i) (g j) = if i=j then 1 else 0 :=
    (orthonormal_iff_ite.mp hg)
  have hgs : ∀ i, InnerProductSpace.gramSchmidt ℂ f i = (c i : ℂ) • g i := by
    intro i
    refine (wellFounded_lt (α := ι)).induction (C := fun i => InnerProductSpace.gramSchmidt ℂ f i = (c i : ℂ) • g i) i ?_
    intro i ih
    letI : Fintype {j : ι // j < i} := (Set.finite_Iio i).fintype
    have himage : g '' Set.Iio i = Set.range (fun j : {j : ι // j < i} => g j) := by
      ext v
      simp
    have htri_i := htri i
    rw [himage] at htri_i
    obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp htri_i
    have hf : f i = (c i : ℂ) • g i + ∑ j : {j : ι // j < i}, a j • g j := by
      rw [ha]
      abel
    rw [InnerProductSpace.gramSchmidt_def]
    have hproject (j : ι) (hj : j ∈ Finset.Iio i) :
        (ℂ ∙ InnerProductSpace.gramSchmidt ℂ f j).starProjection (f i) =
          a ⟨j,Finset.mem_Iio.mp hj⟩ • g j := by
      rw [ih j (Finset.mem_Iio.mp hj)]
      simp only [Submodule.span_singleton_smul_eq
        (isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hc j).ne'))]
      rw [Submodule.starProjection_singleton,hg.norm_eq_one,one_pow,RCLike.ofReal_one,div_one,hf,
        inner_add_right,inner_smul_right,inner_sum]
      have hjne : j ≠ i := (Finset.mem_Iio.mp hj).ne
      rw [hinner j i,ite_eq_right hjne,mul_zero,zero_add]
      simp_rw [inner_smul_right,hinner]
      rw [Finset.sum_eq_single ⟨j,Finset.mem_Iio.mp hj⟩]
      · simp
      · intro k hk hkj
        have hne : j ≠ k.val := by
          intro he
          apply hkj
          exact Subtype.ext he.symm
        simp [hne]
      · simp
    have hsum : (∑ j ∈ Finset.Iio i,
        (ℂ ∙ InnerProductSpace.gramSchmidt ℂ f j).starProjection (f i)) =
        ∑ j : {j : ι // j < i}, a j • g j := by
      rw [Finset.sum_subtype (p := fun j : ι => j < i) (Finset.Iio i) (by simp) (fun j =>
        (ℂ ∙ InnerProductSpace.gramSchmidt ℂ f j).starProjection (f i))]
      apply Finset.sum_congr rfl
      intro j hj
      exact hproject j (Finset.mem_Iio.mpr j.property)
    rw [hsum,hf]
    abel
  funext i
  rw [InnerProductSpace.gramSchmidtNormed,hgs i,norm_smul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (hc i),hg.norm_eq_one,mul_one,smul_smul]
  simp [Complex.ofReal_ne_zero.mpr (hc i).ne']

#print axioms gramSchmidtNormed_of_positive_triangular
end
end GinibrePoincare
