module

public import GinibrePoincare.Analysis.AlternativeBochnerKodairaCutoff

@[expose] public section
namespace GinibrePoincare
noncomputable section
open scoped ComplexConjugate ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Literal flat complex Hessian (2.20) of the Gaussian potential Φ=n|z|². -/
theorem correspondence_gaussian_complex_hessian (n : ℕ) (j k : Fin n)
    (z : Configuration n) :
    bkPartial (dbarComponent (fun w : Configuration n =>
      ((n : ℝ)*configurationNormSq w : ℂ)) k) j z =
      if j = k then (n : ℂ) else 0 := by
  have he : dbarComponent (fun w : Configuration n =>
      ((n : ℝ)*configurationNormSq w : ℂ)) k =
      fun w => (n : ℂ)*w k := by
    funext w
    have h := bkRadial_dbar (fun r : ℝ => (n : ℝ)*r)
      (contDiff_const.mul contDiff_id) k w
    simpa using h
  rw [he]
  let L : Configuration n →L[ℝ] ℂ := (n : ℂ) • ContinuousLinearMap.proj k
  have hL : (fun w : Configuration n => (n : ℂ)*w k) = L := by funext w; rfl
  rw [hL]
  unfold bkPartial bkDirectional
  rw [L.fderiv]
  simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection]
  by_cases hjk : j = k
  · subst k
    simp
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp [hjk, Ne.symm hjk]

/-- Strict plurisubharmonicity follows for every nonzero complex tangent vector. -/
theorem correspondence_gaussian_strict_plurisubharmonic (n : ℕ) (hn : 0<n)
    (z v : Configuration n) (hv : v≠0) :
    0 < (∑ j : Fin n, ∑ k : Fin n, conj (v j)*
      bkPartial (dbarComponent (fun w : Configuration n =>
        ((n : ℝ)*configurationNormSq w : ℂ)) k) j z*v k).re := by
  classical
  simp_rw [correspondence_gaussian_complex_hessian]
  have he (j : Fin n) : (∑ k : Fin n, conj (v j)*(if j=k then (n : ℂ) else 0)*v k) =
      (n : ℂ)*(Complex.normSq (v j) : ℂ) := by
    rw [Finset.sum_eq_single j]
    · simp only [ite_true]
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    · intro k hk hkj
      simp [Ne.symm hkj]
    · simp
  simp_rw [he,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.natCast_re,Complex.natCast_im,mul_zero,sub_zero]
  rw [← Finset.mul_sum]
  apply mul_pos (Nat.cast_pos.mpr hn)
  have hex : ∃j : Fin n, v j≠0 := by
    by_contra h
    apply hv
    ext j
    simpa using not_exists.mp h j
  obtain ⟨j,hj⟩ := hex
  exact Finset.sum_pos' (fun k hk => Complex.normSq_nonneg _) ⟨j,Finset.mem_univ _,Complex.normSq_pos.mpr hj⟩

end
end GinibrePoincare

#print axioms GinibrePoincare.correspondence_gaussian_complex_hessian

#print axioms GinibrePoincare.correspondence_gaussian_strict_plurisubharmonic
