module

public import GinibrePoincare.Analysis.GinibreHamiltonianLaplacian

@[expose] public section

/-! Genuine negative tangential Hessian of the logarithmic Hamiltonian. -/
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem ginibreHamiltonian_real_configuration_imaginary_hessian {n : ℕ}
    (x : Fin n → ℝ) (hx : Function.Injective x) (j : Fin n) :
    secondDirectionalDerivative (ginibreHamiltonian n) (imaginaryCoordinateDirection j)
      (fun i => (x i : ℂ)) =
      2 * (n : ℝ) - 2 * ∑ k ∈ Finset.univ.erase j, ((x j-x k)⁻¹)^2 := by
  have hz : CollisionFree (fun i => (x i : ℂ)) := by
    intro i k h
    exact hx (Complex.ofReal_injective h)
  unfold secondDirectionalDerivative
  rw [show imaginaryCoordinateDirection j = coordinateDirection j Complex.I from rfl,
    ginibreHamiltonian_coordinate_hessian _ _ hz]
  have hi : coordinateDirection j Complex.I j = Complex.I := by simp [coordinateDirection]
  rw [hi]
  have hs : (∑ k ∈ Finset.univ.erase j,
      (Complex.I * ((x j : ℂ)-(x k : ℂ))⁻¹ *
        (coordinateDirection j Complex.I j-coordinateDirection j Complex.I k) *
        ((x j : ℂ)-(x k : ℂ))⁻¹).re) =
      -(∑ k ∈ Finset.univ.erase j, ((x j-x k)⁻¹)^2) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≠ j := (Finset.mem_erase.mp hk).1
    simp [coordinateDirection, hk', ← Complex.ofReal_sub, ← Complex.ofReal_inv,
      Complex.mul_re, Complex.mul_im, pow_two]
  rw [hi] at hs
  rw [hs]
  norm_num
  ring

theorem ginibreHamiltonian_imaginary_hessian_le_pair {n : ℕ}
    (x : Fin n → ℝ) (hx : Function.Injective x) (j k : Fin n) (hjk : k ≠ j) :
    secondDirectionalDerivative (ginibreHamiltonian n) (imaginaryCoordinateDirection j)
      (fun i => (x i : ℂ)) ≤ 2*(n : ℝ)-2*((x j-x k)⁻¹)^2 := by
  rw [ginibreHamiltonian_real_configuration_imaginary_hessian x hx j]
  have hs : ((x j-x k)⁻¹)^2 ≤
      ∑ l ∈ Finset.univ.erase j, ((x j-x l)⁻¹)^2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg ((x j-x l)⁻¹)) (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ k⟩)
  linarith

/-- Every proposed pointwise curvature lower bound fails at a genuine collision-free
configuration and an actual imaginary coordinate direction of Euclidean squared norm one. -/
theorem ginibreHamiltonian_pointwise_curvature_unbounded_below {n : ℕ}
    (hn : 2 ≤ n) (B : ℝ) :
    ∃ z : Configuration n, CollisionFree z ∧
      ∃ j : Fin n, configurationNormSq (imaginaryCoordinateDirection j) = 1 ∧
        secondDirectionalDerivative (ginibreHamiltonian n) (imaginaryCoordinateDirection j) z < B := by
  let L : ℝ := |B| + 2*(n : ℝ) + 2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : 0 < L := by dsimp [L]; positivity
  have hL0 : L ≠ 0 := ne_of_gt hL
  let x : Fin n → ℝ := fun i => (i.val : ℝ)/L
  have hx : Function.Injective x := by
    intro i k h
    apply Fin.ext
    have he : (i.val : ℝ) = (k.val : ℝ) := (div_left_inj' hL0).mp h
    exact_mod_cast he
  let j : Fin n := ⟨0, by omega⟩
  let k : Fin n := ⟨1, by omega⟩
  have hkj : k ≠ j := by intro h; have := congrArg Fin.val h; simp [k,j] at this
  have hp := ginibreHamiltonian_imaginary_hessian_le_pair x hx j k hkj
  have hid : (x j-x k)⁻¹ = -L := by
    dsimp [x,j,k]
    simp
  rw [hid] at hp
  refine ⟨fun i => (x i : ℂ), ?_, j, ?_, ?_⟩
  · intro i k h
    exact hx (Complex.ofReal_injective h)
  · unfold configurationNormSq imaginaryCoordinateDirection coordinateDirection
    simp only [apply_ite Complex.normSq, map_zero, Complex.normSq_I]
    simp
  · have hab : -|B| ≤ B := neg_abs_le B
    have hL1 : 1 ≤ L := by dsimp [L]; nlinarith [abs_nonneg B]
    have hsq : L ≤ L^2 := by nlinarith
    dsimp [L] at hsq
    nlinarith [sq_nonneg L]

/-- The paper's normalized pointwise curvature has no finite lower bound. -/
theorem ginibre_pointwise_bakry_emery_curvature_unbounded_below {n : ℕ}
    (hn : 2 ≤ n) (B : ℝ) :
    ∃ z : Configuration n, CollisionFree z ∧
      ∃ j : Fin n, configurationNormSq (imaginaryCoordinateDirection j) = 1 ∧
        (1/(n : ℝ))*secondDirectionalDerivative (ginibreHamiltonian n)
          (imaginaryCoordinateDirection j) z < B := by
  obtain ⟨z,hz,j,hj,hB⟩ := ginibreHamiltonian_pointwise_curvature_unbounded_below hn ((n : ℝ)*B)
  refine ⟨z,hz,j,hj,?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have h := (div_lt_iff₀ hn').mpr (by simpa [mul_comm] using hB)
  simpa [div_eq_mul_inv, mul_comm] using h

/-- Mean eigenvalue of the paper's normalized real Hessian is exactly two. -/
theorem ginibre_pointwise_mean_curvature {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z) :
    configurationLaplacian (ginibreHamiltonian n) z / ((n : ℝ)*(2*(n : ℝ))) = 2 := by
  rw [ginibreHamiltonian_laplacian z hz]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  ring

#print axioms ginibreHamiltonian_pointwise_curvature_unbounded_below
end
end GinibrePoincare
