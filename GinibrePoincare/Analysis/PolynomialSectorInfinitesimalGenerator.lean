module

public import GinibrePoincare.Analysis.PolynomialSectorSelfAdjoint
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.TangentCone.Real

@[expose] public section

/-! # Infinitesimal-generator identification for the actual closed sector -/
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The exact eigenvalue action on the complete normalized basis. -/
theorem polynomialSectorEvolution_hilbertBasis (n : ℕ) (hn : 2 ≤ n)
    (t : ℝ≥0) (i : PolynomialEigenfunctionData n) :
    polynomialSectorEvolution n hn t (polynomialSectorHilbertBasis n hn i) =
      (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) •
        polynomialSectorHilbertBasis n hn i := by
  simp only [polynomialSectorHilbertBasis_apply, normalizedPolynomialSectorEigenvector,
    map_smul, polynomialSectorEvolution_eigenvector]
  rw [smul_comm]

/-- Exact coordinate action for every vector of the complete sector. -/
theorem polynomialSectorEvolution_inner_basis (n : ℕ) (hn : 2 ≤ n)
    (t : ℝ≥0) (i : PolynomialEigenfunctionData n) (x : closedPolynomialSector n hn) :
    inner ℂ (polynomialSectorHilbertBasis n hn i) (polynomialSectorEvolution n hn t x) =
      (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) *
        inner ℂ (polynomialSectorHilbertBasis n hn i) x := by
  classical
  let b := polynomialSectorHilbertBasis n hn
  have hx : x ∈ (Submodule.span ℂ (Set.range b)).topologicalClosure := by
    rw [b.dense_span]
    trivial
  have hc : IsClosed {x : closedPolynomialSector n hn |
      inner ℂ (b i) (polynomialSectorEvolution n hn t x) =
        (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) * inner ℂ (b i) x} := by
    apply isClosed_eq <;> fun_prop
  apply closure_minimal ?_ hc hx
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    change inner ℂ (b i) (polynomialSectorEvolution n hn t (b j)) =
      (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) * inner ℂ (b i) (b j)
    rw [polynomialSectorEvolution_hilbertBasis]
    have hsmul : inner ℂ (b i) ((Real.exp (-eigenvalue n j.a j.b j.m * t) : ℂ) • b j) =
        (Real.exp (-eigenvalue n j.a j.b j.m * t) : ℂ) * inner ℂ (b i) (b j) := by
      change inner ℂ (b i : GinibrePolynomialL2 n)
        ((Real.exp (-eigenvalue n j.a j.b j.m * t) : ℂ) • (b j : GinibrePolynomialL2 n)) = _
      exact inner_smul_right _ _ _
    rw [hsmul, orthonormal_iff_ite.mp b.orthonormal i j]
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [hij, if_false, mul_zero]
  | zero =>
    change inner ℂ (b i) (polynomialSectorEvolution n hn t 0) = _
    simp only [map_zero, inner_zero_right, mul_zero]
  | add x y _ _ hx hy =>
    change inner ℂ (b i) (polynomialSectorEvolution n hn t (x + y)) = _
    rw [map_add, inner_add_right, inner_add_right, hx, hy, mul_add]
  | smul c x _ hx =>
    change inner ℂ (b i) (polynomialSectorEvolution n hn t (c • x)) = _
    rw [map_smul]
    change inner ℂ (b i : GinibrePolynomialL2 n)
      (c • (polynomialSectorEvolution n hn t x : GinibrePolynomialL2 n)) =
      (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) *
        inner ℂ (b i : GinibrePolynomialL2 n) (c • (x : GinibrePolynomialL2 n))
    have hx' : inner ℂ (b i : GinibrePolynomialL2 n)
        (polynomialSectorEvolution n hn t x : GinibrePolynomialL2 n) =
        (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) *
          inner ℂ (b i : GinibrePolynomialL2 n) (x : GinibrePolynomialL2 n) := hx
    rw [inner_smul_right, inner_smul_right, hx']
    ring

/-- Real-time orbit, extended constantly to negative times for calculus. -/
def polynomialSectorOrbit (n : ℕ) (hn : 2 ≤ n) (x : closedPolynomialSector n hn)
    (t : ℝ) : closedPolynomialSector n hn :=
  polynomialSectorEvolution n hn (Real.toNNReal t) x

theorem polynomialSectorOrbit_continuous (n : ℕ) (hn : 2 ≤ n)
    (x : closedPolynomialSector n hn) : Continuous (polynomialSectorOrbit n hn x) :=
  (continuous_polynomialSectorEvolution n hn x).comp continuous_real_toNNReal

private theorem spectral_scalar_hasDerivAt (rate : ℝ) (c : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (Real.exp (-rate * s) : ℂ) * c)
      ((Real.exp (-rate * t) : ℂ) * (-(rate : ℂ) * c)) t := by
  have h := (((hasDerivAt_id t).const_mul (-rate)).exp).ofReal_comp
  convert h.mul_const c using 1 <;> (try simp only [id_eq, mul_one]) <;>
    push_cast <;> first | rfl | ring

/-- Every actual generator graph pair satisfies the integrated orbit equation. -/
theorem polynomialSectorGenerator_orbit_integral (n : ℕ) (hn : 2 ≤ n)
    (u v : closedPolynomialSector n hn)
    (hp : (u, v) ∈ (polynomialSectorGenerator n hn).graph)
    (t : ℝ) (ht : 0 ≤ t) :
    polynomialSectorOrbit n hn u t = u + ∫ s in (0 : ℝ)..t, polynomialSectorOrbit n hn v s := by
  let b := polynomialSectorHilbertBasis n hn
  have hspec : (u, v) ∈ polynomialSectorSpectralGraph n hn := by
    rwa [polynomialSectorGenerator_graph] at hp
  have hint : IntervalIntegrable (polynomialSectorOrbit n hn v) volume 0 t :=
    (polynomialSectorOrbit_continuous n hn v).intervalIntegrable 0 t
  apply b.repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  have he : inner ℂ (b i) (polynomialSectorOrbit n hn u t) =
      (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) * inner ℂ (b i) u := by
    rw [polynomialSectorOrbit, polynomialSectorEvolution_inner_basis, Real.coe_toNNReal t ht]
  rw [he, inner_add_right]
  have hcomm := (innerSL ℂ (b i)).intervalIntegral_comp_comm hint
  change (∫ s in (0 : ℝ)..t, inner ℂ (b i) (polynomialSectorOrbit n hn v s)) =
    inner ℂ (b i) (∫ s in (0 : ℝ)..t, polynomialSectorOrbit n hn v s) at hcomm
  rw [← hcomm]
  have hc : (∫ s in (0 : ℝ)..t, inner ℂ (b i) (polynomialSectorOrbit n hn v s)) =
      ∫ s in (0 : ℝ)..t, (Real.exp (-eigenvalue n i.a i.b i.m * s) : ℂ) * inner ℂ (b i) v := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := (Set.mem_Icc.mp (by simpa [Set.uIcc_of_le ht] using hs)).1
    change inner ℂ (b i) (polynomialSectorEvolution n hn (Real.toNNReal s) v) = _
    rw [polynomialSectorEvolution_inner_basis, Real.coe_toNNReal s hs0]
  rw [hc]
  have hder : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun r : ℝ => (Real.exp (-eigenvalue n i.a i.b i.m * r) : ℂ) * inner ℂ (b i) u)
        ((Real.exp (-eigenvalue n i.a i.b i.m * s) : ℂ) * inner ℂ (b i) v) s := by
    intro s hs
    rw [hspec i]
    exact spectral_scalar_hasDerivAt _ _ s
  have hcontinuous : Continuous (fun s : ℝ =>
      (Real.exp (-eigenvalue n i.a i.b i.m * s) : ℂ) * inner ℂ (b i) v) := by fun_prop
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (hcontinuous.intervalIntegrable 0 t)
  rw [hcalc]
  simp only [mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul]
  ring

/-- A genuine generator-domain vector has the semigroup's right derivative. -/
theorem polynomialSectorGenerator_hasDerivWithinAt_zero (n : ℕ) (hn : 2 ≤ n)
    (u v : closedPolynomialSector n hn)
    (hp : (u, v) ∈ (polynomialSectorGenerator n hn).graph) :
    HasDerivWithinAt (polynomialSectorOrbit n hn u) v (Set.Ici (0 : ℝ)) 0 := by
  have hc := polynomialSectorOrbit_continuous n hn v
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (0 : ℝ) 0)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hadd : HasDerivWithinAt
      (fun t : ℝ => u + ∫ s in (0 : ℝ)..t, polynomialSectorOrbit n hn v s)
      v (Set.Ici (0 : ℝ)) 0 := by
    simpa only [polynomialSectorOrbit, Real.toNNReal_zero, polynomialSectorEvolution_zero,
      ContinuousLinearMap.id_apply] using (hd.const_add u).hasDerivWithinAt
  exact hadd.congr_of_mem
    (fun t ht => polynomialSectorGenerator_orbit_integral n hn u v hp t ht) (by simp)

/-- The semigroup's right derivative at zero forces the exact closed-domain
spectral equations. -/
theorem polynomialSectorGenerator_graph_of_hasDerivWithinAt_zero (n : ℕ) (hn : 2 ≤ n)
    (u v : closedPolynomialSector n hn)
    (hd : HasDerivWithinAt (polynomialSectorOrbit n hn u) v (Set.Ici (0 : ℝ)) 0) :
    (u, v) ∈ (polynomialSectorGenerator n hn).graph := by
  rw [polynomialSectorGenerator_graph]
  intro i
  let b := polynomialSectorHilbertBasis n hn
  let coeff := (innerSL ℂ (b i)).restrictScalars ℝ
  have hcoord : HasDerivWithinAt
      (fun t : ℝ => inner ℂ (b i) (polynomialSectorOrbit n hn u t))
      (inner ℂ (b i) v) (Set.Ici (0 : ℝ)) 0 :=
    coeff.hasFDerivAt.comp_hasDerivWithinAt 0 hd
  have hscalar : HasDerivWithinAt
      (fun t : ℝ => (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) * inner ℂ (b i) u)
      (-(eigenvalue n i.a i.b i.m : ℂ) * inner ℂ (b i) u) (Set.Ici (0 : ℝ)) 0 := by
    simpa only [mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul] using
      (spectral_scalar_hasDerivAt (eigenvalue n i.a i.b i.m) (inner ℂ (b i) u) 0).hasDerivWithinAt
  have hsame : ∀ t ∈ Set.Ici (0 : ℝ),
      inner ℂ (b i) (polynomialSectorOrbit n hn u t) =
        (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) * inner ℂ (b i) u := by
    intro t ht
    rw [polynomialSectorOrbit, polynomialSectorEvolution_inner_basis, Real.coe_toNNReal t ht]
  have hscalar' := hscalar.congr_of_mem hsame (by simp)
  exact UniqueDiffWithinAt.eq_deriv (Set.Ici (0 : ℝ))
    (uniqueDiffWithinAt_Ici 0) hcoord hscalar'

/-- Exact infinitesimal-generator identification, with the original graph
closure identified by `polynomialSectorGenerator_graph_iff_ambient`. -/
theorem polynomialSectorGenerator_graph_iff_right_derivative (n : ℕ) (hn : 2 ≤ n)
    (u v : closedPolynomialSector n hn) :
    (u, v) ∈ (polynomialSectorGenerator n hn).graph ↔
      HasDerivWithinAt (polynomialSectorOrbit n hn u) v (Set.Ici (0 : ℝ)) 0 :=
  ⟨polynomialSectorGenerator_hasDerivWithinAt_zero n hn u v,
    polynomialSectorGenerator_graph_of_hasDerivWithinAt_zero n hn u v⟩

end
end GinibrePoincare
