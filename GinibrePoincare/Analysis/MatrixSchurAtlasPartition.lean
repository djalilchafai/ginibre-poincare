module

public import GinibrePoincare.Analysis.MatrixSchurAtlasOverlap

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000

def matrixSchurAtlasAngularOverlap {n : ℕ} (V : Set (SchurLowerIndex n → ℂ))
    (C E : Matrix.unitaryGroup (Fin n) ℂ) : Set (SchurLowerIndex n → ℂ) :=
  {x | ((star E * C * matrixSchurExponentialUnitaryFrame n x : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V}

theorem matrixSchurAtlasAngularOverlap_isOpen {n : ℕ} (V : Set (SchurLowerIndex n → ℂ))
    (C E : Matrix.unitaryGroup (Fin n) ℂ)
    (hopen : IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ |
      (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V}) :
    IsOpen (matrixSchurAtlasAngularOverlap V C E) :=
  hopen.preimage (continuous_const.mul (matrixSchurExponentialUnitaryFrame_continuous n))

def matrixSchurAtlasAngularPiece {n : ℕ} (V : Set (SchurLowerIndex n → ℂ))
    (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ) (k : ℕ) : Set (SchurLowerIndex n → ℂ) :=
  V \ ⋃ j : Fin k, matrixSchurAtlasAngularOverlap V (C k) (C j.val)

theorem measurableSet_matrixSchurAtlasAngularPiece {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ)) (hV : IsOpen V)
    (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ)
    (hopen : IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ |
      (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V}) (k : ℕ) :
    MeasurableSet (matrixSchurAtlasAngularPiece V C k) :=
  hV.measurableSet.diff (MeasurableSet.iUnion fun j =>
    (matrixSchurAtlasAngularOverlap_isOpen V (C k) (C j.val) hopen).measurableSet)

theorem matrixSchurAtlas_partition_no_overlap {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ)) (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ)
    (k l : ℕ) (hkl : k < l) (p q : SchurCoordinates n)
    (hp : p ∈ matrixSchurAtlasAngularPiece V C k ×ˢ matrixSchurSortedUpperDomain n)
    (hq : q ∈ matrixSchurAtlasAngularPiece V C l ×ˢ matrixSchurSortedUpperDomain n) :
    matrixSchurAtlasChart (C k) p ≠ matrixSchurAtlasChart (C l) q := by
  intro he
  have hflag := matrixSchurAtlas_overlap_flag V (C l) (C k) q p
    ⟨hq.1.1, hq.2⟩ ⟨hp.1.1, hp.2⟩ he.symm
  have hmem : q.1 ∈ matrixSchurAtlasAngularOverlap V (C l) (C k) := by
    change (((C k : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      (C l : Matrix (Fin n) (Fin n) ℂ)) * matrixSchurExponentialFrame n q.1) ∈
        matrixUnitaryFlagSaturation n V
    rw [Matrix.mul_assoc]
    exact hflag
  exact hq.1.2 (Set.mem_iUnion.mpr ⟨⟨k, hkl⟩, hmem⟩)

theorem matrixSchurAtlas_partition_pairwise_disjoint {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ)) (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ) :
    Pairwise (fun k l => Disjoint
      (matrixSchurAtlasChart (C k) '' (matrixSchurAtlasAngularPiece V C k ×ˢ matrixSchurSortedUpperDomain n))
      (matrixSchurAtlasChart (C l) '' (matrixSchurAtlasAngularPiece V C l ×ˢ matrixSchurSortedUpperDomain n))) := by
  intro k l hne
  apply Set.disjoint_left.mpr
  intro G hGk hGl
  obtain ⟨p, hp, hpk⟩ := hGk
  obtain ⟨q, hq, hql⟩ := hGl
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · exact matrixSchurAtlas_partition_no_overlap V C k l hkl p q hp hq (hpk.trans hql.symm)
  · exact matrixSchurAtlas_partition_no_overlap V C l k hlk q p hq hp (hql.trans hpk.symm)

/-- Choosing the first flag chart yields a genuine disjoint product-domain atlas
covering every simple matrix. -/
theorem matrixSchurAtlas_partition_cover {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ)) (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ)
    (hC : ∀ U : Matrix.unitaryGroup (Fin n) ℂ, ∃ k,
      ((C k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ)) ∈
        matrixUnitaryFlagSaturation n V)
    (G : Matrix (Fin n) (Fin n) ℂ) (hs : G.charpoly.Separable) :
    ∃ k, ∃ p ∈ matrixSchurAtlasAngularPiece V C k ×ˢ matrixSchurSortedUpperDomain n,
      G = matrixSchurAtlasChart (C k) p := by
  classical
  let P : ℕ → Prop := fun k => ∃ p ∈ V ×ˢ matrixSchurSortedUpperDomain n,
    G = matrixSchurAtlasChart (C k) p
  have hP : ∃ k, P k := matrixSchurAtlas_cover_of_unitary_cover n V C hC G hs
  obtain ⟨p, hp, he⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, p, ⟨⟨hp.1, ?_⟩, hp.2⟩, he⟩
  intro hUnion
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hUnion
  have hflag : ((C j.val : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      ((C (Nat.find hP) : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n p.1)) ∈
        matrixUnitaryFlagSaturation n V := by
    change p.1 ∈ matrixSchurAtlasAngularOverlap V (C (Nat.find hP)) (C j.val) at hj
    change (((C j.val : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      (C (Nat.find hP) : Matrix (Fin n) (Fin n) ℂ)) * matrixSchurExponentialFrame n p.1) ∈
        matrixUnitaryFlagSaturation n V at hj
    rw [Matrix.mul_assoc] at hj
    exact hj
  obtain ⟨q, hq, heq⟩ := matrixSchurAtlas_flag_overlap V (C (Nat.find hP)) (C j.val) p hp.2 hflag
  have hPj : P j.val := ⟨q, hq, he.trans heq⟩
  have hmin := Nat.find_min' hP hPj
  exact (Nat.not_le_of_lt j.isLt) hmin

#print axioms matrixSchurAtlas_partition_cover
#print axioms matrixSchurAtlas_partition_pairwise_disjoint
end
end GinibrePoincare
