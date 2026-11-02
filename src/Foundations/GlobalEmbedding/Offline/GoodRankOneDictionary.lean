import GlobalEmbedding.Offline.GoodCovectorDensity
import GlobalEmbedding.Offline.ContinuousRankOneBasis
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual finite rank-one dictionaries with good directions

Source: `main.tex`, the good rank-one dictionary preparation preceding (6.4),
node `repair-good-rank-one-dictionary`.  All forms are native continuous bilinear
maps.  Perturbing the actual covectors produces an actual finite coordinate
matrix; its determinant and inverse coefficients define a genuine open set.
The proved density of the original good cone then supplies a good family in
that set.  No symmetric-form subtype, substituted metric, or density hypothesis
is introduced.
-/

noncomputable section

open GlobalEmbedding.Paper Filter Set
open scoped Topology Matrix ContDiff

namespace GlobalEmbedding.Offline

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

-- Cache the existing nested operator structures, without changing any norm.
private noncomputable local instance dictionaryBilinearSemi :
    SeminormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

private noncomputable local instance dictionaryBilinearNormed :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance dictionaryBilinearNormedSpace :
    NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Actual coordinate columns of the squared covectors in an existing finite
bilinear-form coordinate system. -/
def covectorSquareCoordinateMatrix
    (C : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (ι → ℝ))
    (ξ : ι → V →L[ℝ] ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ C ((ξ j).smulRight (ξ j)) i

omit [Fintype ι] [DecidableEq ι] in
/-- The actual squared-covector matrix varies continuously in the covectors. -/
theorem continuous_covectorSquareCoordinateMatrix
    (C : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (ι → ℝ)) :
    Continuous (covectorSquareCoordinateMatrix C) := by
  apply continuous_matrix
  intro i j
  have hs : Continuous (fun ξ : ι → V →L[ℝ] ℝ ↦ (ξ j).smulRight (ξ j)) := by
    have hb : Continuous (fun p : (V →L[ℝ] ℝ) × (V →L[ℝ] ℝ) ↦ p.1.smulRight p.2) :=
      (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := V) (F := V →L[ℝ] ℝ)).continuous
    have hpair : Continuous (fun ξ : ι → V →L[ℝ] ℝ ↦ (ξ j, ξ j)) :=
      (continuous_apply j).prodMk (continuous_apply j)
    exact hb.comp hpair
  exact (continuous_apply i).comp (C.continuous.comp hs)

omit [DecidableEq ι] in
/-- Actual synthesis followed by the given coordinates is literal matrix-vector
multiplication, with precisely the column convention used by the inverse. -/
theorem coordinates_covector_square_sum
    (C : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (ι → ℝ))
    (ξ : ι → V →L[ℝ] ℝ) (a : ι → ℝ) :
    C (∑ i, a i • (ξ i).smulRight (ξ i)) =
      (covectorSquareCoordinateMatrix C ξ).mulVec a := by
  ext j
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    covectorSquareCoordinateMatrix, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- If the original actual dictionary has a left inverse, its coordinate
matrix is the identity. -/
theorem covectorSquareCoordinateMatrix_eq_one
    (C : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (ι → ℝ))
    (ψ : ι → V →L[ℝ] ℝ)
    (hleft : ∀ a : ι → ℝ, C (∑ i, a i • (ψ i).smulRight (ψ i)) = a) :
    covectorSquareCoordinateMatrix C ψ = 1 := by
  ext i j
  have h := hleft (Pi.single j 1)
  rw [coordinates_covector_square_sum] at h
  have hij := congrFun h i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply,
    Pi.single_apply] using hij

/-- Invertible actual matrices whose inverse coefficients are strictly positive
form an open set.  Positivity is imposed on the real inverse solution itself. -/
theorem isOpen_matrix_positive_inverse_coefficients (b : ι → ℝ) :
    IsOpen {T : Matrix ι ι ℝ | T.det ≠ 0 ∧ ∀ i, 0 < (T⁻¹ *ᵥ b) i} := by
  apply isOpen_iff_mem_nhds.mpr
  intro T hT
  have hdet : ∀ᶠ S : Matrix ι ι ℝ in 𝓝 T, S.det ≠ 0 :=
    (continuous_id.matrix_det.continuousAt.eventually
      (isOpen_ne.mem_nhds hT.1))
  have hinv : ContinuousAt (fun S : Matrix ι ι ℝ ↦ S⁻¹) T :=
    continuousAt_matrix_inv T (by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hT.1)
  have hcoef : ContinuousAt (fun S : Matrix ι ι ℝ ↦ S⁻¹ *ᵥ b) T :=
    (continuous_id.matrix_mulVec continuous_const).continuousAt.comp hinv
  have hpos : ∀ i, ∀ᶠ S : Matrix ι ι ℝ in 𝓝 T, 0 < (S⁻¹ *ᵥ b) i := by
    intro i
    exact ((continuous_apply i).continuousAt.comp hcoef).eventually
      (isOpen_Ioi.mem_nhds (hT.2 i))
  filter_upwards [hdet, Filter.eventually_all.mpr hpos] with S hS hSp
  exact ⟨hS, hSp⟩

omit [DecidableEq ι] in
/-- A literal finite sum of actual squared covectors is a symmetric bilinear
form, with arbitrary real coefficients. -/
theorem covector_square_sum_symmetric
    (ξ : ι → V →L[ℝ] ℝ) (a : ι → ℝ) :
    ∀ v w, (∑ i, a i • (ξ i).smulRight (ξ i)) v w =
      (∑ i, a i • (ξ i).smulRight (ξ i)) w v := by
  intro v w
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A genuine invertible coordinate matrix gives a new continuous coefficient
map with BOTH inverse identities on the actual native bilinear forms.  The
right inverse is proved on every symmetric form from the original right
inverse, so spanning is not an additional conclusion assumed as input. -/
theorem covector_square_basis_of_invertible_coordinate_matrix
    (C : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (ι → ℝ))
    (ψ ξ : ι → V →L[ℝ] ℝ)
    (hright : ∀ A : V →L[ℝ] V →L[ℝ] ℝ, (∀ v w, A v w = A w v) →
      (∑ i, C A i • (ψ i).smulRight (ψ i)) = A)
    (hdet : (covectorSquareCoordinateMatrix C ξ).det ≠ 0) :
    ∃ D : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (ι → ℝ),
      (∀ A, D A = (covectorSquareCoordinateMatrix C ξ)⁻¹ *ᵥ C A) ∧
      (∀ a : ι → ℝ, D (∑ i, a i • (ξ i).smulRight (ξ i)) = a) ∧
      (∀ A : V →L[ℝ] V →L[ℝ] ℝ, (∀ v w, A v w = A w v) →
        (∑ i, D A i • (ξ i).smulRight (ξ i)) = A) ∧
      LinearIndependent ℝ (fun i ↦ (ξ i).smulRight (ξ i)) := by
  let T := covectorSquareCoordinateMatrix C ξ
  have hunit : IsUnit T.det := isUnit_iff_ne_zero.mpr hdet
  let D : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (ι → ℝ) :=
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := ι → ℝ) (F' := ι → ℝ)
      (T⁻¹).mulVecLin).comp C
  have hD (A : V →L[ℝ] V →L[ℝ] ℝ) : D A = T⁻¹ *ᵥ C A := rfl
  have hleftD (a : ι → ℝ) : D (∑ i, a i • (ξ i).smulRight (ξ i)) = a := by
    rw [hD, coordinates_covector_square_sum]
    change T⁻¹ *ᵥ (T *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hunit, Matrix.one_mulVec]
  have hrightD (A : V →L[ℝ] V →L[ℝ] ℝ) (hA : ∀ v w, A v w = A w v) :
      (∑ i, D A i • (ξ i).smulRight (ξ i)) = A := by
    have hcoord : C (∑ i, D A i • (ξ i).smulRight (ξ i)) = C A := by
      rw [coordinates_covector_square_sum, hD]
      change T *ᵥ (T⁻¹ *ᵥ C A) = C A
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hunit, Matrix.one_mulVec]
    calc
      (∑ i, D A i • (ξ i).smulRight (ξ i)) =
          ∑ j, C (∑ i, D A i • (ξ i).smulRight (ξ i)) j • (ψ j).smulRight (ψ j) :=
        (hright _ (covector_square_sum_symmetric ξ (D A))).symm
      _ = ∑ j, C A j • (ψ j).smulRight (ψ j) := by rw [hcoord]
      _ = A := hright A hA
  refine ⟨D, hD, hleftD, hrightD, ?_⟩
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have h := congrArg D ha
  rw [hleftD, map_zero] at h
  exact congrFun h i

variable [FiniteDimensional ℝ V]

/-- The positive finite rank-one dictionary can be perturbed to actual good
directions.  The open set is constructed here from the actual determinant and
inverse solution; no openness, density, or spanning of the final family is
supplied as a hypothesis.  The resulting continuous coefficient map reconstructs
every symmetric form and has strictly positive coefficients at the given form.
-/
theorem exists_positive_good_rank_one_dictionary
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W)
    (hgood : ∃ ξ : V →L[ℝ] ℝ, LinearSecondFormGoodCovector B ξ.toLinearMap)
    (g : V →L[ℝ] V →L[ℝ] ℝ)
    (ψ : ι → V →L[ℝ] ℝ)
    (C : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (ι → ℝ))
    (hleft : ∀ a : ι → ℝ, C (∑ i, a i • (ψ i).smulRight (ψ i)) = a)
    (hright : ∀ A : V →L[ℝ] V →L[ℝ] ℝ, (∀ v w, A v w = A w v) →
      (∑ i, C A i • (ψ i).smulRight (ψ i)) = A)
    (hpositive : ∀ i, 0 < C g i) :
    ∃ (ξ : ι → V →L[ℝ] ℝ)
      (D : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (ι → ℝ)),
      (∀ i, LinearSecondFormGoodCovector B (ξ i).toLinearMap) ∧
      (∀ i, 0 < D g i) ∧
      (∀ a : ι → ℝ, D (∑ i, a i • (ξ i).smulRight (ξ i)) = a) ∧
      (∀ A : V →L[ℝ] V →L[ℝ] ℝ, (∀ v w, A v w = A w v) →
        (∑ i, D A i • (ξ i).smulRight (ξ i)) = A) ∧
      LinearIndependent ℝ (fun i ↦ (ξ i).smulRight (ξ i)) := by
  let U : Set (ι → V →L[ℝ] ℝ) :=
    {ξ | (covectorSquareCoordinateMatrix C ξ).det ≠ 0 ∧
      ∀ i, 0 < ((covectorSquareCoordinateMatrix C ξ)⁻¹ *ᵥ C g) i}
  have hopen : IsOpen U :=
    (isOpen_matrix_positive_inverse_coefficients (C g)).preimage
      (continuous_covectorSquareCoordinateMatrix C)
  have hψ : ψ ∈ U := by
    change (covectorSquareCoordinateMatrix C ψ).det ≠ 0 ∧ _
    rw [covectorSquareCoordinateMatrix_eq_one C ψ hleft]
    simp only [Matrix.det_one, ne_eq, one_ne_zero, not_false_eq_true,
      inv_one, Matrix.one_mulVec, true_and]
    exact hpositive
  obtain ⟨ξ, hξ, hgoodξ⟩ := exists_actual_good_family_mem_open B hgood U hopen ⟨ψ, hψ⟩
  obtain ⟨D, hD, hleftD, hrightD, hind⟩ :=
    covector_square_basis_of_invertible_coordinate_matrix C ψ ξ hright hξ.1
  refine ⟨ξ, D, hgoodξ, ?_, hleftD, hrightD, hind⟩
  intro i
  rw [hD]
  exact hξ.2 i

/-- From an actual good witness and an arbitrary positive definite source
tensor, construct exactly `n(n+1)/2` actual good directions forming a rank-one
basis, with a continuous linear coefficient map and positive coefficients.
The initial dictionary is produced by the proved edge-root construction;
none is supplied as an input to this theorem. -/
theorem positive_good_rank_one_basis
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W)
    (hgood : ∃ ξ : V →L[ℝ] ℝ, LinearSecondFormGoodCovector B ξ.toLinearMap)
    (g : V →L[ℝ] V →L[ℝ] ℝ)
    (hgsymm : ∀ v w, g v w = g w v)
    (hgpos : ∀ v, v ≠ 0 → 0 < g v v) :
    ∃ (ξ : EdgePair (Module.finrank ℝ V + 1) → V →L[ℝ] ℝ)
      (D : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ]
        (EdgePair (Module.finrank ℝ V + 1) → ℝ)),
      (∀ i, LinearSecondFormGoodCovector B (ξ i).toLinearMap) ∧
      (∀ i, 0 < D g i) ∧
      (∀ a, D (continuousRankOneReconstruct ξ a) = a) ∧
      (∀ A, (∀ v w, A v w = A w v) → continuousRankOneReconstruct ξ (D A) = A) ∧
      LinearIndependent ℝ (fun i ↦ (ξ i).smulRight (ξ i)) ∧
      Fintype.card (EdgePair (Module.finrank ℝ V + 1)) =
        Module.finrank ℝ V * (Module.finrank ℝ V + 1) / 2 := by
  classical
  obtain ⟨ψ, C, _hne, _hLI, hleft, hright, hCg⟩ :=
    positive_continuous_rank_one_basis g hgsymm hgpos
  obtain ⟨ξ, D, hξ, hD, hl, hr, hLI⟩ :=
    exists_positive_good_rank_one_dictionary B hgood g ψ C
      (by simpa only [continuousRankOneReconstruct_eq_sum] using hleft)
      (by simpa only [continuousRankOneReconstruct_eq_sum] using hright)
      (by intro i; rw [hCg]; norm_num)
  refine ⟨ξ, D, hξ, hD, ?_, ?_, hLI, ?_⟩
  · simpa only [continuousRankOneReconstruct_eq_sum] using hl
  · simpa only [continuousRankOneReconstruct_eq_sum] using hr
  · rw [card_edgePair]
    simp only [Nat.add_sub_cancel, Nat.mul_comm]

omit [FiniteDimensional ℝ V] [DecidableEq ι] in
/-- Finitely many actual positive coefficients have one positive reserve on
a genuine open neighborhood. The minimum includes the extra number one so
the construction remains valid for an empty dictionary. -/
theorem coefficient_common_positive_neighborhood
    (D : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (ι → ℝ))
    (g : V →L[ℝ] V →L[ℝ] ℝ) (hpositive : ∀ i, 0 < D g i) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ U : Set (V →L[ℝ] V →L[ℝ] ℝ),
      IsOpen U ∧ g ∈ U ∧ ∀ A ∈ U, ∀ i, μ ≤ D A i := by
  let c : Option ι → ℝ := fun i ↦ i.elim 1 (D g)
  let hne : (Finset.univ : Finset (Option ι)).Nonempty := ⟨none, Finset.mem_univ _⟩
  let b : ℝ := Finset.univ.inf' hne c
  have hb : 0 < b := by
    apply (Finset.lt_inf'_iff hne).mpr
    intro i _
    cases i with
    | none => norm_num [c]
    | some i => exact hpositive i
  have hbi (i : ι) : b ≤ D g i :=
    Finset.inf'_le c (Finset.mem_univ (some i))
  let μ := b / 2
  let U : Set (V →L[ℝ] V →L[ℝ] ℝ) := {A | ∀ i, μ < D A i}
  have hU : IsOpen U := by
    have heq : U = ⋂ i, {A | μ < D A i} := by
      ext A
      simp only [U, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const ((continuous_apply i).comp D.continuous)
  refine ⟨μ, by dsimp [μ]; positivity, U, hU, ?_, ?_⟩
  · intro i
    dsimp [μ]
    linarith [hbi i]
  · intro A hA i
    exact (hA i).le

omit [FiniteDimensional ℝ V] [DecidableEq ι] in
/-- The actual positive square-root amplitudes are smooth on the same genuine
coefficient neighborhood and reconstruct every symmetric tensor there.  These
are the literal amplitudes of the resulting dictionary, not independent formal
coefficients. -/
theorem dictionary_positive_square_root_amplitudes
    (ξ : ι → V →L[ℝ] ℝ)
    (D : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (ι → ℝ))
    (hright : ∀ A, (∀ v w, A v w = A w v) → continuousRankOneReconstruct ξ (D A) = A)
    {U : Set (V →L[ℝ] V →L[ℝ] ℝ)} {μ : ℝ} (hμ : 0 < μ)
    (hreserve : ∀ A ∈ U, ∀ i, μ ≤ D A i) :
    (∀ i, ContDiffOn ℝ ∞ (fun A ↦ Real.sqrt (D A i)) U) ∧
    ∀ A ∈ U, (∀ v w, A v w = A w v) →
      continuousRankOneReconstruct ξ (fun i ↦ (Real.sqrt (D A i)) ^ 2) = A := by
  constructor
  · intro i
    have hc : ContDiff ℝ ∞ (fun A : V →L[ℝ] V →L[ℝ] ℝ ↦ D A i) :=
      (contDiff_apply ℝ (fun _ : ι ↦ ℝ) i).comp
        (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := V →L[ℝ] V →L[ℝ] ℝ)
          (F := ι → ℝ) D)
    exact hc.contDiffOn.sqrt (fun A hA ↦ (hμ.trans_le (hreserve A hA i)).ne')
  · intro A hA hsymm
    have heq : (fun i ↦ (Real.sqrt (D A i)) ^ 2) = D A := by
      funext i
      exact Real.sq_sqrt (le_of_lt (hμ.trans_le (hreserve A hA i)))
    rw [heq]
    exact hright A hsymm

#print axioms continuous_covectorSquareCoordinateMatrix
#print axioms coordinates_covector_square_sum
#print axioms covectorSquareCoordinateMatrix_eq_one
#print axioms isOpen_matrix_positive_inverse_coefficients
#print axioms covector_square_sum_symmetric
#print axioms covector_square_basis_of_invertible_coordinate_matrix
#print axioms exists_positive_good_rank_one_dictionary
#print axioms positive_good_rank_one_basis
#print axioms coefficient_common_positive_neighborhood
#print axioms dictionary_positive_square_root_amplitudes

end GlobalEmbedding.Offline
