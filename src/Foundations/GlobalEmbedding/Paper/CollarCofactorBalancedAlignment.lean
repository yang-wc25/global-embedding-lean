import GlobalEmbedding.Paper.CollarHopfGramCofactorCoordinates
import GlobalEmbedding.Paper.BalancedPairingInverseCoordinates
import GlobalEmbedding.Paper.BalancedNormalizedSourceForcing
import GlobalEmbedding.Paper.BalancedQuadraticDataTranslation

/-!
# The same actual collar data in the two existing finite enumerations

Source: `main.tex`, prop:collar, lines522–534, and lem:balanced, lines384–418.
DAG: `collar-cofactor-balanced-alignment`; exclusive W2.
Only the existing Euclidean data coordinates are permuted. The original ambient
norm, actual matrix, Hilbert–Schmidt model and whole-function Q are unchanged.
-/

noncomputable section
open WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The genuine Euclidean reindexing from the existing balanced Fin coordinates
to the existing cofactor Fin coordinates: undo the first enumeration and apply
the second. This is unrelated to the norm on the original Hopf ambient space. -/
def collarCofactorDataCoordinates (a : ℕ) :
    EuclideanSpace ℝ (Fin (Fintype.card (BalancedPairingIndex a))) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a)) :=
  (balancedPairingDataCoordinates a).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (freeCofactorColumnOrder a))

/-- Exact forward and inverse coordinates, with their genuine Euclidean norms.
Cancel the existing enumeration equivalences; empty data are included. -/
theorem collarCofactorDataCoordinates_spec (a : ℕ) :
    (∀ z k, collarCofactorDataCoordinates a z (freeCofactorColumnOrder a k) =
      z (Fintype.equivFin (BalancedPairingIndex a) k)) ∧
    (∀ z k, (collarCofactorDataCoordinates a).symm z
      (Fintype.equivFin (BalancedPairingIndex a) k) = z (freeCofactorColumnOrder a k)) ∧
    (∀ z, ‖collarCofactorDataCoordinates a z‖ = ‖z‖) ∧
    (∀ z, ‖(collarCofactorDataCoordinates a).symm z‖ = ‖z‖) := by
  refine ⟨?_, ?_, (collarCofactorDataCoordinates a).norm_map,
    (collarCofactorDataCoordinates a).symm.norm_map⟩
  · intro z k
    simp only [collarCofactorDataCoordinates, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.piLpCongrLeft_apply]
    change (balancedPairingDataCoordinates a).symm z
      ((freeCofactorColumnOrder a).symm (freeCofactorColumnOrder a k)) = _
    rw [Equiv.symm_apply_apply, (balanced_pairing_data_coordinates_spec a).2.1]
  · intro z k
    simp only [collarCofactorDataCoordinates, LinearIsometryEquiv.symm_trans,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.trans_apply]
    change balancedPairingDataCoordinates a
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (freeCofactorColumnOrder a)).symm z)
      (Fintype.equivFin (BalancedPairingIndex a) k) = _
    rw [(balanced_pairing_data_coordinates_spec a).1,
      LinearIsometryEquiv.piLpCongrLeft_symm]
    rfl

/-- The actual T matrix applied to u is exactly the original balanced pairing,
in the cofactor enumeration. Reuse the actual native matrix pairing identity
and the original coordinate isometries; no desired packing identity is assumed. -/
theorem collarHopf_pairing_balanced_coordinates {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F)
    (x : FreeHopfProduct C) (u : EuclideanSpace ℝ (Fin N)) :
    WithLp.toLp 2
      ((collarAmbientHopfPairingMatrix C F (freeHopfAmbientInclusion C x)).mulVec
        (fun j ↦ u j)) =
      collarCofactorDataCoordinates a (balancedPairingDataCoordinates a
        (balancedPairingMap (F ∘ freeHopfAmbientInclusion C) (freeHopfGenerator C) x u)) := by
  apply PiLp.ext
  intro r
  obtain ⟨k, rfl⟩ := (freeCofactorColumnOrder a).surjective r
  rw [(collarCofactorDataCoordinates_spec a).1,
    (balanced_pairing_data_coordinates_spec a).1]
  simpa only [Equiv.symm_apply_apply] using
    collarAmbientHopfPairingMatrix_pairing C F hF x u (freeCofactorColumnOrder a k)

/-- The same HS coefficient in the other domain enumeration, by the already
proved coefficient equivalences and domain arrowCongr. This is a continuous
linear equivalence, without an operator-norm/HS-norm identification. -/
def collarCofactorCoefficientCoordinates (a N : ℕ) :
    EuclideanSpace ℝ (Fin (N * Fintype.card (BalancedPairingIndex a))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N * (freeSymmetricColumnCount a + a))) :=
  ((hilbertSchmidtCoordinateEquiv (Fintype.card (BalancedPairingIndex a)) N).toContinuousLinearEquiv.trans
      ((collarCofactorDataCoordinates a).toContinuousLinearEquiv.arrowCongr
        (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))))).trans
          (hilbertSchmidtCoordinateEquiv (freeSymmetricColumnCount a + a) N).symm.toContinuousLinearEquiv

/-- The exact HS coefficient transport commutes with actual operator evaluation.
Cancel the existing equivalences and the domain permutation. -/
theorem collarCofactorCoefficientCoordinates_evaluation (a N : ℕ)
    (z : EuclideanSpace ℝ (Fin (N * Fintype.card (BalancedPairingIndex a))))
    (u : EuclideanSpace ℝ (Fin (Fintype.card (BalancedPairingIndex a)))) :
    hilbertSchmidtCoordinateEvaluation (freeSymmetricColumnCount a + a) N
      (collarCofactorCoefficientCoordinates a N z) (collarCofactorDataCoordinates a u) =
        hilbertSchmidtCoordinateEvaluation (Fintype.card (BalancedPairingIndex a)) N z u := by
  change (hilbertSchmidtCoordinateEquiv (freeSymmetricColumnCount a + a) N)
    ((hilbertSchmidtCoordinateEquiv (freeSymmetricColumnCount a + a) N).symm
      (((collarCofactorDataCoordinates a).toContinuousLinearEquiv.arrowCongr
        (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))))
          (hilbertSchmidtCoordinateEquiv (Fintype.card (BalancedPairingIndex a)) N z)))
            (collarCofactorDataCoordinates a u) = _
  rw [LinearEquiv.apply_symm_apply]
  change (hilbertSchmidtCoordinateEquiv (Fintype.card (BalancedPairingIndex a)) N z)
    ((collarCofactorDataCoordinates a).symm (collarCofactorDataCoordinates a u)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- The same native inverse has exactly the transported balanced HS coordinates.
This is cancellation of existing coordinate equivalences, for every operator. -/
theorem collarCofactorCoefficientCoordinates_native {a N : ℕ}
    (R : EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    collarCofactorCoefficientCoordinates a N (balancedPairingInverseCoordinates a N R) =
      (hilbertSchmidtCoordinateEquiv (freeSymmetricColumnCount a + a) N).symm
        (R.comp (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          (freeCofactorColumnOrder a)).symm.toContinuousLinearMap) := by
  apply (hilbertSchmidtCoordinateEquiv (freeSymmetricColumnCount a + a) N).injective
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨v, rfl⟩ := (collarCofactorDataCoordinates a).surjective u
  change hilbertSchmidtCoordinateEvaluation (freeSymmetricColumnCount a + a) N
    (collarCofactorCoefficientCoordinates a N (balancedPairingInverseCoordinates a N R))
      (collarCofactorDataCoordinates a v) = _
  rw [collarCofactorCoefficientCoordinates_evaluation,
    (balanced_pairing_inverse_coordinates_spec a N).1,
    LinearEquiv.apply_symm_apply]
  change R ((balancedPairingDataCoordinates a).symm v) =
    R ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (freeCofactorColumnOrder a)).symm
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (freeCofactorColumnOrder a))
        ((balancedPairingDataCoordinates a).symm v)))
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- The actual ordinary-transpose Gram matrix coefficient is exactly the HS
transport of the SAME native inverse's existing balanced coordinates. Use the
accepted actual Gram/cofactor identity, then the literal HS flattening formula.
No full-rank premise is needed, since both inverses are the same total inverse. -/
theorem collarHopf_cofactor_balanced_inverse_coordinates {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (x : FreeHopfProduct C) :
    collarCofactorCoefficientCoordinates a N (balancedPairingInverseCoordinates a N
      (freeGramRightInverse (freeColumnOperator
        (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x)))) =
      toLp 2 (fun q : Fin (N * (freeSymmetricColumnCount a + a)) ↦
        let T := collarAmbientHopfPairingMatrix C F (freeHopfAmbientInclusion C x)
        (T.transpose * (T * T.transpose)⁻¹)
          (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) := by
  rw [collarCofactorCoefficientCoordinates_native, ← collarHopf_gram_cofactor_coordinates C F x]
  simp only [hilbertSchmidtCoordinateEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- The literal raw (0,S) in cofactor order is twice the SAME existing normalized
balanced residual at t=1,S4=0. Compute the actual coordinates; thus the factor
one half in the accepted69 equation is inserted exactly once, not twice. -/
theorem collarCofactor_raw_residual {a : ℕ} (S : Matrix (Fin a) (Fin a) ℝ)
    (r : Fin (freeSymmetricColumnCount a + a)) :
    collarCofactorDataCoordinates a
      ((2 : ℝ) • balancedNormalizedResidualCoordinates 1 S 0) r =
        match (freeCofactorColumnOrder a).symm r with
        | Sum.inl _ => 0
        | Sum.inr ij => S ij.val.1 ij.val.2 := by
  obtain ⟨k, rfl⟩ := (freeCofactorColumnOrder a).surjective r
  rw [(collarCofactorDataCoordinates_spec a).1, Equiv.symm_apply_apply]
  change (2 : ℝ) * balancedNormalizedResidualCoordinates 1 S 0
    (Fintype.equivFin (BalancedPairingIndex a) k) = _
  rw [(balanced_normalized_residual_data_spec 1 S 0).2.2.1]
  cases k <;> simp [balancedNormalizedResidualData]
  ring

/-- Apply the existing bounded target-map provider to this particular genuine
data permutation, on the ORIGINAL little space. No carrier is reconstructed. -/
def collarCofactorLittleDataMap {a k : ℕ} {α : ℝ} :
    LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) k α →L[ℝ]
      LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) k α :=
  (collar_holder_target_map (a := a) (k := k) (α := α)
    (collarCofactorDataCoordinates a).toContinuousLinearMap).choose_spec.choose

/-- The inverse target permutation uses the same accepted original-space API. -/
def collarBalancedLittleDataMap {a k : ℕ} {α : ℝ} :
    LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) k α →L[ℝ]
      LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) k α :=
  (collar_holder_target_map (a := a) (N := freeSymmetricColumnCount a + a)
    (M := Fintype.card (BalancedPairingIndex a)) (k := k) (α := α)
    (collarCofactorDataCoordinates a).symm.toContinuousLinearMap).choose_spec.choose

/-- The selected map is literal pointwise postcomposition. Its norm bound is
already supplied by the accepted target-map theorem, without a new estimate. -/
theorem collarCofactorLittleDataMap_value {a k : ℕ} {α : ℝ}
    (f : LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) k α)
    (y : EuclideanSpace ℝ (Fin a)) :
    (collarCofactorLittleDataMap f).val.toFun y =
      collarCofactorDataCoordinates a (f.val.toFun y) :=
  congrFun ((collar_holder_target_map (a := a) (N := Fintype.card (BalancedPairingIndex a))
    (M := freeSymmetricColumnCount a + a) (k := k) (α := α)
    (collarCofactorDataCoordinates a).toContinuousLinearMap).choose_spec.choose_spec.2.2.1 f) y

/-- Literal inverse postcomposition on the original little functions. -/
theorem collarBalancedLittleDataMap_value {a k : ℕ} {α : ℝ}
    (f : LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) k α)
    (y : EuclideanSpace ℝ (Fin a)) :
    (collarBalancedLittleDataMap f).val.toFun y =
      (collarCofactorDataCoordinates a).symm (f.val.toFun y) :=
  congrFun ((collar_holder_target_map (a := a) (N := freeSymmetricColumnCount a + a)
    (M := Fintype.card (BalancedPairingIndex a)) (k := k) (α := α)
    (collarCofactorDataCoordinates a).symm.toContinuousLinearMap).choose_spec.choose_spec.2.2.1 f) y

/-- The two original little maps cancel. Use the actual lift formulas, the
existing carrier injectivity and the genuine data equivalence inverse laws. -/
theorem collarCofactorLittleDataMap_inverse (a k : ℕ) (α : ℝ) :
    (∀ f : LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) k α,
      collarBalancedLittleDataMap (collarCofactorLittleDataMap f) = f) ∧
    (∀ f : LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) k α,
      collarCofactorLittleDataMap (collarBalancedLittleDataMap f) = f) := by
  constructor <;> intro f <;> apply Subtype.ext <;>
    apply periodicCAlpha_toFun_injective <;> funext y
  · rw [collarBalancedLittleDataMap_value, collarCofactorLittleDataMap_value,
      LinearIsometryEquiv.symm_apply_apply]
  · rw [collarCofactorLittleDataMap_value, collarBalancedLittleDataMap_value,
      LinearIsometryEquiv.apply_symm_apply]

/-- Constant target reindexing commutes with every actual spatial translation.
This is equality of the existing whole little functions, by their lifted values. -/
theorem collarCofactorLittleDataMap_translate {a k : ℕ} {α : ℝ}
    (t : EuclideanSpace ℝ (Fin a))
    (f : LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) k α) :
    collarCofactorLittleDataMap (littlePeriodicCAlphaTranslateIsometry t f) =
      littlePeriodicCAlphaTranslateIsometry t (collarCofactorLittleDataMap f) := by
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext y
  rw [collarCofactorLittleDataMap_value]
  change collarCofactorDataCoordinates a (f.val.toFun (y + t)) =
    (collarCofactorLittleDataMap f).val.toFun (y + t)
  exact (collarCofactorLittleDataMap_value f (y + t)).symm

/-- The actual old Gram defect, in the actual cofactor row order, is exactly
the transported canonical residual at the SAME native orbit point. Reuse the
accepted original-action inclusion and old-Gram identity; no new forcing is used. -/
theorem collarHopf_raw_residual_balanced_coordinates {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) :
    collarCofactorDataCoordinates a ((2 : ℝ) • balancedNormalizedResidualCoordinates 1
      (Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i (F ∘ freeHopfAmbientInclusion C)
        (freeHopfRealAction C (fun i ↦ y i) x)) - 1) 0) =
      toLp 2 (fun r : Fin (freeSymmetricColumnCount a + a) ↦
        match (freeCofactorColumnOrder a).symm r with
        | Sum.inl _ => 0
        | Sum.inr ij => collarAmbientHopfMetricDefect C F
          (collarAmbientHopfAction C (fun i ↦ y i) (freeHopfAmbientInclusion C x))
            ij.val.1 ij.val.2) := by
  apply PiLp.ext
  intro r
  rw [collarCofactor_raw_residual]
  rw [collarAmbientHopfAction_inclusion, collarAmbientHopfMetricDefect_inclusion]

/-- An actual original little raw OLD-Gram forcing has canonical balanced data
given by the actual inverse target map. Its precise packing is proved from the
literal raw formula, rather than assumed as a desired coordinate compatibility.
The forward map recovers the SAME h, with the actual inverse-map norm bound. -/
theorem collarHopf_little_raw_forcing_balanced_coordinates {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (x : FreeHopfProduct C)
    (h : LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ))
    (hh : ∀ y r, h.val.toFun y r = match (freeCofactorColumnOrder a).symm r with
      | Sum.inl _ => 0
      | Sum.inr ij => collarAmbientHopfMetricDefect C F
        (collarAmbientHopfAction C (fun i ↦ y i) (freeHopfAmbientInclusion C x))
          ij.val.1 ij.val.2) :
    ∃ hB : LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) 2 (1 / 2 : ℝ),
      (∀ y, hB.val.toFun y = (2 : ℝ) • balancedNormalizedResidualCoordinates 1
        (Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i (F ∘ freeHopfAmbientInclusion C)
          (freeHopfRealAction C (fun i ↦ y i) x)) - 1) 0) ∧
      collarCofactorLittleDataMap hB = h ∧
      ‖hB‖ ≤ ‖collarBalancedLittleDataMap (a := a) (k := 2) (α := (1 / 2 : ℝ))‖ * ‖h‖ := by
  refine ⟨collarBalancedLittleDataMap h, ?_,
    (collarCofactorLittleDataMap_inverse a 2 (1 / 2 : ℝ)).2 h,
    (collarBalancedLittleDataMap (a := a) (k := 2) (α := (1 / 2 : ℝ))).le_opNorm h⟩
  intro y
  rw [collarBalancedLittleDataMap_value]
  apply (collarCofactorDataCoordinates a).injective
  rw [LinearIsometryEquiv.apply_symm_apply, collarHopf_raw_residual_balanced_coordinates]
  apply PiLp.ext
  exact hh y

/-- SAME accepted whole-function Q, with only its output reindexed by the actual
little target map. No PDE inverse, Q component or bilinear assembly is reproved. -/
def collarCofactorQuadraticDataOperator {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
        LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 α :=
  (ContinuousLinearMap.compL ℝ (LittlePeriodicCAlphaFunction a N 2 α)
    (LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) 2 α)
    (LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 α)
    collarCofactorLittleDataMap).comp (balancedQuadraticDataOperator hα0 hα1)

/-- The exact whole-function output formula of the transported SAME Q. -/
theorem collarCofactorQuadraticDataOperator_value {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (v w : LittlePeriodicCAlphaFunction a N 2 α)
    (y : EuclideanSpace ℝ (Fin a)) :
    (collarCofactorQuadraticDataOperator hα0 hα1 v w).val.toFun y =
      collarCofactorDataCoordinates a
        ((balancedQuadraticDataOperator hα0 hα1 v w).val.toFun y) :=
  collarCofactorLittleDataMap_value _ y

/-- Each actual cofactor row is the original whole-function component, with
exactly its original -1 or 1/2 factor. Use the existing Q coordinate theorem. -/
theorem collarCofactorQuadraticDataOperator_coordinate {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (k : BalancedPairingIndex a)
    (v w : LittlePeriodicCAlphaFunction a N 2 α) (y : EuclideanSpace ℝ (Fin a)) :
    (collarCofactorQuadraticDataOperator hα0 hα1 v w).val.toFun y
      (freeCofactorColumnOrder a k) =
      (balancedQuadraticDataComponent hα0 hα1 k v w).val.toFun y 0 := by
  rw [collarCofactorQuadraticDataOperator_value,
    (collarCofactorDataCoordinates_spec a).1, balancedQuadraticDataOperator_coordinate]

/-- Undoing only the output enumeration recovers literally the accepted whole
balanced Q. This is the already proved little target-map inverse law. -/
theorem collarCofactorQuadraticDataOperator_balanced {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    collarBalancedLittleDataMap (collarCofactorQuadraticDataOperator hα0 hα1 v w) =
      balancedQuadraticDataOperator hα0 hα1 v w :=
  (collarCofactorLittleDataMap_inverse a 2 α).1 _

/-- The actual first and once-indexed second cofactor rows are the SAME -Qi
and Qij/2, as whole-function outputs. Reuse the accepted explicit first/second
formulas and the genuine data-coordinate permutation, without a new Q proof. -/
theorem collarCofactorQuadraticDataOperator_components {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (v w : LittlePeriodicCAlphaFunction a N 2 α)
    (y : EuclideanSpace ℝ (Fin a)) :
    (∀ i, (collarCofactorQuadraticDataOperator hα0 hα1 v w).val.toFun y
      (freeCofactorColumnOrder a (Sum.inl i)) =
        -((balancedQuadraticFirst (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
          hα1.le i v w).val.toFun y 0)) ∧
    (∀ ij : {p : Fin a × Fin a // p.1 ≤ p.2},
      (collarCofactorQuadraticDataOperator hα0 hα1 v w).val.toFun y
        (freeCofactorColumnOrder a (Sum.inr ij)) =
        (balancedQuadraticSecond (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
          hα1.le ij.val.1 ij.val.2 v w).val.toFun y 0 / 2) := by
  constructor
  · intro i
    rw [collarCofactorQuadraticDataOperator_value, (collarCofactorDataCoordinates_spec a).1]
    exact ((balanced_pairing_data_coordinates_spec a).2.1 _ _).symm.trans
      (balancedQuadraticDataOperator_first hα0 hα1 i v w y)
  · intro ij
    rw [collarCofactorQuadraticDataOperator_value, (collarCofactorDataCoordinates_spec a).1]
    exact ((balanced_pairing_data_coordinates_spec a).2.1 _ _).symm.trans
      (balancedQuadraticDataOperator_second hα0 hα1 ij v w y)

/-- Symmetry of the SAME Q survives constant output transport. -/
theorem collarCofactorQuadraticDataOperator_symmetric {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    collarCofactorQuadraticDataOperator hα0 hα1 v w =
      collarCofactorQuadraticDataOperator hα0 hα1 w v :=
  congrArg collarCofactorLittleDataMap
    (balancedQuadraticDataOperator_symmetric hα0 hα1 v w)

/-- Translation of the SAME Q follows from its accepted translation identity
and the actual original little target-map/translation identity. -/
theorem collarCofactorQuadraticDataOperator_translate {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (t : EuclideanSpace ℝ (Fin a))
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    collarCofactorQuadraticDataOperator hα0 hα1
      (littlePeriodicCAlphaTranslateIsometry t v) (littlePeriodicCAlphaTranslateIsometry t w) =
      littlePeriodicCAlphaTranslateIsometry t
        (collarCofactorQuadraticDataOperator hα0 hα1 v w) := by
  change collarCofactorLittleDataMap (balancedQuadraticDataOperator hα0 hα1
    (littlePeriodicCAlphaTranslateIsometry t v) (littlePeriodicCAlphaTranslateIsometry t w)) = _
  rw [balancedQuadraticDataOperator_translate_euclidean, collarCofactorLittleDataMap_translate]
  rfl

/-- The transported SAME Q has a fixed genuine original-norm bilinear bound,
before any Gaussian width. Directly reuse the accepted Q bound and the actual
target-map operator norm; no HS/operator-norm or ambient-norm identification. -/
theorem collarCofactorQuadraticDataOperator_bound {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ v w : LittlePeriodicCAlphaFunction a N 2 α,
      ‖collarCofactorQuadraticDataOperator hα0 hα1 v w‖ ≤ K * ‖v‖ * ‖w‖ := by
  obtain ⟨B, hB, hb⟩ := balancedQuadraticDataOperator_bound (N := N) hα0 hα1
  let L := collarCofactorLittleDataMap (a := a) (k := 2) (α := α)
  refine ⟨1 + ‖L‖ * B, by positivity, ?_⟩
  intro v w
  change ‖L (balancedQuadraticDataOperator hα0 hα1 v w)‖ ≤ _
  calc
    _ ≤ ‖L‖ * ‖balancedQuadraticDataOperator hα0 hα1 v w‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (B * ‖v‖ * ‖w‖) := mul_le_mul_of_nonneg_left (hb v w) (norm_nonneg L)
    _ ≤ (1 + ‖L‖ * B) * ‖v‖ * ‖w‖ := by
      nlinarith [norm_nonneg v, norm_nonneg w, mul_nonneg (norm_nonneg v) (norm_nonneg w)]

/-- An actual original little coefficient with the literal SAME matrix formula
has the canonical balanced inverse coefficients on EVERY real orbit point.
Construct it by the accepted constant target-map theorem, using the inverse of
the genuine HS coordinate CLE. The actual CLM norm factor is retained.

The returned evaluation identity holds on whole original little functions.
Consequently ANY two genuine HS-formula multipliers agree after this exact
coefficient/data transport. Their formulas, not a desired packing identity, are
the only multiplier premises. No69 solution or analytic seed is constructed. -/
theorem collarHopf_little_coefficient_balanced_coordinates {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (x : FreeHopfProduct C)
    (coeff : LittlePeriodicCAlphaFunction a (N * (freeSymmetricColumnCount a + a))
      2 (1 / 2 : ℝ))
    (hc : ∀ y q,
      let T := collarAmbientHopfPairingMatrix C F
        (collarAmbientHopfAction C (fun i ↦ y i) (freeHopfAmbientInclusion C x))
      coeff.val.toFun y q = (T.transpose * (T * T.transpose)⁻¹)
        (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) :
    ∃ coeffB : LittlePeriodicCAlphaFunction a
        (N * Fintype.card (BalancedPairingIndex a)) 2 (1 / 2 : ℝ),
      (∀ y, coeffB.val.toFun y = balancedPairingInverseCoordinates a N
        (freeGramRightInverse (freeColumnOperator (freeFlowColumns (freeHopfProductFlow C)
          (F ∘ freeHopfAmbientInclusion C) (freeHopfRealAction C (fun i ↦ y i) x))))) ∧
      ‖coeffB‖ ≤ ‖(collarCofactorCoefficientCoordinates a N).symm.toContinuousLinearMap‖ * ‖coeff‖ ∧
      (∀ (u : LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a))
          2 (1 / 2 : ℝ)) y,
        hilbertSchmidtCoordinateEvaluation (freeSymmetricColumnCount a + a) N
          (coeff.val.toFun y) ((collarCofactorLittleDataMap u).val.toFun y) =
        hilbertSchmidtCoordinateEvaluation (Fintype.card (BalancedPairingIndex a)) N
          (coeffB.val.toFun y) (u.val.toFun y)) ∧
      ∀ (multC : LittlePeriodicCAlphaFunction a (N * (freeSymmetricColumnCount a + a))
          2 (1 / 2 : ℝ) →L[ℝ]
          LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ) →L[ℝ]
          LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
        (multB : LittlePeriodicCAlphaFunction a (N * Fintype.card (BalancedPairingIndex a))
          2 (1 / 2 : ℝ) →L[ℝ]
          LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) 2 (1 / 2 : ℝ) →L[ℝ]
          LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)),
        (∀ A u y, (multC A u).val.toFun y =
          hilbertSchmidtCoordinateEvaluation (freeSymmetricColumnCount a + a) N
            (A.val.toFun y) (u.val.toFun y)) →
        (∀ A u y, (multB A u).val.toFun y =
          hilbertSchmidtCoordinateEvaluation (Fintype.card (BalancedPairingIndex a)) N
            (A.val.toFun y) (u.val.toFun y)) →
        ∀ u, multC coeff (collarCofactorLittleDataMap u) = multB coeffB u := by
  let e := collarCofactorCoefficientCoordinates a N
  obtain ⟨_, L, _, _, hL, hLn⟩ := collar_holder_target_map (a := a) (k := 2)
    (α := (1 / 2 : ℝ)) e.symm.toContinuousLinearMap
  have hcoeff (y : EuclideanSpace ℝ (Fin a)) : coeff.val.toFun y =
      e (balancedPairingInverseCoordinates a N (freeGramRightInverse
        (freeColumnOperator (freeFlowColumns (freeHopfProductFlow C)
          (F ∘ freeHopfAmbientInclusion C) (freeHopfRealAction C (fun i ↦ y i) x))))) := by
    rw [collarHopf_cofactor_balanced_inverse_coordinates]
    apply PiLp.ext
    intro q
    rw [hc, collarAmbientHopfAction_inclusion]
  have hvalue (y : EuclideanSpace ℝ (Fin a)) :
      (L coeff).val.toFun y = e.symm (coeff.val.toFun y) := congrFun (hL coeff) y
  have heval (u : LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a))
      2 (1 / 2 : ℝ)) (y : EuclideanSpace ℝ (Fin a)) :
      hilbertSchmidtCoordinateEvaluation (freeSymmetricColumnCount a + a) N
        (coeff.val.toFun y) ((collarCofactorLittleDataMap u).val.toFun y) =
      hilbertSchmidtCoordinateEvaluation (Fintype.card (BalancedPairingIndex a)) N
        ((L coeff).val.toFun y) (u.val.toFun y) := by
    rw [collarCofactorLittleDataMap_value, hvalue]
    have h := collarCofactorCoefficientCoordinates_evaluation a N
      (e.symm (coeff.val.toFun y)) (u.val.toFun y)
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h
  refine ⟨L coeff, ?_, ?_, heval, ?_⟩
  · intro y
    rw [hvalue, hcoeff, ContinuousLinearEquiv.symm_apply_apply]
  · exact (L.le_opNorm coeff).trans (mul_le_mul_of_nonneg_right hLn (norm_nonneg coeff))
  · intro multC multB hmultC hmultB u
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext y
    rw [hmultC, hmultB]
    exact heval u y

end GlobalEmbedding.Paper
