import GlobalEmbedding.Paper.BalancedQuadraticOperators
import GlobalEmbedding.Paper.LittlePeriodicShiftedLaplacianInverse
import GlobalEmbedding.Paper.BalancedPairingDataCoordinates
import GlobalEmbedding.Paper.CollarHolderTargetMap

/-!
# The actual whole-function balanced quadratic data operator

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines407–410.
DAG node: `balanced-quadratic-data-operator`.

Assemble the actual scalar operators with the actual scalar inverse, using only the
existing first/once-indexed-second pairing data and its unique fixed coordinate isometry.
-/

noncomputable section
namespace GlobalEmbedding.Paper

/-- Insert one genuine scalar value into one existing data coordinate and then use
W3's fixed data isometry. Source: Qcal=(-Qi,Qij/2) preceding(4.3). -/
def balancedQuadraticDataValueInjection (a : ℕ) (j : BalancedPairingIndex a) :
    EuclideanSpace ℝ (Fin 1) →L[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (BalancedPairingIndex a))) :=
  (balancedPairingDataCoordinates a).toContinuousLinearMap.comp
    (realEuclideanOneIsometry.symm.toContinuousLinearMap.smulRight
      (EuclideanSpace.single j 1))

/-- The already proved genuine bounded target postcomposition embeds a whole scalar
little function in the chosen existing data coordinate. Source: actual Qcal assembly
in the proof of `lem:balanced`; reuse `collar_holder_target_map` without reproof. -/
def balancedQuadraticDataInjection {a k : ℕ} {α : ℝ} (j : BalancedPairingIndex a) :
    LittlePeriodicCAlphaFunction a 1 k α →L[ℝ]
      LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) k α :=
  (collar_holder_target_map (a := a) (k := k) (α := α)
    (balancedQuadraticDataValueInjection a j)).choose_spec.choose

/-- The selected actual bounded injection has exactly its original pointwise target
map. Source: the fully proved target-map selection in actual Qcal assembly. -/
theorem balancedQuadraticDataInjection_value {a k : ℕ} {α : ℝ}
    (j : BalancedPairingIndex a) (f : LittlePeriodicCAlphaFunction a 1 k α)
    (x : EuclideanSpace ℝ (Fin a)) :
    (balancedQuadraticDataInjection j f).val.toFun x =
      balancedPairingDataCoordinates a (f.val.toFun x 0 • EuclideanSpace.single j 1) := by
  have h := (collar_holder_target_map (a := a) (k := k) (α := α)
    (balancedQuadraticDataValueInjection a j)).choose_spec.choose_spec.2.2.1 f
  exact congrFun h x

/-- The actual first component is −Qi and each ordered second component is Qij/2,
using the genuinely constructed scalar PDE inverse. Source: Qcal preceding(4.3). -/
def balancedQuadraticDataComponent {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (j : BalancedPairingIndex a) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α :=
  match j with
  | Sum.inl i => (-1 : ℝ) • balancedQuadraticFirst
      (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1) hα1.le i
  | Sum.inr ij => (1 / 2 : ℝ) • balancedQuadraticSecond
      (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1) hα1.le ij.val.1 ij.val.2

/-- The true whole-function Qcal=(-Qi,Qij/2) is a bounded bilinear map into the
single existing data-coordinate little space. Embed each complete scalar output
and take the finite sum over the existing once-indexed tuple. No Q or PDE inverse
is an input. Source: `lem:balanced`, the equation preceding(4.3). -/
def balancedQuadraticDataOperator {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
        LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) 2 α :=
  ∑ j : BalancedPairingIndex a,
    (ContinuousLinearMap.compL ℝ (LittlePeriodicCAlphaFunction a N 2 α)
      (LittlePeriodicCAlphaFunction a 1 2 α)
      (LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) 2 α)
      (balancedQuadraticDataInjection j)).comp (balancedQuadraticDataComponent hα0 hα1 j)

/-- Evaluation of the actual whole-function injection gives exactly one original
coordinate. Source: fixed once-indexed data assembly for Qcal in `lem:balanced`. -/
theorem balancedQuadraticDataInjection_coordinate {a k : ℕ} {α : ℝ}
    (j r : BalancedPairingIndex a) (f : LittlePeriodicCAlphaFunction a 1 k α)
    (x : EuclideanSpace ℝ (Fin a)) :
    (balancedQuadraticDataInjection j f).val.toFun x
        (Fintype.equivFin (BalancedPairingIndex a) r) =
      if r = j then f.val.toFun x 0 else 0 := by
  classical
  rw [balancedQuadraticDataInjection_value,
    (balanced_pairing_data_coordinates_spec a).1]
  by_cases hr : r = j
  · subst r
    simp [EuclideanSpace.single]
  · simp [EuclideanSpace.single, hr]

/-- Evaluate Qcal only after its complete scalar component operators have acted.
Actual bounded evaluation commutes with the finite operator sum, and each genuine
coordinate injection selects its one existing data component. Source: Qcal preceding(4.3). -/
theorem balancedQuadraticDataOperator_coordinate {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (r : BalancedPairingIndex a)
    (v w : LittlePeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    (balancedQuadraticDataOperator hα0 hα1 v w).val.toFun x
        (Fintype.equivFin (BalancedPairingIndex a) r) =
      (balancedQuadraticDataComponent hα0 hα1 r v w).val.toFun x 0 := by
  classical
  obtain ⟨ev, hev, _⟩ := collar_little_holder_evaluation
    (a := a) (N := Fintype.card (BalancedPairingIndex a)) (k := 2) (α := α) x
  let e := (PiLp.proj 2 (fun _ : Fin (Fintype.card (BalancedPairingIndex a)) ↦ ℝ)
    (Fintype.equivFin (BalancedPairingIndex a) r)).comp ev
  have he (f : LittlePeriodicCAlphaFunction a (Fintype.card (BalancedPairingIndex a)) 2 α) :
      e f = f.val.toFun x (Fintype.equivFin (BalancedPairingIndex a) r) := by
    change ev f (Fintype.equivFin (BalancedPairingIndex a) r) = _
    rw [hev]
  rw [← he]
  simp only [balancedQuadraticDataOperator, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply]
  rw [map_sum]
  simp only [he, balancedQuadraticDataInjection_coordinate]
  simp

/-- The actual first data entry is the negative of the complete original Qi output,
with the unique existing inverse data-coordinate isometry. Source: Qcal preceding(4.3). -/
theorem balancedQuadraticDataOperator_first {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (i : Fin a)
    (v w : LittlePeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    (balancedPairingDataCoordinates a).symm
        ((balancedQuadraticDataOperator hα0 hα1 v w).val.toFun x) (Sum.inl i) =
      -((balancedQuadraticFirst (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
        hα1.le i v w).val.toFun x 0) := by
  rw [(balanced_pairing_data_coordinates_spec a).2.1,
    balancedQuadraticDataOperator_coordinate]
  change ((-1 : ℝ) • (balancedQuadraticFirst
    (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1) hα1.le i v w).val).toFun x 0 = _
  rw [(periodicCAlpha_pointwise_operations a 1 2 α).2.2]
  simp

/-- Each once-indexed second datum is exactly half of the complete original Qij
output, including the diagonal, with no duplicated nonsymmetric coordinates.
Source: Qcal preceding(4.3) in the proof of `lem:balanced`. -/
theorem balancedQuadraticDataOperator_second {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (ij : {p : Fin a × Fin a // p.1 ≤ p.2})
    (v w : LittlePeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    (balancedPairingDataCoordinates a).symm
        ((balancedQuadraticDataOperator hα0 hα1 v w).val.toFun x) (Sum.inr ij) =
      (balancedQuadraticSecond (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
        hα1.le ij.val.1 ij.val.2 v w).val.toFun x 0 / 2 := by
  rw [(balanced_pairing_data_coordinates_spec a).2.1,
    balancedQuadraticDataOperator_coordinate]
  change ((1 / 2 : ℝ) • (balancedQuadraticSecond
    (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
      hα1.le ij.val.1 ij.val.2 v w).val).toFun x 0 = _
  rw [(periodicCAlpha_pointwise_operations a 1 2 α).2.2]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Every actual data component is symmetric in its whole-function inputs, by the
proved symmetry of the actual scalar operators and the original scalar factors.
Source: symmetric Qcal in the proof of `lem:balanced`. -/
theorem balancedQuadraticDataComponent_symmetric {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (j : BalancedPairingIndex a)
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticDataComponent hα0 hα1 j v w =
      balancedQuadraticDataComponent hα0 hα1 j w v := by
  cases j with
  | inl i =>
      change (-1 : ℝ) • balancedQuadraticFirst _ _ i v w =
        (-1 : ℝ) • balancedQuadraticFirst _ _ i w v
      rw [balancedQuadraticFirst_symmetric]
  | inr ij =>
      change (1 / 2 : ℝ) • balancedQuadraticSecond _ _ ij.val.1 ij.val.2 v w =
        (1 / 2 : ℝ) • balancedQuadraticSecond _ _ ij.val.1 ij.val.2 w v
      rw [balancedQuadraticSecond_symmetric]

/-- The assembled actual whole-function Qcal is symmetric. Its finite bounded sum
inherits input symmetry from the genuine scalar component operators.
Source: the symmetric bilinear map Qcal preceding(4.3). -/
theorem balancedQuadraticDataOperator_symmetric {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticDataOperator hα0 hα1 v w =
      balancedQuadraticDataOperator hα0 hα1 w v := by
  classical
  simp only [balancedQuadraticDataOperator, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [balancedQuadraticDataComponent_symmetric]

/-- The actual bounded bilinear Qcal has one positive finite bound for every pair
of original little functions. This is the genuine norm of the constructed finite
operator assembly, with no assumed bound or desired Q as an input.
Source: uniform bilinear bounds used after(4.3) in `lem:balanced`. -/
theorem balancedQuadraticDataOperator_bound {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ v w : LittlePeriodicCAlphaFunction a N 2 α,
      ‖balancedQuadraticDataOperator hα0 hα1 v w‖ ≤ C * ‖v‖ * ‖w‖ :=
  (balancedQuadraticDataOperator hα0 hα1).isBoundedBilinearMap.bound

/-- The original zero-dimensional fiber has empty first and second data, hence its
actual Qcal is the zero bounded bilinear map. Source: the a=0 edge case of Qcal. -/
theorem balancedQuadraticDataOperator_zero_dimension {N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    balancedQuadraticDataOperator (a := 0) (N := N) hα0 hα1 = 0 := by
  simp [balancedQuadraticDataOperator, BalancedPairingIndex]

#print axioms balancedQuadraticDataOperator
#print axioms balancedQuadraticDataInjection_value
#print axioms balancedQuadraticDataOperator_coordinate
#print axioms balancedQuadraticDataOperator_first
#print axioms balancedQuadraticDataOperator_second
#print axioms balancedQuadraticDataOperator_symmetric
#print axioms balancedQuadraticDataOperator_bound
#print axioms balancedQuadraticDataOperator_zero_dimension

end GlobalEmbedding.Paper
