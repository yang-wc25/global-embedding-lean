import GlobalEmbedding.Paper.BalancedPairingRightInverse
import GlobalEmbedding.Paper.BalancedQuadraticDataOperator
import GlobalEmbedding.Paper.BalancedNormalizedSourceForcing

/-!
# Actual whole-function fixed branches give the original native pairings

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines403–418.
DAG node: `balanced-actual-fixed-branch-pairings`.
-/

open Manifold

namespace GlobalEmbedding.Paper

/-- The literal evaluated source equation gives the original first/second pairings.

The raw tuple is the actual normalized residual, without requiring a little-space carrier
for it. Apply the actual full pairing right inverse to the evaluated equation, multiply
by epsilon, and use bilinearity of the actual nonlocal Qcal on entire little functions.
Only after Qcal has acted do we evaluate its actual coordinates. The proved original
Qi/Qij coordinate formulas then give the source signs, half factor and cubic/quartic
residual. No restriction on the inverse image or value of its normalization at zero
is imposed. This proof even retains epsilon zero whenever an actual right inverse exists. -/
theorem balanced_actual_fixed_branch_pairings
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
    {N a : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (P : M → EuclideanSpace ℝ (Fin N))
    (D : Fin a → ∀ x : M, TangentSpace I x) (x : M)
    (C Ctilde : EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (hC : IsBalancedPairingRightInverse P D x C)
    (ε : ℝ) (hnormalized : Ctilde = ε • C)
    (S3 S4 : Matrix (Fin a) (Fin a) ℝ)
    (v : LittlePeriodicCAlphaFunction a N 2 α) (z : EuclideanSpace ℝ (Fin a))
    (hv : v.val.toFun z = Ctilde (balancedNormalizedResidualData ε S3 S4) +
      Ctilde ((balancedPairingDataCoordinates a).symm
        ((balancedQuadraticDataOperator hα0 hα1 v v).val.toFun z))) :
    (∀ i, inner ℝ (balancedDirectionalDerivative P (D i) x) ((ε • v).val.toFun z) =
      -((balancedQuadraticFirst (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
        hα1.le i (ε • v) (ε • v)).val.toFun z 0)) ∧
    (∀ ij : {p : Fin a × Fin a // p.1 ≤ p.2},
      2 * inner ℝ (balancedDirectionalDerivative
        (balancedDirectionalDerivative P (D ij.val.2)) (D ij.val.1) x)
        ((ε • v).val.toFun z) =
        ε ^ 3 * S3 ij.val.1 ij.val.2 + ε ^ 4 * S4 ij.val.1 ij.val.2 +
          (balancedQuadraticSecond (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
            hα1.le ij.val.1 ij.val.2 (ε • v) (ε • v)).val.toFun z 0) := by
  obtain ⟨ev, hev, _⟩ := collar_little_holder_evaluation (N := N) (k := 2) (α := α) z
  obtain ⟨evData, hevData, _⟩ := collar_little_holder_evaluation
    (N := Fintype.card (BalancedPairingIndex a)) (k := 2) (α := α) z
  let out := (balancedPairingDataCoordinates a).symm.toContinuousLinearMap.comp evData
  have hout (w : LittlePeriodicCAlphaFunction a
      (Fintype.card (BalancedPairingIndex a)) 2 α) :
      out w = (balancedPairingDataCoordinates a).symm (w.val.toFun z) := by
    simp only [out, ContinuousLinearMap.comp_apply, hevData]
    rfl
  let Q := balancedQuadraticDataOperator (a := a) (N := N) hα0 hα1
  have hscaled : out (Q (ε • v) (ε • v)) = ε ^ 2 • out (Q v v) := by
    simp only [map_smul, smul_apply, smul_smul, pow_two]
  have hv' : ev v = (ε • C)
      (balancedNormalizedResidualData ε S3 S4 + out (Q v v)) := by
    rw [hev, hv, hnormalized, hout, map_add]
  have hCv (d : EuclideanSpace ℝ (BalancedPairingIndex a)) :
      balancedPairingMap P D x (C d) = d := congrArg (fun T ↦ T d) hC
  have hp : balancedPairingMap P D x ((ε • v).val.toFun z) =
      ε ^ 2 • balancedNormalizedResidualData ε S3 S4 + out (Q (ε • v) (ε • v)) := by
    calc
      balancedPairingMap P D x ((ε • v).val.toFun z) =
          ε • balancedPairingMap P D x (ev v) := by rw [← hev, map_smul, map_smul]
      _ = ε ^ 2 • balancedNormalizedResidualData ε S3 S4 + out (Q (ε • v) (ε • v)) := by
        rw [hv', smul_apply, map_smul, hCv, hscaled]
        simp only [smul_add, smul_smul, pow_two]
  rw [hout] at hp
  constructor
  · intro i
    have he := congrArg (fun d : EuclideanSpace ℝ (BalancedPairingIndex a) ↦
      d (Sum.inl i)) hp
    change inner ℝ (balancedDirectionalDerivative P (D i) x) ((ε • v).val.toFun z) =
      ε ^ 2 * balancedNormalizedResidualData ε S3 S4 (Sum.inl i) +
        (balancedPairingDataCoordinates a).symm
          ((Q (ε • v) (ε • v)).val.toFun z) (Sum.inl i) at he
    rw [(balanced_normalized_residual_data_spec ε S3 S4).1,
      balancedQuadraticDataOperator_first] at he
    simpa only [mul_zero, zero_add] using he
  · intro ij
    have he := congrArg (fun d : EuclideanSpace ℝ (BalancedPairingIndex a) ↦
      d (Sum.inr ij)) hp
    change inner ℝ (balancedDirectionalDerivative
        (balancedDirectionalDerivative P (D ij.val.2)) (D ij.val.1) x)
        ((ε • v).val.toFun z) =
      (ε ^ 2 • balancedNormalizedResidualData ε S3 S4) (Sum.inr ij) +
        (balancedPairingDataCoordinates a).symm
          ((Q (ε • v) (ε • v)).val.toFun z) (Sum.inr ij) at he
    rw [(balanced_normalized_residual_data_spec ε S3 S4).2.2.2.2,
      balancedQuadraticDataOperator_second] at he
    linarith

end GlobalEmbedding.Paper
