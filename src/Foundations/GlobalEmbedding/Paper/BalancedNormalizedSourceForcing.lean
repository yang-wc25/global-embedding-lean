import GlobalEmbedding.Paper.BalancedPairingDataCoordinates
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic.Ring

/-!
# The literal normalized residual datum and source forcing

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`,
equation (4.3) and its scaled pairings, lines 403–418.
DAG node: `balanced-normalized-source-forcing`.
-/

open Set WithLp Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual raw tuple in (4.3), with first entries zero and each ordered second
entry included once with the original factor one half. Data and its index are the
existing complete pairing space, without a new enumeration or a matrix norm. -/
noncomputable def balancedNormalizedResidualData {a : ℕ} (t : ℝ)
    (S3 S4 : Matrix (Fin a) (Fin a) ℝ) : EuclideanSpace ℝ (BalancedPairingIndex a) :=
  toLp 2 (fun i ↦ match i with
    | Sum.inl _ => 0
    | Sum.inr p => (t * S3 p.val.1 p.val.2 + t ^ 2 * S4 p.val.1 p.val.2) / 2)

/-- The same literal raw datum in the unique fixed Fin coordinates. -/
noncomputable def balancedNormalizedResidualCoordinates {a : ℕ} (t : ℝ)
    (S3 S4 : Matrix (Fin a) (Fin a) ℝ) :
    EuclideanSpace ℝ (Fin (Fintype.card (BalancedPairingIndex a))) :=
  balancedPairingDataCoordinates a (balancedNormalizedResidualData t S3 S4)

/-- The literal normalized inverse as a value operator on the unique Fin data coordinates.
Its range remains arbitrary, and its value at time zero is unconstrained. -/
noncomputable def balancedNormalizedSourceOperator {a N : ℕ}
    (Ctilde : EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin (Fintype.card (BalancedPairingIndex a))) →L[ℝ]
      EuclideanSpace ℝ (Fin N) :=
  Ctilde.comp (balancedPairingDataCoordinates a).symm.toContinuousLinearMap

/-- The original N-valued forcing in (4.3), obtained by applying the actual normalized
inverse to the raw residual tuple before solving the whole-function fixed equation. -/
noncomputable def balancedNormalizedSourceForcing {a N : ℕ}
    (Ctilde : EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) (t : ℝ) (S3 S4 : Matrix (Fin a) (Fin a) ℝ) :
    EuclideanSpace ℝ (Fin N) :=
  Ctilde (balancedNormalizedResidualData t S3 S4)

/-- Exact raw, Fin-coordinate and t²-scaled raw values in the original pairing index.
Evaluate the literal tuple and the sole proved coordinate isometry. Scalar polynomial
algebra gives the original cubic/quartic residual after multiplication by t².
Source: (4.3) and the pairings immediately following it. -/
theorem balanced_normalized_residual_data_spec {a : ℕ} (t : ℝ)
    (S3 S4 : Matrix (Fin a) (Fin a) ℝ) :
    (∀ i, balancedNormalizedResidualData t S3 S4 (Sum.inl i) = 0) ∧
    (∀ p : {p : Fin a × Fin a // p.1 ≤ p.2},
      balancedNormalizedResidualData t S3 S4 (Sum.inr p) =
        (t * S3 p.val.1 p.val.2 + t ^ 2 * S4 p.val.1 p.val.2) / 2) ∧
    (∀ i, balancedNormalizedResidualCoordinates t S3 S4
      (Fintype.equivFin (BalancedPairingIndex a) i) =
        balancedNormalizedResidualData t S3 S4 i) ∧
    (∀ i, (t ^ 2 • balancedNormalizedResidualData t S3 S4) (Sum.inl i) = 0) ∧
    (∀ p : {p : Fin a × Fin a // p.1 ≤ p.2},
      (t ^ 2 • balancedNormalizedResidualData t S3 S4) (Sum.inr p) =
        (t ^ 3 * S3 p.val.1 p.val.2 + t ^ 4 * S4 p.val.1 p.val.2) / 2) := by
  refine ⟨fun _ ↦ rfl, fun _ ↦ rfl,
    (balanced_pairing_data_coordinates_spec a).1 _, ?_, ?_⟩
  · intro i
    change t ^ 2 * 0 = 0
    exact mul_zero _
  · intro p
    change t ^ 2 * ((t * S3 p.val.1 p.val.2 + t ^ 2 * S4 p.val.1 p.val.2) / 2) = _
    ring

/-- The raw polynomial vanishes at zero, and therefore so does the actual forcing
for every normalized operator, without any condition on that operator's zero value.
The forcing also equals the actual Fin-coordinate source operator applied to the same
raw datum in Fin coordinates. These are equality of actual values, not just norms.
Proof: all zero-time coordinates are zero, linear maps send zero to zero, and the
fixed coordinate isometry cancels its inverse. Source: forcing and scaling in (4.3). -/
theorem balanced_normalized_source_forcing_spec {a N : ℕ}
    (Ctilde : EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) (t : ℝ) (S3 S4 : Matrix (Fin a) (Fin a) ℝ) :
    balancedNormalizedResidualData 0 S3 S4 = 0 ∧
      balancedNormalizedResidualCoordinates 0 S3 S4 = 0 ∧
      balancedNormalizedSourceForcing Ctilde 0 S3 S4 = 0 ∧
      balancedNormalizedSourceForcing Ctilde t S3 S4 =
        balancedNormalizedSourceOperator Ctilde
          (balancedNormalizedResidualCoordinates t S3 S4) := by
  have hd : balancedNormalizedResidualData 0 S3 S4 = 0 := by
    ext i
    cases i <;> simp [balancedNormalizedResidualData]
  refine ⟨hd, ?_, ?_, ?_⟩
  · unfold balancedNormalizedResidualCoordinates
    rw [hd, map_zero]
  · unfold balancedNormalizedSourceForcing
    rw [hd, map_zero]
  · unfold balancedNormalizedSourceForcing balancedNormalizedSourceOperator
      balancedNormalizedResidualCoordinates
    change Ctilde _ = Ctilde ((balancedPairingDataCoordinates a).symm
      (balancedPairingDataCoordinates a (balancedNormalizedResidualData t S3 S4)))
    rw [LinearIsometryEquiv.symm_apply_apply]

section NativeSmoothness

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]

/-- The literal raw datum and its fixed Fin coordinates are genuinely native smooth
when time and each fixed coefficient entry are. No norm on matrices is chosen.
Proof: the existing finite product criterion proves smoothness entry by entry, then
compose with the genuine PiLp linear coordinates and sole fixed Data-to-Fin isometry.
Source: the actual normalized forcing in (4.3). -/
theorem balanced_normalized_residual_data_contMDiffOn {a : ℕ} {s : Set X}
    (t : X → ℝ) (S3 S4 : X → Matrix (Fin a) (Fin a) ℝ)
    (ht : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ t s)
    (hS3 : ∀ i j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x ↦ S3 x i j) s)
    (hS4 : ∀ i j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x ↦ S4 x i j) s) :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex a)) ∞
      (fun x ↦ balancedNormalizedResidualData (t x) (S3 x) (S4 x)) s ∧
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ
        (Fin (Fintype.card (BalancedPairingIndex a)))) ∞
        (fun x ↦ balancedNormalizedResidualCoordinates (t x) (S3 x) (S4 x)) s := by
  have hp : ContMDiffOn I 𝓘(ℝ, BalancedPairingIndex a → ℝ) ∞
      (fun x (i : BalancedPairingIndex a) ↦ match i with
        | Sum.inl _ => (0 : ℝ)
        | Sum.inr p => (t x * S3 x p.val.1 p.val.2 +
            (t x) ^ 2 * S4 x p.val.1 p.val.2) / 2) s := by
    apply contMDiffOn_pi_module_iff.mpr
    intro i
    cases i with
    | inl i => exact contMDiffOn_const
    | inr p =>
      exact ((ht.mul (hS3 p.val.1 p.val.2)).add
        ((ht.pow 2).mul (hS4 p.val.1 p.val.2))).div_const 2
  have hd : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex a)) ∞
      (fun x ↦ balancedNormalizedResidualData (t x) (S3 x) (S4 x)) s :=
    PiLp.contDiff_toLp.contMDiff.comp_contMDiffOn hp
  refine ⟨hd, ?_⟩
  exact (balancedPairingDataCoordinates a).toContinuousLinearMap.contDiff.contMDiff
    |>.comp_contMDiffOn hd

/-- Actual normalized coefficients and forcing inherit native smoothness on their
original source domain, including time zero with unconstrained normalized inverse.
Compose the smooth actual normalized operator with the fixed inverse data coordinates;
apply it to the proved smooth actual raw datum. Source: (4.3). -/
theorem balanced_normalized_source_contMDiffOn {a N : ℕ} {s : Set X}
    (t : X → ℝ) (S3 S4 : X → Matrix (Fin a) (Fin a) ℝ)
    (Ctilde : X → EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (ht : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ t s)
    (hS3 : ∀ i j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x ↦ S3 x i j) s)
    (hS4 : ∀ i j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x ↦ S4 x i j) s)
    (hC : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) ∞ Ctilde s) :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ
      (Fin (Fintype.card (BalancedPairingIndex a))) →L[ℝ]
        EuclideanSpace ℝ (Fin N)) ∞
      (fun x ↦ balancedNormalizedSourceOperator (Ctilde x)) s ∧
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (fun x ↦ balancedNormalizedSourceForcing (Ctilde x) (t x) (S3 x) (S4 x)) s := by
  refine ⟨hC.clm_comp contMDiffOn_const, ?_⟩
  exact hC.clm_apply (balanced_normalized_residual_data_contMDiffOn t S3 S4 ht hS3 hS4).1

end NativeSmoothness

#print axioms balancedNormalizedResidualData
#print axioms balancedNormalizedResidualCoordinates
#print axioms balancedNormalizedSourceOperator
#print axioms balancedNormalizedSourceForcing
#print axioms balanced_normalized_residual_data_spec
#print axioms balanced_normalized_source_forcing_spec
#print axioms balanced_normalized_residual_data_contMDiffOn
#print axioms balanced_normalized_source_contMDiffOn

end GlobalEmbedding.Paper
