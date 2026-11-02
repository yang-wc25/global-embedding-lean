import GlobalEmbedding.Paper.BalancedPairingDataCoordinates
import GlobalEmbedding.Paper.HilbertSchmidtCoordinateEvaluation
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Faithful smooth coefficients for every arbitrary pairing right inverse

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 376–418.
DAG node: `balanced-pairing-inverse-coordinates`.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Faithful continuous linear coordinates for every map from the full actual pairing
space to the Euclidean target. Reindex the domain by the unique fixed Data/Fin isometry,
then use the already proved actual Hilbert–Schmidt coefficient equivalence. Both steps
are equivalences on all operators; no column-span condition or right inverse is presumed.
The coordinate norm is Hilbert–Schmidt, rather than asserted equal to the operator norm. -/
noncomputable def balancedPairingInverseCoordinates (a N : ℕ) :
    (EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ] EuclideanSpace ℝ (Fin N)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N * Fintype.card (BalancedPairingIndex a))) :=
  let e := hilbertSchmidtCoordinateEquiv (Fintype.card (BalancedPairingIndex a)) N
  ((balancedPairingDataCoordinates a).toContinuousLinearEquiv.arrowCongr
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N)))).trans
      e.symm.toContinuousLinearEquiv

/-- Actual Hilbert–Schmidt evaluation of these coordinates recovers the original
arbitrary operator, with the specified domain reindexing, and scaling commutes exactly.
Cancel the genuine coefficient equivalence and domain isometry. This is the value bridge
needed by the already constructed actual little Hölder pointwise multiplier. -/
theorem balanced_pairing_inverse_coordinates_spec (a N : ℕ) :
    (∀ C z, hilbertSchmidtCoordinateEvaluation (Fintype.card (BalancedPairingIndex a)) N
      (balancedPairingInverseCoordinates a N C) z =
        C ((balancedPairingDataCoordinates a).symm z)) ∧
    (∀ C u, hilbertSchmidtCoordinateEvaluation (Fintype.card (BalancedPairingIndex a)) N
      (balancedPairingInverseCoordinates a N C) (balancedPairingDataCoordinates a u) =
        C u) ∧
    (∀ C (ε : ℝ), balancedPairingInverseCoordinates a N (ε • C) =
      ε • balancedPairingInverseCoordinates a N C) := by
  have heval (C : EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
      (z : EuclideanSpace ℝ (Fin (Fintype.card (BalancedPairingIndex a)))) :
      hilbertSchmidtCoordinateEvaluation (Fintype.card (BalancedPairingIndex a)) N
        (balancedPairingInverseCoordinates a N C) z =
          C ((balancedPairingDataCoordinates a).symm z) := by
    change (hilbertSchmidtCoordinateEquiv (Fintype.card (BalancedPairingIndex a)) N)
      ((hilbertSchmidtCoordinateEquiv (Fintype.card (BalancedPairingIndex a)) N).symm
        (((balancedPairingDataCoordinates a).toContinuousLinearEquiv.arrowCongr
          (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N)))) C)) z = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨heval, ?_, fun C ε ↦ map_smul (balancedPairingInverseCoordinates a N) ε C⟩
  intro C u
  rw [heval, LinearIsometryEquiv.symm_apply_apply]

/-- A genuinely smooth-through-zero arbitrary inverse family has genuinely smooth
actual coefficient coordinates on its original domain. Compose its actual CLM-valued
family with the constructed continuous linear coordinate equivalence. The domain may be
only the original open parameter neighborhood; no extension to the whole real axis or
condition on its zero value is imposed. -/
theorem balanced_pairing_inverse_coordinates_contMDiffOn
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
    (a N : ℕ) (s : Set M)
    (C : M → EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (hC : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) ∞ C s) :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ
      (Fin (N * Fintype.card (BalancedPairingIndex a)))) ∞
      (fun x ↦ balancedPairingInverseCoordinates a N (C x)) s := by
  exact (balancedPairingInverseCoordinates a N).toContinuousLinearMap.contDiff.contMDiff.comp_contMDiffOn hC

end GlobalEmbedding.Paper
