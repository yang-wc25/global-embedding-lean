import GlobalEmbedding.Paper.BalancedPairing

/-!
# Fixed isometric coordinates for the full actual pairing-data space

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 376.
DAG node: `balanced-pairing-data-coordinates`.
-/

namespace GlobalEmbedding.Paper

/-- One fixed linear isometry from the actual first/once-indexed-second tuple to the
`Fin R` Euclidean target used by the existing little Hölder spaces, where `R=a+s_a`.
Only the enumeration changes: every actual data coordinate remains independent.
Use its inverse after evaluating a `Fin R`-valued little function to recover actual
pairing data; this never imposes any restriction on a right inverse's range. -/
noncomputable def balancedPairingDataCoordinates (a : ℕ) :
    EuclideanSpace ℝ (BalancedPairingIndex a) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (BalancedPairingIndex a))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin (BalancedPairingIndex a))

/-- The fixed coordinate isometry preserves exactly every actual coordinate in both
directions and preserves both Euclidean norms. The finite-domain PiLp isometry supplies
norm preservation, and the inverse enumeration cancels by the equivalence laws.
In particular the actual nonlocal output can be evaluated before this coordinate change. -/
theorem balanced_pairing_data_coordinates_spec (a : ℕ) :
    (∀ z i, balancedPairingDataCoordinates a z
      (Fintype.equivFin (BalancedPairingIndex a) i) = z i) ∧
    (∀ z i, (balancedPairingDataCoordinates a).symm z i =
      z (Fintype.equivFin (BalancedPairingIndex a) i)) ∧
    (∀ z, ‖balancedPairingDataCoordinates a z‖ = ‖z‖) ∧
    (∀ z, ‖(balancedPairingDataCoordinates a).symm z‖ = ‖z‖) := by
  refine ⟨?_, ?_, (balancedPairingDataCoordinates a).norm_map,
    (balancedPairingDataCoordinates a).symm.norm_map⟩
  · intro z i
    change z ((Fintype.equivFin (BalancedPairingIndex a)).symm
      (Fintype.equivFin (BalancedPairingIndex a) i)) = z i
    rw [Equiv.symm_apply_apply]
  · intro z i
    have h := congrArg (fun w : EuclideanSpace ℝ
      (Fin (Fintype.card (BalancedPairingIndex a))) ↦
        w (Fintype.equivFin (BalancedPairingIndex a) i))
      ((balancedPairingDataCoordinates a).apply_symm_apply z)
    change ((balancedPairingDataCoordinates a).symm z)
      ((Fintype.equivFin (BalancedPairingIndex a)).symm
        (Fintype.equivFin (BalancedPairingIndex a) i)) = _ at h
    simpa only [Equiv.symm_apply_apply] using h

end GlobalEmbedding.Paper
