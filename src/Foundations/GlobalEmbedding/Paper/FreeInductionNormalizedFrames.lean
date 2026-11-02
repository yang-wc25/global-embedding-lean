import GlobalEmbedding.Paper.FreeInductionBaseNormalization

/-!
# Actual near and far normalized frames of the same induction polynomial

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 477–495.
DAG: `free-induction-normalized-frames`. Exclusive owner W4.
-/
noncomputable section
open scoped Manifold ContDiff
namespace GlobalEmbedding.Paper

variable {m K : ℕ} (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]
variable (H : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
variable (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
variable (Z W : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))

/-- Literal projected near polynomial, with the canonical actual base, masks and adjoints. -/
def freeHopfInductionNearFrame (p : ℝ × FreeHopfProduct C) :
    EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (K + (2 + m))) :=
  freeNormalizedColumnPolynomial
    (freeInductionNearProjection K m
      (orbitDeriv planarHopfFlow f (freeHopfProductSplit C p.2).2))
    (freeCoordinateMask (freeNearColumnMask m))
    (balancedPairingMap (freeHopfInductionBase C H f) (freeHopfGenerator C) p.2).adjoint
    (balancedPairingMap Z (freeHopfGenerator C) p.2).adjoint
    (balancedPairingMap W (freeHopfGenerator C) p.2).adjoint p.1

/-- Literal unprojected far polynomial of the same base and displacement/correction. -/
def freeHopfInductionFarFrame (p : ℝ × FreeHopfProduct C) :
    EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (K + (2 + m))) :=
  freeNormalizedColumnPolynomial (ContinuousLinearMap.id ℝ _)
    (freeCoordinateMask (freeFarColumnMask m))
    (balancedPairingMap (freeHopfInductionBase C H f) (freeHopfGenerator C) p.2).adjoint
    (balancedPairingMap Z (freeHopfGenerator C) p.2).adjoint
    (balancedPairingMap W (freeHopfGenerator C) p.2).adjoint p.1

variable (hH : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
  𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
variable (hf : MatrixPlanarSelectorProperties f)
variable (hZ : ContMDiff (freeHopfModel C)
  𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ Z)
variable (hW : ContMDiff (freeHopfModel C)
  𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ W)

include hH hf hZ hW in
/-- Both actual normalized families are jointly native smooth through epsilon zero.
Only genuine smoothness of the same maps is supplied; no normalized regularity is a premise. -/
theorem freeHopfInductionFrames_contMDiff :
    ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ (freeHopfInductionNearFrame C H f Z W) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ (freeHopfInductionFarFrame C H f Z W) := by
  let adjEquiv := ContinuousLinearMap.adjoint (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin (K + (2 + m))))
    (F := EuclideanSpace ℝ (BalancedPairingIndex (m + 1)))
  let adj := adjEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hcoeff (F : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))
      (hF : ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ F) :
      ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C))
        𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞
        (fun p : ℝ × FreeHopfProduct C ↦
          (balancedPairingMap F (freeHopfGenerator C) p.2).adjoint) :=
    (adj.contDiff.contMDiff.comp
      (freePairingMap_contMDiff F hF (freeHopfGeneratorSection C))).comp contMDiff_snd
  have hF := freeHopfInductionBase_contMDiff C H hH f hf.smooth
  have hlast : ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      (planarHopfModel (C (Fin.last m))) ∞
      (fun p : ℝ × FreeHopfProduct C ↦ (freeHopfProductSplit C p.2).2) :=
    (contMDiff_snd.comp (freeHopfProductSplit_contMDiff C)).comp contMDiff_snd
  have hprj := (freeInductionNearProjection_selector_contMDiff K m _ f hf).comp hlast
  exact ⟨freeNormalizedColumnPolynomial_contMDiff _ _ _ _ _ _ hprj
    (hcoeff _ hF) (hcoeff _ hZ) (hcoeff _ hW) contMDiff_fst,
    freeNormalizedColumnPolynomial_contMDiff _ _ _ _ _ _ contMDiff_const
      (hcoeff _ hF) (hcoeff _ hZ) (hcoeff _ hW) contMDiff_fst⟩

include hH hf hZ hW in
/-- The original full pairing map of the same polynomial has exactly the near adjoint-scale
factorization. The base-annihilation premise is discharged by the genuine base geometry. -/
theorem freeHopfInductionNearFrame_adjoint_scale (ε : ℝ) (x : FreeHopfProduct C) :
    (balancedPairingMap (freePolynomialFamily (freeHopfInductionBase C H f) Z W ε)
      (freeHopfGenerator C) x).comp
        (freeInductionNearProjection K m
          (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2)) =
      (freeColumnScale (freeCoordinateMask (freeNearColumnMask m)) ε).comp
        (freeHopfInductionNearFrame C H f Z W (ε, x)).adjoint := by
  have hs := freeNormalizedColumnPolynomial_adjoint
    (freeInductionNearProjection K m
      (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2))
    (freeInductionNearProjection_adjoint K m _)
    (freeCoordinateMask (freeNearColumnMask m))
    (freeCoordinateMask_idempotent _) (freeCoordinateMask_adjoint _)
    (balancedPairingMap (freeHopfInductionBase C H f) (freeHopfGenerator C) x).adjoint
    (balancedPairingMap Z (freeHopfGenerator C) x).adjoint
    (balancedPairingMap W (freeHopfGenerator C) x).adjoint
    (freeInductionBase_near_operator_zero C H hH f hf x) ε
  have hp := freePolynomialFamily_columnOperator _ _ _
    (freeHopfInductionBase_contMDiff C H hH f hf.smooth) hZ hW
    (freeHopfGeneratorSection C) ε x
  change (balancedPairingMap (freePolynomialFamily (freeHopfInductionBase C H f) Z W ε)
      (freeHopfGenerator C) x).adjoint =
    freeColumnPolynomial
      (balancedPairingMap (freeHopfInductionBase C H f) (freeHopfGenerator C) x).adjoint
      (balancedPairingMap Z (freeHopfGenerator C) x).adjoint
      (balancedPairingMap W (freeHopfGenerator C) x).adjoint ε at hp
  rw [← hp, ContinuousLinearMap.adjoint_adjoint] at hs
  exact hs

include hH hf hZ hW in
/-- The same original full pairing map has the far adjoint-scale factorization,
with no target projection and no restriction of the data range. -/
theorem freeHopfInductionFarFrame_adjoint_scale (ε : ℝ) (x : FreeHopfProduct C) :
    balancedPairingMap (freePolynomialFamily (freeHopfInductionBase C H f) Z W ε)
      (freeHopfGenerator C) x =
      (freeColumnScale (freeCoordinateMask (freeFarColumnMask m)) ε).comp
        (freeHopfInductionFarFrame C H f Z W (ε, x)).adjoint := by
  have hb : ((ContinuousLinearMap.id ℝ _).comp
      (balancedPairingMap (freeHopfInductionBase C H f) (freeHopfGenerator C) x).adjoint).comp
        (freeCoordinateMask (freeFarColumnMask m)) = 0 := by
    rw [ContinuousLinearMap.id_comp]
    exact freeInductionBase_far_operator_zero C H hH f hf.smooth x
  have hs := freeNormalizedColumnPolynomial_adjoint (ContinuousLinearMap.id ℝ _)
    (ContinuousLinearMap.adjoint_id)
    (freeCoordinateMask (freeFarColumnMask m))
    (freeCoordinateMask_idempotent _) (freeCoordinateMask_adjoint _)
    (balancedPairingMap (freeHopfInductionBase C H f) (freeHopfGenerator C) x).adjoint
    (balancedPairingMap Z (freeHopfGenerator C) x).adjoint
    (balancedPairingMap W (freeHopfGenerator C) x).adjoint hb ε
  have hp := freePolynomialFamily_columnOperator _ _ _
    (freeHopfInductionBase_contMDiff C H hH f hf.smooth) hZ hW
    (freeHopfGeneratorSection C) ε x
  change (balancedPairingMap (freePolynomialFamily (freeHopfInductionBase C H f) Z W ε)
      (freeHopfGenerator C) x).adjoint =
    freeColumnPolynomial
      (balancedPairingMap (freeHopfInductionBase C H f) (freeHopfGenerator C) x).adjoint
      (balancedPairingMap Z (freeHopfGenerator C) x).adjoint
      (balancedPairingMap W (freeHopfGenerator C) x).adjoint ε at hp
  rw [← hp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_id] at hs
  exact hs

#print axioms freeHopfInductionNearFrame
#print axioms freeHopfInductionFarFrame
#print axioms freeHopfInductionFrames_contMDiff
#print axioms freeHopfInductionNearFrame_adjoint_scale
#print axioms freeHopfInductionFarFrame_adjoint_scale

end GlobalEmbedding.Paper
