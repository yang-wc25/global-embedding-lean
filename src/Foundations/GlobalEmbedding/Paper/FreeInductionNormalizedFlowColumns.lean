import GlobalEmbedding.Paper.FreeInductionBaseNormalization

/-!
# The two actual normalized polynomials equal the original normalized flow columns

Source: `main.tex`, `thm:free`, lines477–495.
DAG: `free-induction-normalized-flow-columns`; exclusive F3 owner W2.
All expressions use the existing same F0/Z/W, projections and masks. B definitions,
smoothness, scales, margins, rank, gluing and the full inverse remain W4's scope.
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise

namespace GlobalEmbedding.Paper

variable {m K : ℕ} (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]

local instance freeNormalizedFlowMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance freeNormalizedFlowOldPositive (i : Fin m) :
    Fact (0 < freeHopfOldDimensions C i) := inferInstanceAs (Fact (0 < C i.castSucc))

variable
    (H ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hIH : FreeSelectorProperties (freeHopfModel (freeHopfOldDimensions C))
      (freeHopfProductFlow (freeHopfOldDimensions C)) H ν)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar) (hf : MatrixPlanarSelectorProperties f)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η) (δ : ℝ)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (W : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))
    (hW : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ W)
    (ε : ℝ) (hε : ε ≠ 0) (x : FreeHopfProduct C)

include hIH hf hP hQ hη hA hn hW hε in
/-- The actual expanded near normalized polynomial equals the genuine column
operator of the original normalized Hopf-flow columns of the same P_epsilon.

Proof: construct true native smoothness of the fixed literal F0 and Z from the
same IH and data. The accepted actual near base-annihilation theorem supplies the
exact zero operator required by the accepted polynomial normalization bridge.
Apply that bridge and convert its actual balanced columns to the original literal
flow columns using the accepted generator/flow correspondence on this very smooth
polynomial slice. No raw-column equality or base-annihilation input is assumed.
Source: the projected near normalization in main.tex477–489. -/
theorem freeHopfInductionNearPolynomial_eq_flowColumns :
    freeNormalizedColumnPolynomial
      (freeInductionNearProjection K m
        (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2))
      (freeCoordinateMask (freeNearColumnMask m))
      (balancedPairingMap (freeHopfInductionBase C H f) (freeHopfGenerator C) x).adjoint
      (balancedPairingMap (freeHopfInductionZ C ν P Q η δ A n) (freeHopfGenerator C) x).adjoint
      (balancedPairingMap W (freeHopfGenerator C) x).adjoint ε =
      freeColumnOperator (freeNormalizedColumns
        (freeInductionNearProjection K m
          (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2))
        (freeNearColumnMask m) ε
        (freeFlowColumns (freeHopfProductFlow C)
          (freePolynomialFamily (freeHopfInductionBase C H f)
            (freeHopfInductionZ C ν P Q η δ A n) W ε) x)) := by
  have hF := freeHopfInductionBase_contMDiff C H hIH.1 f hf.smooth
  have hZ := freeHopfInductionZ_contMDiff C ν hIH.2.1 P Q hP hQ η hη δ A n hA hn
  have hbase := freeInductionBase_near_operator_zero C H hIH.1 f hf x
  have he := free_actual_normalized_polynomial_eq_columns
    (freeHopfInductionBase C H f) (freeHopfInductionZ C ν P Q η δ A n) W hF hZ hW
    (freeHopfGeneratorSection C) x
    (freeInductionNearProjection K m
      (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2))
    (freeNearColumnMask m) hbase ε hε
  simp only [freeHopfGeneratorSection, ContMDiffSection.coeFn_mk] at he
  rw [freeHopf_balanced_pairing_columns C _
    (freePolynomialFamily_contMDiff _ _ _ hF hZ hW ε) x] at he
  exact he

include hIH hf hP hQ hη hA hn hW hε in
/-- The actual expanded far normalized polynomial equals the genuine column
operator of the original normalized Hopf-flow columns of the same P_epsilon.

Proof: the accepted actual far base-annihilation theorem kills precisely the
canonical mixed mask. Identity projection changes no actual column. Apply the
same accepted normalization bridge to the same fixed F0/Z/W and use the genuine
native balanced/flow-column correspondence on the same polynomial slice.
There is no new normalized family or supplied operator equality.
Source: the unprojected far normalization in main.tex477–489. -/
theorem freeHopfInductionFarPolynomial_eq_flowColumns :
    freeNormalizedColumnPolynomial (ContinuousLinearMap.id ℝ _)
      (freeCoordinateMask (freeFarColumnMask m))
      (balancedPairingMap (freeHopfInductionBase C H f) (freeHopfGenerator C) x).adjoint
      (balancedPairingMap (freeHopfInductionZ C ν P Q η δ A n) (freeHopfGenerator C) x).adjoint
      (balancedPairingMap W (freeHopfGenerator C) x).adjoint ε =
      freeColumnOperator (freeNormalizedColumns (ContinuousLinearMap.id ℝ _)
        (freeFarColumnMask m) ε
        (freeFlowColumns (freeHopfProductFlow C)
          (freePolynomialFamily (freeHopfInductionBase C H f)
            (freeHopfInductionZ C ν P Q η δ A n) W ε) x)) := by
  have hF := freeHopfInductionBase_contMDiff C H hIH.1 f hf.smooth
  have hZ := freeHopfInductionZ_contMDiff C ν hIH.2.1 P Q hP hQ η hη δ A n hA hn
  have hbase : ((ContinuousLinearMap.id ℝ _).comp
      (balancedPairingMap (freeHopfInductionBase C H f) (freeHopfGenerator C) x).adjoint).comp
      (freeCoordinateMask (freeFarColumnMask m)) = 0 := by
    rw [ContinuousLinearMap.id_comp]
    convert freeInductionBase_far_operator_zero C H hIH.1 f hf.smooth x using 1; rfl
  have he := free_actual_normalized_polynomial_eq_columns
    (freeHopfInductionBase C H f) (freeHopfInductionZ C ν P Q η δ A n) W hF hZ hW
    (freeHopfGeneratorSection C) x (ContinuousLinearMap.id ℝ _)
    (freeFarColumnMask m) hbase ε hε
  simp only [freeHopfGeneratorSection, ContMDiffSection.coeFn_mk] at he
  rw [freeHopf_balanced_pairing_columns C _
    (freePolynomialFamily_contMDiff _ _ _ hF hZ hW ε) x] at he
  exact he

end GlobalEmbedding.Paper
