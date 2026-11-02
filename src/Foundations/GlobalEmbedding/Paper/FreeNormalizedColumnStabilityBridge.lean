import GlobalEmbedding.Paper.FreeCorrectionStability
import GlobalEmbedding.Paper.FreeNormalizedPolynomialColumns

/-!
# The exact normalized-column operator used by correction stability

Source: `main.tex`, `thm:free`, lines477–495.
DAG: `free-normalized-column-stability-bridge`.
The genuine coordinate masks and scale algebra are the accepted W4 definitions.
The actual normalized polynomial is identified with the actual projected and
rescaled columns of the stability estimate, without introducing another norm.
-/

noncomputable section
open scoped BigOperators Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual projected/rescaled column operator satisfies the genuine W4 scale identity.
Proof: evaluate on the actual Euclidean coefficients and sum the column identities;
the masked factors epsilon and epsilon inverse cancel exactly at nonzero epsilon. -/
theorem freeNormalizedColumnOperator_scale (prj : E →L[ℝ] E) (masked : ι → Bool)
    (ε : ℝ) (hε : ε ≠ 0) (v : ι → E) :
    (freeColumnOperator (freeNormalizedColumns prj masked ε v)).comp
      (freeColumnScale (freeCoordinateMask masked) ε) = prj.comp (freeColumnOperator v) := by
  have hcoord (u : EuclideanSpace ℝ ι) (i : ι) :
      freeColumnScale (freeCoordinateMask masked) ε u i =
        if masked i then ε * u i else u i := by
    simp only [freeColumnScale, add_apply, sub_apply, ContinuousLinearMap.id_apply,
      smul_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, freeCoordinateMask_apply]
    split <;> simp_all
  ext u
  simp only [ContinuousLinearMap.comp_apply, freeColumnOperator_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcoord]
  by_cases hi : masked i = true <;>
    simp [freeNormalizedColumns, hi, smul_smul, hε, mul_comm]

/-- Any genuine normalized operator with W4's exact scale identity is the operator
of the actual normalized columns used in stability.
Proof: the accepted inverse-scale identity makes the nonzero-epsilon scale
surjective. Cancel that common scale from the two actual operator identities. -/
theorem free_normalized_operator_eq_columns (prj : E →L[ℝ] E) (masked : ι → Bool)
    (ε : ℝ) (hε : ε ≠ 0) (v : ι → E) (B : EuclideanSpace ℝ ι →L[ℝ] E)
    (hscale : B.comp (freeColumnScale (freeCoordinateMask masked) ε) =
      prj.comp (freeColumnOperator v)) :
    B = freeColumnOperator (freeNormalizedColumns prj masked ε v) := by
  have hSD := freeColumnScale_comp_inverseScale (freeCoordinateMask masked)
    (freeCoordinateMask_idempotent masked) ε
  have hsurj : Function.Surjective (freeColumnScale (freeCoordinateMask masked) ε) := by
    intro u
    refine ⟨freeInverseScale (freeCoordinateMask masked) ε (ε⁻¹ • u), ?_⟩
    have hh := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι ↦
      L (ε⁻¹ • u)) hSD
    simpa only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      smul_smul, mul_inv_cancel₀ hε, one_smul] using hh
  ext u
  obtain ⟨w, rfl⟩ := hsurj u
  have hB := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] E ↦ L w) hscale
  have hN := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] E ↦ L w)
    (freeNormalizedColumnOperator_scale prj masked ε hε v)
  exact hB.trans hN.symm

/-- The actual accepted normalized polynomial is exactly the column operator required
for stability, once its actual unnormalized columns are identified.
Proof: apply the accepted genuine polynomial scale identity and the scale
uniqueness just proved; no polynomial derivative expansion is repeated. -/
theorem free_normalized_polynomial_eq_columns (prj : E →L[ℝ] E) (masked : ι → Bool)
    (A0 A1 A2 : EuclideanSpace ℝ ι →L[ℝ] E)
    (hbase : (prj.comp A0).comp (freeCoordinateMask masked) = 0)
    (ε : ℝ) (hε : ε ≠ 0) (v : ι → E)
    (hraw : freeColumnPolynomial A0 A1 A2 ε = freeColumnOperator v) :
    freeNormalizedColumnPolynomial prj (freeCoordinateMask masked) A0 A1 A2 ε =
      freeColumnOperator (freeNormalizedColumns prj masked ε v) := by
  apply free_normalized_operator_eq_columns prj masked ε hε v
  rw [freeNormalizedColumnPolynomial_scale prj _
    (freeCoordinateMask_idempotent masked) A0 A1 A2 hbase ε, hraw]

section ActualPairing

variable {V H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The adjoint of the original full pairing map is exactly the actual finite-column
operator used in stability, with both original Euclidean norms unchanged.
Proof: test the actual adjoint against any ambient vector. The Euclidean tuple
inner product is the finite sum of the actual column pairings, which is the inner
product with their genuine linear combination. No differentiability is needed. -/
theorem free_balanced_pairing_adjoint_eq_columnOperator {a N : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (D : Fin a → ∀ x : M, TangentSpace I x) (x : M) :
    (balancedPairingMap P D x).adjoint = freeColumnOperator (balancedPairingColumns P D x) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left, freeColumnOperator_apply, sum_inner]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left]
  change inner ℝ (u i) (inner ℝ (balancedPairingColumns P D x i) w) = _
  exact Real.inner_apply _ _

/-- The actual normalized polynomial of the same native F, Z and W is precisely
the normalized first/sorted-second column operator in the stability estimate.
Proof: reuse the accepted actual polynomial-pairing adjoint identity, identify
that adjoint with the true finite column operator, and apply scale uniqueness.
Only the genuine projected base annihilation is needed from the actual patch. -/
theorem free_actual_normalized_polynomial_eq_columns [IsManifold I ∞ M] {a N : ℕ}
    (F Z W : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z)
    (hW : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ W)
    (D : Fin a → ContMDiffSection I V ∞ (TangentSpace I : M → Type _)) (x : M)
    (prj : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (masked : BalancedPairingIndex a → Bool)
    (hbase : (prj.comp (balancedPairingMap F (fun i ↦ D i) x).adjoint).comp
      (freeCoordinateMask masked) = 0) (ε : ℝ) (hε : ε ≠ 0) :
    freeNormalizedColumnPolynomial prj (freeCoordinateMask masked)
      (balancedPairingMap F (fun i ↦ D i) x).adjoint
      (balancedPairingMap Z (fun i ↦ D i) x).adjoint
      (balancedPairingMap W (fun i ↦ D i) x).adjoint ε =
      freeColumnOperator (freeNormalizedColumns prj masked ε
        (balancedPairingColumns (freePolynomialFamily F Z W ε) (fun i ↦ D i) x)) := by
  apply free_normalized_polynomial_eq_columns prj masked _ _ _ hbase ε hε
  rw [← freePolynomialFamily_columnOperator F Z W hF hZ hW D ε x,
    free_balanced_pairing_adjoint_eq_columnOperator]

end ActualPairing

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeNormalizedColumnOperator_scale
#print axioms GlobalEmbedding.Paper.free_normalized_operator_eq_columns
#print axioms GlobalEmbedding.Paper.free_normalized_polynomial_eq_columns
#print axioms GlobalEmbedding.Paper.free_balanced_pairing_adjoint_eq_columnOperator
#print axioms GlobalEmbedding.Paper.free_actual_normalized_polynomial_eq_columns
