import Probes.ActualFullProbeFirstStep
import Probes.ActualTrueSecondFormParameter

/-!
# Fixed-connection response of the complete homogeneous first block

The derivatives are native derivatives of actualFiniteProbeWithReconstruction,
including every real/imaginary original solver channel. The connection is fixed
as required for the exact-metric bridge in ActualTrueSecondFormParameter.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Set Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Offline

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

-- Native nested operator structures, fixed to avoid redundant typeclass search.
private noncomputable local instance fullProbeBilinearSemi :
    SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance fullProbeBilinearNormed :
    NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance fullProbeBilinearNormedSpace :
    NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace


/-- Actual native first-jet parameter map of the combined first block. -/
def actualReconstructedProbeFirstJetMap (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (x : D) : (Fin p → ℝ) →L[ℝ] D →L[ℝ] V :=
  probePairedColumnMap label
    (fun i ↦ fderiv ℝ (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i)) x)
    (fun i ↦ fderiv ℝ (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i)) x) +
  ∑ l, probeColumnMap (fun q ↦ fderiv ℝ
    (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order (k l q)) x)

/-- The true first jet of the SAME combined family. -/
theorem actualFiniteProbeWithReconstruction_fderiv
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l) O)
    (hamplitude : ∀ l, ContDiffOn ℝ ∞ (amplitude l) O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ∀ l q, ContDiffOn ℝ ∞ (k l q) O)
    (u : Fin p → ℝ) (x : D) (hx : x ∈ O) :
    fderiv ℝ (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k u) x =
      actualReconstructedProbeFirstJetMap label δ τ weight phase amplitude F hF c order k x u := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  have hh := congrArg (fun T ↦ T ![v])
    (actualFiniteProbeWithReconstruction_spatial_jet label δ τ weight phase amplitude F hF c order k
      O hO hphase hamplitude hA hB hG hJ hT0 hk 1 u x hx)
  simpa [actualReconstructedProbeJetMap, actualReconstructedProbeFirstJetMap,
    probePairedColumnMap_apply, probeColumnMap_apply, sum_apply, add_apply, smul_apply] using hh

/-- Native parameter derivative after the actual first spatial derivative. -/
theorem hasFDerivAt_actualFiniteProbeWithReconstruction_fderiv
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l) O)
    (hamplitude : ∀ l, ContDiffOn ℝ ∞ (amplitude l) O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ∀ l q, ContDiffOn ℝ ∞ (k l q) O)
    (u : Fin p → ℝ) (x : D) (hx : x ∈ O) :
    HasFDerivAt (fun w ↦ fderiv ℝ
      (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k w) x)
      (actualReconstructedProbeFirstJetMap label δ τ weight phase amplitude F hF c order k x) u := by
  have heq := funext (fun w ↦ actualFiniteProbeWithReconstruction_fderiv label δ τ weight
    phase amplitude F hF c order k O hO hphase hamplitude hA hB hG hJ hT0 hk w x hx)
  rw [heq]
  exact (actualReconstructedProbeFirstJetMap label δ τ weight phase amplitude F hF c order k x).hasFDerivAt

/-- Actual parameter differentiation of the combined covariant Hessian. -/
theorem hasFDerivAt_actualFullProbeFixedConnectionHessian
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l) O)
    (hamplitude : ∀ l, ContDiffOn ℝ ∞ (amplitude l) O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ∀ l q, ContDiffOn ℝ ∞ (k l q) O)
    (Γ : D →L[ℝ] D →L[ℝ] D) (u : Fin p → ℝ) (x : D) (hx : x ∈ O) :
    HasFDerivAt (fun w ↦ probeFixedConnectionHessian Γ
      (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k w) x)
      (actualReconstructedProbeHessianMap label δ τ weight phase amplitude F hF c order k x -
        (probeConnectionComposition (F := V) Γ).comp
          (actualReconstructedProbeFirstJetMap label δ τ weight phase amplitude F hF c order k x)) u := by
  exact (hasFDerivAt_actualFiniteProbeWithReconstruction_hessian label δ τ weight
    phase amplitude F hF c order k O hO hphase hamplitude hA hB hG hJ hT0 hk u x hx).sub
      ((probeConnectionComposition (F := V) Γ).hasFDerivAt.comp u
        (hasFDerivAt_actualFiniteProbeWithReconstruction_fderiv label δ τ weight
          phase amplitude F hF c order k O hO hphase hamplitude hA hB hG hJ hT0 hk u x hx))

/-- The actual cos principal term including ALL homogeneous connection remainders. -/
theorem actualFullProbe_cos_fixed_connection_response
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l) O)
    (hamplitude : ∀ l, ContDiffOn ℝ ∞ (amplitude l) O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ∀ l q, ContDiffOn ℝ ∞ (k l q) O)
    (Γ : D →L[ℝ] D →L[ℝ] D) (u : Fin p → ℝ) (x : D) (hx : x ∈ O)
    (i : Fin r) (hτ : τ ≠ 0) (hw : weight i ≠ 0) :
    fderiv ℝ (fun w ↦ probeFixedConnectionHessian Γ
      (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k w) x) u
      (Pi.single (label (i, false)) 1) =
      ((δ / τ) * Real.cos (weight i * phase i x / τ)) •
        phaseRankOneHessian (phase i) (amplitude i) x +
      (actualProbeCosConnectionRemainder Γ δ τ (weight i) (phase i) (amplitude i) x +
        ∑ l, probeFixedConnectionHessian Γ
          (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order
            (k l (label (i, false)))) x) := by
  rw [(hasFDerivAt_actualFullProbeFixedConnectionHessian label δ τ weight phase amplitude F hF c
    order k O hO hphase hamplitude hA hB hG hJ hT0 hk Γ u x hx).fderiv]
  simp only [actualReconstructedProbeHessianMap, actualReconstructedProbeFirstJetMap,
    add_apply, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
    probePairedColumnMap_cos_column, probeColumnMap_column]
  rw [actualProbeCosColumn_hessian_at
    (((hphase i).contDiffAt (hO.mem_nhds hx)).of_le (by simp))
    (((hamplitude i).contDiffAt (hO.mem_nhds hx)).of_le (by simp)) δ τ (weight i) hτ hw]
  simp only [actualProbeCosConnectionRemainder, probeFixedConnectionHessian,
    map_add, map_sum, Finset.sum_sub_distrib]
  abel

/-- The actual sin principal term including ALL homogeneous connection remainders. -/
theorem actualFullProbe_sin_fixed_connection_response
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l) O)
    (hamplitude : ∀ l, ContDiffOn ℝ ∞ (amplitude l) O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) y)) O)
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (c y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c y)) O)
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hk : ∀ l q, ContDiffOn ℝ ∞ (k l q) O)
    (Γ : D →L[ℝ] D →L[ℝ] D) (u : Fin p → ℝ) (x : D) (hx : x ∈ O)
    (i : Fin r) (hτ : τ ≠ 0) (hw : weight i ≠ 0) :
    fderiv ℝ (fun w ↦ probeFixedConnectionHessian Γ
      (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k w) x) u
      (Pi.single (label (i, true)) 1) =
      ((δ / τ) * Real.sin (weight i * phase i x / τ)) •
        phaseRankOneHessian (phase i) (amplitude i) x +
      (actualProbeSinConnectionRemainder Γ δ τ (weight i) (phase i) (amplitude i) x +
        ∑ l, probeFixedConnectionHessian Γ
          (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order
            (k l (label (i, true)))) x) := by
  rw [(hasFDerivAt_actualFullProbeFixedConnectionHessian label δ τ weight phase amplitude F hF c
    order k O hO hphase hamplitude hA hB hG hJ hT0 hk Γ u x hx).fderiv]
  simp only [actualReconstructedProbeHessianMap, actualReconstructedProbeFirstJetMap,
    add_apply, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
    probePairedColumnMap_sin_column, probeColumnMap_column]
  rw [actualProbeSinColumn_hessian_at
    (((hphase i).contDiffAt (hO.mem_nhds hx)).of_le (by simp))
    (((hamplitude i).contDiffAt (hO.mem_nhds hx)).of_le (by simp)) δ τ (weight i) hτ hw]
  simp only [actualProbeSinConnectionRemainder, probeFixedConnectionHessian,
    map_add, map_sum, Finset.sum_sub_distrib]
  abel

#print axioms actualFullProbe_cos_fixed_connection_response
#print axioms actualFullProbe_sin_fixed_connection_response
end GlobalEmbedding.Offline
