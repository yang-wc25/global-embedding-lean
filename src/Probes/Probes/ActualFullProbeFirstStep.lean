import Probes.ActualRealHomogeneousBounds

/-!
# Actual free probe plus all original homogeneous reconstructions

This is a single finite parameter family. Its free part is the previously
used paired-value principal map; each homogeneous term is the original finite
solver with both real and imaginary channels. The native parameter derivative
AFTER the actual spatial Hessian is proved directly for the combined family.
Background/secondary metric corrections and the infinite repair tail are not
included in this first-step homogeneous block.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Filter Set Manifold
open scoped ContDiff Topology BigOperators
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

/-- Literal free paired waves plus every actual real homogeneous correction,
using the SAME finite source parameters in the original finite solver. -/
def actualFiniteProbeWithReconstruction (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (u : Fin p → ℝ) (x : D) : V :=
  actualFiniteProbeDisplacement label δ τ weight phase amplitude u x +
    ∑ l, actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order
      (finiteProbeSource (k l) u) x

/-- The actual native n-jet parameter map of the full homogeneous first block. -/
def actualReconstructedProbeJetMap (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (n : ℕ) (x : D) :
    (Fin p → ℝ) →L[ℝ] D [×n]→L[ℝ] V :=
  probePairedColumnMap label
    (fun i ↦ iteratedFDeriv ℝ n (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i)) x)
    (fun i ↦ iteratedFDeriv ℝ n (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i)) x) +
  ∑ l, probeColumnMap (fun q ↦ iteratedFDeriv ℝ n
    (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order (k l q)) x)

/-- The actual Hessian parameter map in the original nested CLM representation. -/
def actualReconstructedProbeHessianMap (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ) (amplitude : Fin r → D → V)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (order : ℕ) (k : Fin r → Fin p → D → Cdata)
    (x : D) :
    (Fin p → ℝ) →L[ℝ] D →L[ℝ] D →L[ℝ] V :=
  probePairedColumnMap label
    (fun i ↦ fderiv ℝ (fderiv ℝ (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i))) x)
    (fun i ↦ fderiv ℝ (fderiv ℝ (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i))) x) +
  ∑ l, probeColumnMap (fun q ↦ fderiv ℝ (fderiv ℝ
    (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order (k l q))) x)

/-- The actual spatial jet is the proved continuous linear parameter map. -/
theorem actualFiniteProbeWithReconstruction_spatial_jet
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
    (hk : ∀ l q, ContDiffOn ℝ ∞ (k l q) O) (n : ℕ)
    (u : Fin p → ℝ) (x : D) (hx : x ∈ O) :
    iteratedFDeriv ℝ n
      (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k u) x =
      actualReconstructedProbeJetMap label δ τ weight phase amplitude F hF c order k n x u := by
  classical
  have hph l : ContDiffAt ℝ n (phase l) x :=
    ((hphase l).contDiffAt (hO.mem_nhds hx)).of_le (by simp)
  have ham l : ContDiffAt ℝ n (amplitude l) x :=
    ((hamplitude l).contDiffAt (hO.mem_nhds hx)).of_le (by simp)
  have hfree : ContDiffAt ℝ n (actualFiniteProbeDisplacement label δ τ weight phase amplitude u) x := by
    have heq := funext (fun y ↦ actualFiniteProbeDisplacement_eq_sum label δ τ weight phase amplitude u y)
    rw [heq]
    exact ContDiffAt.sum (fun i _ ↦
      ((contDiffAt_actualProbeCosColumn (hph i) (ham i) δ τ (weight i)).const_smul _).add
        ((contDiffAt_actualProbeSinColumn (hph i) (ham i) δ τ (weight i)).const_smul _))
  have hrec l : ContDiffAt ℝ n
      (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) F hF c τ order
        (finiteProbeSource (k l) u)) x :=
    ((actualRealHomogeneousProbe_contDiffOn _ F hF c τ order _ O hO
      ((hphase l).const_smul (weight l)) hA hB hG hJ hT0
      (finiteProbeSource_contDiffOn (k l) O (hk l) u)).contDiffAt
        (hO.mem_nhds hx)).of_le (by simp)
  change iteratedFDeriv ℝ n (fun y ↦
    actualFiniteProbeDisplacement label δ τ weight phase amplitude u y +
      ∑ l, actualRealHomogeneousProbe (fun z ↦ weight l * phase l z) F hF c τ order
        (finiteProbeSource (k l) u) y) x = _
  rw [fun_iteratedFDeriv_add_apply hfree (ContDiffAt.sum (fun l _ ↦ hrec l)),
    iteratedFDeriv_fun_sum_apply (fun l _ ↦ hrec l),
    actualFiniteProbeDisplacement_iteratedFDeriv n label δ τ weight phase amplitude u x hph ham]
  simp only [actualReconstructedProbeJetMap, add_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact actualRealHomogeneousProbe_spatial_jet _ F hF c τ order (k l) O hO
    ((hphase l).const_smul (weight l)) hA hB hG hJ hT0 (hk l) x hx u n

/-- Native parameter differentiation after arbitrary spatial differentiation
of the SAME complete free-plus-homogeneous block. -/
theorem hasFDerivAt_actualFiniteProbeWithReconstruction_spatial_jet
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
    (hk : ∀ l q, ContDiffOn ℝ ∞ (k l q) O) (n : ℕ)
    (u : Fin p → ℝ) (x : D) (hx : x ∈ O) :
    HasFDerivAt (fun w ↦ iteratedFDeriv ℝ n
      (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k w) x)
      (actualReconstructedProbeJetMap label δ τ weight phase amplitude F hF c order k n x) u := by
  have heq := funext (fun w ↦ actualFiniteProbeWithReconstruction_spatial_jet label δ τ weight
    phase amplitude F hF c order k O hO hphase hamplitude hA hB hG hJ hT0 hk n w x hx)
  rw [heq]
  exact (actualReconstructedProbeJetMap label δ τ weight phase amplitude F hF c order k n x).hasFDerivAt

/-- The same native combined Hessian, with exact original parameter labels. -/
theorem actualFiniteProbeWithReconstruction_hessian
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
    fderiv ℝ (fderiv ℝ
      (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k u)) x =
      actualReconstructedProbeHessianMap label δ τ weight phase amplitude F hF c order k x u := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hh := congrArg (fun T ↦ T ![v, w])
    (actualFiniteProbeWithReconstruction_spatial_jet label δ τ weight phase amplitude F hF c order k
      O hO hphase hamplitude hA hB hG hJ hT0 hk 2 u x hx)
  simpa [actualReconstructedProbeJetMap, actualReconstructedProbeHessianMap,
    probePairedColumnMap_apply, probeColumnMap_apply, sum_apply, add_apply, smul_apply,
    iteratedFDeriv_two_apply] using hh

/-- The actual mixed parameter/Hessian derivative is proved for the combined family. -/
theorem hasFDerivAt_actualFiniteProbeWithReconstruction_hessian
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
    HasFDerivAt (fun w ↦ fderiv ℝ (fderiv ℝ
      (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k w)) x)
      (actualReconstructedProbeHessianMap label δ τ weight phase amplitude F hF c order k x) u := by
  have heq := funext (fun w ↦ actualFiniteProbeWithReconstruction_hessian label δ τ weight
    phase amplitude F hF c order k O hO hphase hamplitude hA hB hG hJ hT0 hk w x hx)
  rw [heq]
  exact (actualReconstructedProbeHessianMap label δ τ weight phase amplitude F hF c order k x).hasFDerivAt

/-- Exact cosine principal term for the complete original homogeneous first block.
The retained remainder consists of the actual slow free-wave remainder and
the actual spatial Hessians of both-channel reconstructed source columns. -/
theorem actualFullProbe_cos_hessian_response
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
    (u : Fin p → ℝ) (x : D) (hx : x ∈ O) (i : Fin r)
    (hτ : τ ≠ 0) (hw : weight i ≠ 0) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ
      (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k w)) x) u
      (Pi.single (label (i, false)) 1) =
      ((δ / τ) * Real.cos (weight i * phase i x / τ)) •
          phaseRankOneHessian (phase i) (amplitude i) x +
      (actualProbeCosRemainder δ τ (weight i) (phase i) (amplitude i) x +
        ∑ l, fderiv ℝ (fderiv ℝ (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y)
          F hF c τ order (k l (label (i, false))))) x) := by
  rw [(hasFDerivAt_actualFiniteProbeWithReconstruction_hessian label δ τ weight phase amplitude
    F hF c order k O hO hphase hamplitude hA hB hG hJ hT0 hk u x hx).fderiv]
  simp only [actualReconstructedProbeHessianMap, add_apply, sum_apply,
    probePairedColumnMap_cos_column, probeColumnMap_column]
  rw [actualProbeCosColumn_hessian_at
    (((hphase i).contDiffAt (hO.mem_nhds hx)).of_le (by simp))
    (((hamplitude i).contDiffAt (hO.mem_nhds hx)).of_le (by simp)) δ τ (weight i) hτ hw]
  abel

/-- The matching exact sine principal term for the SAME combined family. -/
theorem actualFullProbe_sin_hessian_response
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
    (u : Fin p → ℝ) (x : D) (hx : x ∈ O) (i : Fin r)
    (hτ : τ ≠ 0) (hw : weight i ≠ 0) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ
      (actualFiniteProbeWithReconstruction label δ τ weight phase amplitude F hF c order k w)) x) u
      (Pi.single (label (i, true)) 1) =
      ((δ / τ) * Real.sin (weight i * phase i x / τ)) •
          phaseRankOneHessian (phase i) (amplitude i) x +
      (actualProbeSinRemainder δ τ (weight i) (phase i) (amplitude i) x +
        ∑ l, fderiv ℝ (fderiv ℝ (actualRealHomogeneousProbe (fun y ↦ weight l * phase l y)
          F hF c τ order (k l (label (i, true))))) x) := by
  rw [(hasFDerivAt_actualFiniteProbeWithReconstruction_hessian label δ τ weight phase amplitude
    F hF c order k O hO hphase hamplitude hA hB hG hJ hT0 hk u x hx).fderiv]
  simp only [actualReconstructedProbeHessianMap, add_apply, sum_apply,
    probePairedColumnMap_sin_column, probeColumnMap_column]
  rw [actualProbeSinColumn_hessian_at
    (((hphase i).contDiffAt (hO.mem_nhds hx)).of_le (by simp))
    (((hamplitude i).contDiffAt (hO.mem_nhds hx)).of_le (by simp)) δ τ (weight i) hτ hw]
  abel

#print axioms hasFDerivAt_actualFiniteProbeWithReconstruction_spatial_jet
#print axioms actualFullProbe_cos_hessian_response
#print axioms actualFullProbe_sin_hessian_response
end GlobalEmbedding.Offline
