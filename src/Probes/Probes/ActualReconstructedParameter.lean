import Probes.FiniteModeParameterResponse
import GlobalEmbedding.Paper.IncrementsPrimaryReconstructedChannels

/-!
# Actual homogeneous reconstruction and real probe parameters

Source: main.tex (6.2), its finite reconstruction, and the first-step probe
construction in (8.3).  The output is the ORIGINAL
`incrementsPrimaryReconstructedChannel`, with its actual tangent Gram inverse,
normal inclusion, and transverse first-order correction.  Local smoothness is
required of the genuine finite-mode coefficient fields and source columns only.
No derivative of a surrogate correction is substituted for the native one.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Filter Set
open scoped Topology ContDiff BigOperators

namespace GlobalEmbedding.Continuation

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ} [Fintype ι]

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

/-- The actual reconstruction depends only on the input first germ. -/
theorem modeReconstruction_eq_of_eventuallyEq (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (u v : D → D) (x : D)
    (he : u =ᶠ[𝓝 x] v) :
    incrementsModeReconstruction F hF c u x = incrementsModeReconstruction F hF c v x := by
  simp only [incrementsModeReconstruction_split, he.eq_of_nhds, he.fderiv_eq]

/-- Finite source superposition is preserved by the SAME actual reconstruction.
Differentiability is checked before distributing the native spatial derivative. -/
theorem modeReconstruction_finiteProbeSource (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (g : ι → D → D) (u : ι → ℝ) (x : D)
    (hg : ∀ i, DifferentiableAt ℝ (g i) x) :
    incrementsModeReconstruction F hF c (finiteProbeSource g u) x =
      ∑ i, u i • incrementsModeReconstruction F hF c (g i) x := by
  simp only [incrementsModeReconstruction_split, finiteProbeSource]
  change _ + (incrementsModeReconstructionR1 F hF c x)
    (fderiv ℝ (fun y ↦ ∑ i, u i • g i y) x) = _
  have hd : fderiv ℝ (fun y ↦ ∑ i, u i • g i y) x =
      ∑ i, fderiv ℝ (fun y ↦ u i • g i y) x :=
    fderiv_fun_sum (u := Finset.univ) (fun i _ ↦ (hg i).const_smul (u i))
  rw [hd]
  simp only [fderiv_fun_const_smul (hg _), map_sum, map_smul,
    Finset.sum_add_distrib, smul_add]

/-- The true reconstructed channel expands in its true source columns on the
original open set. All spatial derivative germs are inherited from that set. -/
theorem primaryReconstructedParameter_eq_sum [DecidableEq ι]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) :
    incrementsPrimaryReconstructedChannel F hF c channel tau p (finiteProbeSource k u) x =
      ∑ i, u i • incrementsPrimaryReconstructedChannel F hF c channel tau p (k i) x := by
  let A := incrementsModeComplexFirstOrderA F hF c
  let B := incrementsModeComplexFirstOrderB F hF c
  let alpha := (tau : ℂ) / Complex.I
  let g : ι → D → D := fun i y ↦ channel (incrementsActualModeSum A B alpha p (k i) y)
  have hg (i : ι) : ContDiffOn ℝ ∞ (g i) O :=
    channel.contDiff.comp_contDiffOn
      (increments_actual_mode_sum_contDiffOn A B alpha p (k i) O hO hA hB (hk i))
  have he : (fun y ↦ channel
      (incrementsActualModeSum A B alpha p (finiteProbeSource k u) y))
      =ᶠ[𝓝 x] finiteProbeSource g u := by
    filter_upwards [hO.mem_nhds hx] with y hy
    rw [finiteModeParameter_eq_sum A B alpha p k O hO hA hB hk y hy u]
    simp only [map_sum, map_smul, finiteProbeSource, g]
  change incrementsModeReconstruction F hF c _ x = _
  rw [modeReconstruction_eq_of_eventuallyEq F hF c _ _ x he]
  exact modeReconstruction_finiteProbeSource F hF c g u x
    (fun i ↦ ((hg i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))

/-- Explicit continuous linear map of the real parameters, formed from the
original reconstructed source columns themselves. -/
def reconstructedParameterMap (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata) (x : D) :
    (ι → ℝ) →L[ℝ] V :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight
    (incrementsPrimaryReconstructedChannel F hF c channel tau p (k i) x)

theorem reconstructedParameterMap_apply (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (x : D) (u : ι → ℝ) :
    reconstructedParameterMap F hF c channel tau p k x u =
      ∑ i, u i • incrementsPrimaryReconstructedChannel F hF c channel tau p (k i) x := by
  simp only [reconstructedParameterMap, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

/-- Genuine parameter differentiation of the original homogeneous correction. -/
theorem hasFDerivAt_primaryReconstructedParameter [DecidableEq ι]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) :
    HasFDerivAt (fun w ↦ incrementsPrimaryReconstructedChannel F hF c channel tau p
      (finiteProbeSource k w) x) (reconstructedParameterMap F hF c channel tau p k x) u := by
  have he : (fun w ↦ incrementsPrimaryReconstructedChannel F hF c channel tau p
      (finiteProbeSource k w) x) = reconstructedParameterMap F hF c channel tau p k x := by
    funext w
    rw [primaryReconstructedParameter_eq_sum F hF c channel tau p k O hO hA hB hk x hx w,
      reconstructedParameterMap_apply]
  rw [he]
  exact (reconstructedParameterMap F hF c channel tau p k x).hasFDerivAt

/-- A real parameter column is the actual homogeneous correction of the same
source column, including the differentiated transverse reconstruction. -/
theorem fderiv_primaryReconstructedParameter_column [DecidableEq ι]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) (i : ι) :
    fderiv ℝ (fun w ↦ incrementsPrimaryReconstructedChannel F hF c channel tau p
      (finiteProbeSource k w) x) u (Pi.single i 1) =
        incrementsPrimaryReconstructedChannel F hF c channel tau p (k i) x := by
  rw [(hasFDerivAt_primaryReconstructedParameter F hF c channel tau p k O hO hA hB hk x hx u).fderiv,
    reconstructedParameterMap_apply]
  simp [Pi.single_apply]

/-- Every native spatial derivative of the parameter column is the derivative
of that SAME actual correction. This includes the spatial Hessian used in probes. -/
theorem iteratedFDeriv_fderiv_primaryReconstructedParameter_column [DecidableEq ι]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O)
    (u : ι → ℝ) (i : ι) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ
      (fun w ↦ incrementsPrimaryReconstructedChannel F hF c channel tau p
        (finiteProbeSource k w) y) u (Pi.single i 1)) x =
    iteratedFDeriv ℝ j (incrementsPrimaryReconstructedChannel F hF c channel tau p (k i)) x := by
  have he : (fun y ↦ fderiv ℝ
      (fun w ↦ incrementsPrimaryReconstructedChannel F hF c channel tau p
        (finiteProbeSource k w) y) u (Pi.single i 1))
      =ᶠ[𝓝 x] incrementsPrimaryReconstructedChannel F hF c channel tau p (k i) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact fderiv_primaryReconstructedParameter_column F hF c channel tau p k O hO hA hB hk y hy u i
  exact (he.iteratedFDeriv ℝ j).eq_of_nhds

/-- Probe reflection changes the sign of the actual correction, without any
assumption on the desired zero-phase mean. -/
theorem primaryReconstructedParameter_neg [DecidableEq ι]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : ι → D → Cdata)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) :
    incrementsPrimaryReconstructedChannel F hF c channel tau p (finiteProbeSource k (-u)) x =
      -incrementsPrimaryReconstructedChannel F hF c channel tau p (finiteProbeSource k u) x := by
  rw [primaryReconstructedParameter_eq_sum F hF c channel tau p k O hO hA hB hk x hx (-u),
    primaryReconstructedParameter_eq_sum F hF c channel tau p k O hO hA hB hk x hx u]
  simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.primaryReconstructedParameter_eq_sum
#print axioms GlobalEmbedding.Continuation.hasFDerivAt_primaryReconstructedParameter
#print axioms GlobalEmbedding.Continuation.iteratedFDeriv_fderiv_primaryReconstructedParameter_column
#print axioms GlobalEmbedding.Continuation.primaryReconstructedParameter_neg
