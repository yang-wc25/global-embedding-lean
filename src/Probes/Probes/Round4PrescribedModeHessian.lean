import Probes.Round4PrescribedPhysicalResponse
import Probes.Round4PrescribedReconstructedColumns

/-! Local native Hessian columns of the SAME complete original mode. These
identities connect the global observed Hessian to its actual local principal
estimate without postulating a response or mixed-derivative interchange. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff BigOperators Topology
namespace GlobalEmbedding.Continuation
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

private local instance modeHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance modeHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance modeHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

theorem round4_actual_mode_hessian_response_column
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x))
    (phi : D → ℝ) (tau : ℝ) (length : ℕ) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hG : ContDiffOn ℝ ∞ (fun x => freeGramRightInverse (fderiv ℝ (F ∘ c) x)) O)
    (hJ : ContDiffOn ℝ ∞ (fun x => (normalSpace (I := I) F (c x)).subtypeL.comp
      (incrementsModeCoordinateJ F hF c x)) O)
    (hT : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F c) O)
    (hBR : ContDiffOn ℝ ∞ (fun x => fun k : Fin (m+1) =>
      (incrementsModeSecondForm F hF c x 0 k : V)) O)
    (hvf : ContDiffOn ℝ ∞ (fun x => (vf x : V)) O) (hphi : ContDiffOn ℝ ∞ phi O)
    (u : Fin p → ℝ) (x : D) (hx : x ∈ O) (q : Fin p) :
    fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ
      (round4ActualProbeMode label l F hF c vf phi tau length v)) x) u (Pi.single q 1) =
      fderiv ℝ (fderiv ℝ (round4ActualProbeMode label l F hF c vf phi tau length (Pi.single q 1))) x := by
  let wave := round4ActualProbeMode label l F hF c vf phi tau length
  have hsm (v : Fin p → ℝ) : ContDiffOn ℝ ∞ (wave v) O := by
    have hamp (ch : Bool) := round4PrescribedAmplitude_contDiffOn ch label l F hF c vf
      tau length O hO hA hB hG hJ hT hBR hvf v
    have hh := (((hphi.div_const tau).cos).smul (hamp false)).sub
      (((hphi.div_const tau).sin).smul (hamp true))
    exact hh.congr (fun y hy => round4ActualProbeMode_eq_amplitudes label l F hF c vf phi tau length v y)
  have hs := round4_actual_homogeneous_source_smooth F hF c vf O hBR hvf
  let J := probeColumnMap (fun k => fderiv ℝ (fderiv ℝ (wave (Pi.single k 1))) x)
  have hjet (v : Fin p → ℝ) : iteratedFDeriv ℝ 2 (wave v) x =
      probeColumnMap (fun k => iteratedFDeriv ℝ 2 (wave (Pi.single k 1)) x) v := by
    have he := eventuallyEq_of_mem (hO.mem_nhds hx) (fun y hy =>
      round4ActualProbeMode_finite_source label l F hF c vf phi tau length O hO hA hB hs v y hy)
    rw [(he.iteratedFDeriv ℝ 2).eq_of_nhds]
    exact iteratedFDeriv_finiteProbeSource _ v 2 x (fun k =>
      ((hsm (Pi.single k 1)).contDiffAt (hO.mem_nhds hx)).of_le (by simp))
  have heq (v : Fin p → ℝ) : fderiv ℝ (fderiv ℝ (wave v)) x = J v := by
    apply ContinuousLinearMap.ext
    intro d
    apply ContinuousLinearMap.ext
    intro e
    have hh := congrArg (fun T => T ![d,e]) (hjet v)
    simpa [J,probeColumnMap_apply,iteratedFDeriv_two_apply,Fin.sum_univ_two,sum_apply,smul_apply] using hh
  have hf : (fun v => fderiv ℝ (fderiv ℝ (wave v)) x) = J := funext heq
  change fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (wave v)) x) u (Pi.single q 1) = _
  rw [hf,J.hasFDerivAt.fderiv,probeColumnMap_apply]
  simp [Pi.single_apply,wave]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_mode_hessian_response_column
