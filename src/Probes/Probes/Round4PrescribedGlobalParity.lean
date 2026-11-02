import Probes.Round4PrescribedReconstructedColumns
import GlobalEmbedding.Paper.IncrementsGlobalPrimaryMeanBinding

/-!
# Reflection of the same prescribed amplitudes after actual chart pullback

The full amplitudes, including the original finite source solver and its
spatial reconstruction derivative, are extended by the original chart formula.
Their oddness is derived from the actual source columns on the chart target.
This is an equality of entire spatial fields, so subsequent native spatial
and manifold derivatives preserve it. No parameter-space norm on a space of
smooth tensor fields is introduced.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Pspace" => Fin p → ℝ

/-- Original conditional chart pullback of the complete prescribed amplitude.
No new output cutoff is multiplied onto the finite reconstruction. -/
def round4PrescribedGlobalAmplitude
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (Ep × M) (Ep × D))
    (u : Pspace) (z : Ep × M) : V := by
  classical
  exact if z ∈ a.source then
    round4PrescribedAmplitude imag label l (F (a z).1) (hF (a z).1) (c (a z).1)
      (vf (a z).1) tau length u (a z).2 else 0

theorem round4PrescribedGlobalAmplitude_neg
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (Ep × M) (Ep × D))
    (hA : ContDiffOn ℝ ∞ (fun z : Ep × D =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hB : ContDiffOn ℝ ∞ (fun z : Ep × D =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hBR : ContDiffOn ℝ ∞ (fun z : Ep × D => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) a.target)
    (hvf : ContDiffOn ℝ ∞ (fun z : Ep × D => (vf z.1 z.2 : V)) a.target)
    (u : Pspace) :
    round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a (-u) =
      -round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a u := by
  classical
  funext z
  by_cases hz : z ∈ a.source
  · let b := (a z).1
    let y := (a z).2
    let O := (fun x : D => (b,x)) ⁻¹' a.target
    have hO : IsOpen O := a.open_target.preimage (continuous_const.prodMk continuous_id)
    have hy : y ∈ O := a.map_source hz
    have hAs := hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (by intro x hx; exact hx : MapsTo (fun x : D => (b,x)) O a.target)
    have hBs := hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (by intro x hx; exact hx : MapsTo (fun x : D => (b,x)) O a.target)
    have hBRs := hBR.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (by intro x hx; exact hx : MapsTo (fun x : D => (b,x)) O a.target)
    have hvfs := hvf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (by intro x hx; exact hx : MapsTo (fun x : D => (b,x)) O a.target)
    have hs := round4_actual_homogeneous_source_smooth (F b) (hF b) (c b) (vf b) O hBRs hvfs
    have hneg := round4PrescribedAmplitude_finite_source imag label l (F b) (hF b) (c b)
      (vf b) tau length O hO hAs hBs hs (-u) y hy
    have hpos := round4PrescribedAmplitude_finite_source imag label l (F b) (hF b) (c b)
      (vf b) tau length O hO hAs hBs hs u y hy
    simp only [round4PrescribedGlobalAmplitude,hz,ite_true,Pi.neg_apply]
    change round4PrescribedAmplitude imag label l (F b) (hF b) (c b) (vf b) tau length (-u) y = _
    rw [hneg,hpos]
    simp only [finiteProbeSource,Pi.neg_apply,neg_smul,Finset.sum_neg_distrib]
  · simp only [round4PrescribedGlobalAmplitude,hz,ite_false,Pi.neg_apply,neg_zero]

omit [IsManifold I ∞ M] [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] in
/-- Native source-only differentiation respects the equality of full fields,
including the target tangent cast used by the original metric. -/
theorem round4_global_spatial_derivative_neg (f : Ep × M → V) (z : Ep × M) :
    incrementsGlobalSpatialDerivative (I := I) (-f) z =
      -incrementsGlobalSpatialDerivative (I := I) f z := by
  change mfderiv I 𝓘(ℝ,V) (-(fun x => f (z.1,x))) z.2 =
    -mfderiv I 𝓘(ℝ,V) (fun x => f (z.1,x)) z.2
  exact mfderiv_neg

/-- The actual native coefficient of the complete chart-extended amplitudes.
The Boolean labels the imaginary channel, consistently with the prescribed
source convention. -/
def round4PrescribedNativeCoefficient
    (imag : Bool) (phi : Ep × M → ℝ) (tau : ℝ)
    (R Q : Ep × M → V) (z : Ep × M) : TangentSpace I z.2 →L[ℝ] V :=
  let slow := incrementsGlobalSpatialDerivative (I := I) (if imag then Q else R) z
  let fast := (incrementsGlobalScalarDerivative (I := I) phi z).smulRight
    (tau⁻¹ • (if imag then R z else Q z))
  if imag then slow + fast else slow - fast

omit [IsManifold I ∞ M] [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] in
theorem round4PrescribedNativeCoefficient_neg
    (imag : Bool) (phi : Ep × M → ℝ) (tau : ℝ)
    (R Q : Ep × M → V) (z : Ep × M) :
    round4PrescribedNativeCoefficient (I := I) imag phi tau (-R) (-Q) z =
      -round4PrescribedNativeCoefficient (I := I) imag phi tau R Q z := by
  cases imag <;>
    simp only [round4PrescribedNativeCoefficient,Bool.false_eq_true,ite_false,ite_true]
  all_goals rw [round4_global_spatial_derivative_neg]
  all_goals ext v; simp [ContinuousLinearMap.smulRight_apply,sub_eq_add_neg,add_comm]


end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4PrescribedGlobalAmplitude_neg
#print axioms GlobalEmbedding.Continuation.round4_global_spatial_derivative_neg
#print axioms GlobalEmbedding.Continuation.round4PrescribedNativeCoefficient_neg
