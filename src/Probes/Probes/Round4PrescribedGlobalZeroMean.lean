import Probes.Round4PrescribedObservedMean
import Probes.Round4PrescribedGlobalSmooth

/-!
# Actual globally reconstructed prescribed mean equals the genuine zero germ

This consumes only the primitive source smoothness/support, chart data and real
phase noncriticality. Smoothness and support of the complete amplitudes come
from the original finite reconstruction and conditional chart extension. The
result identifies their original four-phase selector with the native tensor.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Pspace" => Fin p → ℝ

theorem round4_prescribed_global_zero_native_mean
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) W)
    (b : Ep) (obs : D → M) (x : D) (hxW : (b,obs x) ∈ W) (htau : tau ≠ 0)
    (hobs : ContMDiffAt 𝓘(ℝ,D) I ∞ obs x)
    (hdouble : ∀ l, (b,obs x) ∈ K l →
      fderiv ℝ (fun y => phase l (b,obs y)+phase l (b,obs y)) x ≠ 0)
    (hinteraction : ∀ l k, l ≠ k → (b,obs x) ∈ K l → (b,obs x) ∈ K k →
      fderiv ℝ (fun y => phase l (b,obs y)+phase k (b,obs y)) x ≠ 0 ∧
      fderiv ℝ (fun y => phase l (b,obs y)-phase k (b,obs y)) x ≠ 0)
    (u : Pspace) (j k : Fin (m+1)) :
    let R := fun l => round4PrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) u
    let Q := fun l => round4PrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) u
    let w := fun s : Fin (m+1) => mfderiv 𝓘(ℝ,D) I obs x
      ((tangentSpaceCastModel 𝓘(ℝ,D) x).symm (EuclideanSpace.single s 1))
    (round4ObservedZeroMean phase tau R Q b obs x j k).re =
      round4PrescribedNativeMean label F hF c vf phase tau length a u b (obs x) (w j) (w k) := by
  intro R Q w
  have ha (l : Fin r) (ch : Bool) := round4_prescribed_global_amplitude_smooth ch label l F hF
    (c l) (vf l) tau length (a l) W (K l) hW (hK l) (hKsource l) (hchart l)
    (hA l) (hB l) (hG l) (hJ l) (hT l) (hBR l) (hvf l) (hinput l) u
  exact round4_observed_zero_native_mean phase tau R Q W K hW
    (fun l => (ha l false).2) (fun l => (ha l true).2) b obs x hxW htau
    (fun l => (hphase l).contMDiffAt (hW.mem_nhds hxW))
    (fun l => (ha l false).1.contMDiffAt (hW.mem_nhds hxW))
    (fun l => (ha l true).1.contMDiffAt (hW.mem_nhds hxW))
    hobs hdouble hinteraction j k

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_zero_native_mean
