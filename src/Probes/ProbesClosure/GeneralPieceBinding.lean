import ProbesClosure.GeneralPieceGeometry
import NormalPolar.OriginalWaveSeedSupportedRaw

/-!
# Primitive two-channel binding for arbitrary-cutoff prescribed pieces

This record contains only source identities and geometric facts manufactured
from the actual general source family. The raw solver, physical geometry,
phase, original normal value and full source carrier are the same objects.
The genuine reconstructed paired wave is then defined without introducing
new parameter coordinates for subordinate partition pieces.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
open scoped ContDiff Topology BigOperators Classical

namespace GlobalEmbedding.Continuation
variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
namespace GeneralLegalWaveRawFamily
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

def pieceBinding (family : GeneralLegalWaveRawFamily F hF waves weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hweight : ∀ l, 0 < weight l)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1)
    (l : Fin r) (s : Fin (family.piece l).seed.refinement.count)
    (length : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1) :
    GlobalWaveSupportedProbeBinding
      (fun _ : Fin 1 => (waves l).phase)
      (fun _ : Fin 1 => (family.piece l).seed.pieceValue s)
      (fun _ : Fin 1 => (family.piece l).seed.pieceCarrier s)
      (fun _ : Fin 1 => ((family.piece l).seed.inner s).chart)
      (fun _ : Fin 1 => weight l)
      (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
      (fun _ : Fin 1 => (family.piece l).seed.coordinate s)
      (fun _ : Fin 1 => (family.piece l).seed.cutoffCoordinates s)
      (fun _ : Fin 1 => (family.piece l).seed.scaledNormal c hc s)
      (fun _ : Fin 1 => fun z : Z × M => weight l * (waves l).phase z.2)
      (fun _ : Fin 1 => (family.piece l).seed.physicalChart s)
      univ (fun _ : Fin 1 => (family.piece l).seed.carrier s)
      ell (family.geometryBudget (max (2+length+1) 2))
      (family.cutoffBudget (2+length+1)) (family.normalBudget (2+length+1))
      (fun _ : Fin 1 => family.raw c hc l s (2+length+1) 2 ell hell hell1) (default : Z) where
  geometry := fun _ => (family.piece l).seed.physicalGeometry (hweight l) hImm c hc s
  source_inside := fun _ => subset_univ _
  coordinates := fun _ _ _ => rfl
  target := fun _ _ hy => ⟨mem_univ _,hy⟩
  phase_original := by
    intro _ y hy
    apply (div_eq_iff (hweight l).ne').mpr
    exact (((family.piece l).seed.inner s).inverse_phase y hy).symm.trans (mul_comm _ _)
  amplitude_original := fun _ _ _ => rfl
  samples := by
    intro _ x hx
    rw [family.raw_sample]
    exact ⟨mem_univ _,((family.piece l).seed.inner s).chart.map_source
      ((family.piece l).seed.pieceCarrier_source s hx)⟩
  slice := fun _ => mem_univ _
  carrier := fun _ _ hz => hz.2

def piecePairMap (family : GeneralLegalWaveRawFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1)
    (l : Fin r) (s : Fin (family.piece l).seed.refinement.count)
    (delta tau : ℝ) (length : ℕ) (u : ProbeParameters 1) (x : M) : V :=
  round4PrescribedGlobalWave (round4PairedParameterIndex 1).toEmbedding
    (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
    (fun _ : Fin 1 => (family.piece l).seed.coordinate s)
    (fun _ : Fin 1 => actualProbeNormalAmplitude (fun _ : Z => c • F)
      ((family.piece l).seed.coordinate s) ((family.piece l).seed.cutoffCoordinates s)
      ((family.piece l).seed.scaledNormal c hc s) delta tau (weight l))
    (fun _ : Fin 1 => fun z : Z × M => weight l * (waves l).phase z.2)
    tau length (fun _ : Fin 1 => (family.piece l).seed.physicalChart s)
    (probeParameterEmbedding (round4PairedParameterIndex 1).toEmbedding u) (default,x)

end GeneralLegalWaveRawFamily
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.pieceBinding
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.piecePairMap
