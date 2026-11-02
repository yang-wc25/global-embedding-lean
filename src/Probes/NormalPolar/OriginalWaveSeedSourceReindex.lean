import NormalPolar.OriginalWaveSeedPairProjection
import Probes.Round4PrescribedGlobalParity
import NormalPolar.FullResponseScales
import Probes.Round4OriginalProbeParameters

/-! Reindexing changes neither source nor reconstructed amplitude: an
original label reads exactly its two original parameter coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Continuation GlobalEmbedding.Upgrade

theorem originalProbeEmbedding_apply_label {r p : ℕ}
    (label : (Fin r × Bool) ↪ Fin p) (u : ProbeParameters r) (q : Fin r × Bool) :
    probeParameterEmbedding label u (label q) = u q := by
  change Function.extend label u 0 (label q) = u q
  exact label.injective.extend_apply _ _ q

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N p r p' r' : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem originalPrescribedAmplitude_pair_values
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (label' : (Fin r' × Bool) ↪ Fin p') (l' : Fin r')
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x))
    (tau : ℝ) (length : ℕ) (u : Fin p → ℝ) (v : Fin p' → ℝ)
    (hfalse : u (label (l,false)) = v (label' (l',false)))
    (htrue : u (label (l,true)) = v (label' (l',true))) (x : D) :
    round4PrescribedAmplitude imag label l F hF c vf tau length u x =
      round4PrescribedAmplitude imag label' l' F hF c vf tau length v x := by
  have hs : actualPairedNormalSource label l F hF c vf u =
      actualPairedNormalSource label' l' F hF c vf v := by
    funext y
    simp only [actualPairedNormalSource,hfalse,htrue]
  simp only [round4PrescribedAmplitude,hfalse,htrue,hs]

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

theorem originalPrescribedGlobalAmplitude_pair_values
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (label' : (Fin r' × Bool) ↪ Fin p') (l' : Fin r')
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (Ep × M) (Ep × D))
    (u : Fin p → ℝ) (v : Fin p' → ℝ)
    (hfalse : u (label (l,false)) = v (label' (l',false)))
    (htrue : u (label (l,true)) = v (label' (l',true))) (z : Ep × M) :
    round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a u z =
      round4PrescribedGlobalAmplitude imag label' l' F hF c vf tau length a v z := by
  unfold round4PrescribedGlobalAmplitude
  split_ifs with hz
  · exact originalPrescribedAmplitude_pair_values imag label l label' l' _ _ _ _ tau length u v
      hfalse htrue _
  · rfl

theorem originalPrescribedGlobalAmplitude_pair_projection
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (Ep × M) (Ep × D))
    (u : ProbeParameters r) (z : Ep × M) :
    round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a
      (probeParameterEmbedding label u) z =
    round4PrescribedGlobalAmplitude imag (round4PairedParameterIndex 1).toEmbedding (0 : Fin 1)
      F hF c vf tau length a
      (probeParameterEmbedding (round4PairedParameterIndex 1).toEmbedding (originalProbePairProjection l u)) z := by
  apply originalPrescribedGlobalAmplitude_pair_values imag label l
    (round4PairedParameterIndex 1).toEmbedding (0 : Fin 1) F hF c vf tau length a
  · simp only [originalProbeEmbedding_apply_label,originalProbePairProjection_apply]
  · simp only [originalProbeEmbedding_apply_label,originalProbePairProjection_apply]

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.originalProbeEmbedding_apply_label
#print axioms GlobalEmbedding.NormalPolar.originalPrescribedAmplitude_pair_values
#print axioms GlobalEmbedding.NormalPolar.originalPrescribedGlobalAmplitude_pair_values
#print axioms GlobalEmbedding.NormalPolar.originalPrescribedGlobalAmplitude_pair_projection

