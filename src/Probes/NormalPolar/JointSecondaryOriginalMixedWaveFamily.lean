import NormalPolar.JointSecondaryOriginalMixedSeed
import NormalPolar.OriginalWaveSeedRescaledFamily

/-! One construction selects the common prescribed phase weights first,
then the true full mixed secondary seeds and the actual original prescribed
wave refinements with those same weights. Neither family reselects a phase,
label or weight. Both families' budgets precede every contraction and scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade
open Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N r : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
variable (Data : IncrementsOriginalNativeData (m+1) d N M P)
  (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
  (p : P) (hpO : p ∈ Data.parameterOpen)
  (waves : Fin r → LocalLegalWave (n := m+1) (fun x => Data.F (p,x))
    (incrementsOriginal_slice_contMDiff Data hd hs p hpO))

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

theorem jointSecondary_exists_original_mixed_and_wave_family
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data) :
    Nonempty (Σ mixed : JointSecondaryOriginalMixedSeedFamily (Ep := Ep) Data hd hs p hpO waves,
      GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily
        (fun y => Data.F (p,y)) (incrementsOriginal_slice_contMDiff Data hd hs p hpO)
        waves mixed.probeWeight) := by
  obtain ⟨mixed⟩ := jointSecondary_exists_original_mixed_seed_family (Ep := Ep)
    Data hd hs p hpO waves hp hImm
  obtain ⟨family⟩ := GlobalEmbedding.NormalPolar.exists_originalWaveSeedRescaledFamily
    (fun y => Data.F (p,y)) (incrementsOriginal_slice_contMDiff Data hd hs p hpO)
    (hImm.immersion p hpO) waves mixed.probeWeight mixed.probeWeight_pos
  exact ⟨⟨mixed,family⟩⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_exists_original_mixed_and_wave_family
