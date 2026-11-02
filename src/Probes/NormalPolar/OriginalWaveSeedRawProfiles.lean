import NormalPolar.OriginalWaveSeedRawFullProfiles
import NormalPolar.ParameterDisplacementPrescribedRaw

/-! The full prescribed raw-profile input is produced from an arbitrary
original legal wave, its immersion and its actual finite adapted refinement.
No solver coefficient, reconstructed amplitude or output estimate is assumed.
All prefix constants are fixed before both requested orders and scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Z × D

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}
  {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

namespace OriginalWaveSeedBuffer

/-- The complete actual raw input of a piece. Geometry bounds are common
finite-prefix constants; the original normal and cutoff retain their own
budgets. These choices depend on the seed, never on a later scale. -/
theorem exists_actual_raw_profiles (b : OriginalWaveSeedBuffer d i)
    (hweight : 0 < weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x)) :
    ∃ b' : OriginalWaveSeedBuffer d i, b.compactTarget ⊆ interior b'.compactTarget ∧
    ∃ Mg Bchi Bnu : ℕ → ℝ,
      (∀ n, 0 < Mg n ∧ 0 < Bchi n ∧ 0 < Bnu n) ∧
      ∀ (n j : ℕ) (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
        Nonempty (ActualPrescribedSpatialRawProfiles
          (fun _ : Z => F) (fun _ => hF) (fun _ => b'.spatialChart.symm)
          (d.cutoffCoordinates i) (fun _ x => w.normal (b'.spatialChart.symm x))
          b.chart univ (tsupport (d.cutoff i)) n j ell
          (Mg (max n j)) (Bchi n) (Bnu n)) := by
  obtain ⟨b',hbb,Mg,Bchi,Bnu,hpos,hraw⟩ :=
    b.exists_actual_raw_full_profiles hweight hImm
  refine ⟨b',hbb,Mg,Bchi,Bnu,hpos,?_⟩
  intro n j ell hell hell1
  obtain ⟨raw,_⟩ := hraw n j ell hell hell1
  exact ⟨raw⟩

end OriginalWaveSeedBuffer
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.exists_actual_raw_profiles
