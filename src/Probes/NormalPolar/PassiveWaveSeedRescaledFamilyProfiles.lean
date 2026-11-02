import NormalPolar.PassiveWaveSeedParameterRaw
import NormalPolar.PassiveWaveSeedRescaledObservation

/-! Actual original legal waves produce the complete grouped primitive
profiles on every original physical parameter chart. Source sampling sets
are the given compact coordinate norm domains, not smaller chart supports.
All costs are fixed before the reference contraction, order, oscillation scale and observer index. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation GlobalEmbedding.Offline

variable {m N d r count : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [TopologicalSpace P]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "IM" => 𝓘(ℝ,D)
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

namespace OriginalWaveSeedRescaledFamily

theorem exists_uniform_parameter_raw_profiles (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (R : Fin A.count → Set D) (hR : ∀ h, IsCompact (R h))
    (hRt : ∀ h, R h ⊆ (A.chart h).target)
    (B : Fin count → OpenPartialHomeomorph P Ep)
    (Samples : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (hSB : ∀ idx z, parameterTensorModelEquiv (m+1) d z ∈ Samples idx → z.1 ∈ (B idx.2).target)
    (hSR : ∀ idx z, parameterTensorModelEquiv (m+1) d z ∈ Samples idx → z.2 ∈ R idx.1) :
    ∃ T Pphase : ℕ → ℝ, (∀ k, 0 < T k ∧ 0 < Pphase k) ∧
      ∀ (contraction : ℝ) (hc : contraction ∈ Icc (1/2 : ℝ) 1)
        (n j : ℕ) (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
      ∀ idx : Fin A.count × Fin count,
      Nonempty (JointGroupedPrescribedParameterChartRawData
        (fun _ : P => contraction • F) (fun _ => contMDiff_const_rescale F hF contraction)
        (fun l s _ => (family.outer l s).spatialChart.symm)
        (fun l s (z : P × D) => (family.refinement l).cutoffCoordinates s (0,z.2))
        (fun l s _ x => actualRescaledNormal F hF contraction (originalWave_contraction_ne_zero contraction hc)
          ((family.outer l s).spatialChart.symm x)
          ((waves l).normal ((family.outer l s).spatialChart.symm x)))
        (fun l (z : P × M) => weight l * (waves l).phase z.2)
        (fun l s => passiveParameterChart (0 : Z) (family.inner l s).chart)
        (B idx.2) (A.chart idx.1) ((B idx.2).target ×ˢ (A.chart idx.1).target)
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx)
        n j ell (family.geometryBudget (max n (j+1))) (family.cutoffBudget n)
        (family.normalBudget n) (Pphase (j+1)) T) := by
  obtain ⟨T,Pphase,hpos,hprofiles⟩ := family.exists_uniform_observation_profiles_samples A hA R hR hRt
  refine ⟨fun k => 1+T k,Pphase,fun k => ⟨by linarith [(hpos k).1],(hpos k).2⟩,?_⟩
  intro contraction hc n j ell hell hell1 idx
  obtain ⟨profiles⟩ := hprofiles contraction hc n (j+1) ell hell hell1 idx.1
  exact ⟨passiveWaveSeed_parameter_raw (B idx.2) (A.chart idx.1) (hA.chart_mem idx.1)
    (fun _ : Z => contraction • F) (fun _ => contMDiff_const_rescale F hF contraction)
    (fun l s _ => (family.outer l s).spatialChart.symm)
    (fun l s => (family.refinement l).cutoffCoordinates s)
    (fun l s _ x => actualRescaledNormal F hF contraction (originalWave_contraction_ne_zero contraction hc)
          ((family.outer l s).spatialChart.symm x)
          ((waves l).normal ((family.outer l s).spatialChart.symm x)))
    (fun l s => (family.inner l s).chart)
    (fun l s => tsupport ((family.refinement l).cutoff s)) n j ell
    (family.geometryBudget (max n (j+1))) (family.cutoffBudget n) (family.normalBudget n)
    hell (R idx.1) (hRt idx.1) T (fun k => (hpos k).1.le)
    (fun l z => weight l * (waves l).phase z.2) (Pphase (j+1)) profiles
    ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx)
    (fun z hz => hSB idx z hz) (fun z hz => hSR idx z hz)⟩

end OriginalWaveSeedRescaledFamily
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.exists_uniform_parameter_raw_profiles
