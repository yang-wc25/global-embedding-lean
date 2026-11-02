import NormalPolar.PassiveRescaledData
import Probes.Round3ParameterOriginalPrimaryGeometry
import Probes.Round3ParameterNativeRefinementSamples

/-! The same actual primary family under reference contraction. Only the
normal-membership proof changes; all seven primitive fields are literal.
Consequently the original whole-family geometry and the exact original
chart/sample budgets are uniform before the contraction parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P Sub Label : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [Fintype Sub] [Fintype Label]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

def passiveRescaledPrimary (F : P → M → V)
    (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Label) (Β := Sub) F)
    (c : ℝ) (hc : c ≠ 0) :
    Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Label) (Β := Sub)
      (fun p x => c • F p x) := by
  refine { g with normal_mem := ?_ }
  intro nu a z hz
  change g.normal nu (z.1,g.inverse nu a z.1 z.2) ∈
    normalSpace (I := IM) (c • F z.1) (g.inverse nu a z.1 z.2)
  rw [normalSpace_const_rescale (F z.1) (hF z.1) c hc]
  exact g.normal_mem nu a z hz

theorem passiveRescaledPrimary_fields (F : P → M → V)
    (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Label) (Β := Sub) F)
    (c : ℝ) (hc : c ≠ 0) :
    let out := passiveRescaledPrimary F hF g c hc
    out.phase=g.phase ∧ out.cutoff=g.cutoff ∧ out.normal=g.normal ∧
      out.linearArgument=g.linearArgument ∧ out.eta=g.eta ∧ out.chart=g.chart ∧ out.inverse=g.inverse :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

variable [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem passiveRescaled_primary_geometry (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x))) (R : ℕ) (hg : Round3ParameterOriginalPrimaryGeometry Data g R)
    (c : ℝ) (hc : c ≠ 0) :
    Round3ParameterOriginalPrimaryGeometry (passiveRescaledData Data c)
      (passiveRescaledPrimary (fun p x => Data.F (p,x)) hF g c hc) R :=
  { phase := hg.phase
    cutoff := hg.cutoff
    normal := hg.normal
    linear := hg.linear
    preserves := hg.preserves
    inverse := hg.inverse
    phase_coordinate := hg.phase_coordinate
    inverse_active := hg.inverse_active
    smooth := hg.smooth
    compact := hg.compact
    support := hg.support
    partition := hg.partition
    count := hg.count }

theorem passiveRescaled_primary_profiles (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x))) (Forward Inverse Meta : ℕ → ℝ)
    (h : Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta)
    (c : ℝ) (hc : c ≠ 0) :
    Round3ParameterOriginalChartProfiles (passiveRescaledData Data c)
      (passiveRescaledPrimary (fun p x => Data.F (p,x)) hF g c hc) Forward Inverse Meta := h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveRescaledPrimary
#print axioms GlobalEmbedding.Continuation.passiveRescaled_primary_profiles
