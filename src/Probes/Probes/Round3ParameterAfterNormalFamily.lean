import Probes.Round3ParameterFixedProfileRebase

/-! Rebind the actual current map and its newly constructed intrinsic normal
in the SAME fixed-carrier primary family. Every cutoff, actual chart and
inverse function is kept. Its new normal-space membership is proved from the
new original normal conditions at the true active physical point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def round3ParameterAfterNormalFamily
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {Sub : Type*} [Fintype Sub]
    (g0 : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Sub)
      (fun p x => Ref.F (p,x)))
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
    (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm})
    (hdNew : IncrementsOriginalDomainConditions (round3ParameterStageData Ref F H V normal domain neighborhood))
    (hsNew : IncrementsOriginalSmoothInputs (round3ParameterStageData Ref F H V normal domain neighborhood))
    (hnNew : IncrementsOriginalFreeNormalConditions (round3ParameterStageData Ref F H V normal domain neighborhood) hdNew hsNew)
    (hActive : ∀ nu a z, z ∈ (g0.chart nu a).target →
      (z.1,g0.inverse nu a z.1 z.2) ∈ domain nu ∩
        incrementsOriginalParameterRegion (round3ParameterStageData Ref F H V normal domain neighborhood)) :
    Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Sub)
      (fun p x => F (p,x)) where
  phase := g0.phase
  cutoff := g0.cutoff
  normal := normal
  linearArgument := g0.linearArgument
  eta := g0.eta
  chart := g0.chart
  inverse := g0.inverse
  normal_mem := fun nu a z hz => hnNew.normal nu (z.1,g0.inverse nu a z.1 z.2) (hActive nu a z hz)

theorem round3Parameter_after_normal_geometry_and_profiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    {Sub : Type*} [Fintype Sub]
    (g0 : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Sub)
      (fun p x => Ref.F (p,x)))
    (R : ℕ) (hg0 : Round3ParameterOriginalPrimaryGeometry Ref g0 R)
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfiles : Round3ParameterOriginalChartProfiles Ref g0 Forward Inverse Meta)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
    (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm})
    (hdNew : IncrementsOriginalDomainConditions (round3ParameterStageData Ref F H V normal domain neighborhood))
    (hsNew : IncrementsOriginalSmoothInputs (round3ParameterStageData Ref F H V normal domain neighborhood))
    (hnNew : IncrementsOriginalFreeNormalConditions (round3ParameterStageData Ref F H V normal domain neighborhood) hdNew hsNew)
    (hActive : ∀ nu a z, z ∈ (g0.chart nu a).target →
      (z.1,g0.inverse nu a z.1 z.2) ∈ domain nu ∩
        incrementsOriginalParameterRegion (round3ParameterStageData Ref F H V normal domain neighborhood)) :
    let g := round3ParameterAfterNormalFamily Ref g0 F H V normal domain neighborhood hdNew hsNew hnNew hActive
    Round3ParameterOriginalPrimaryGeometry (round3ParameterStageData Ref F H V normal domain neighborhood) g R ∧
      Round3ParameterOriginalChartProfiles (round3ParameterStageData Ref F H V normal domain neighborhood)
        g Forward Inverse Meta ∧
      g.eta = g0.eta ∧ g.chart = g0.chart ∧ g.inverse = g0.inverse := by
  intro g
  have hg : Round3ParameterOriginalPrimaryGeometry (round3ParameterStageData Ref F H V normal domain neighborhood) g R := {
    phase := hg0.phase
    cutoff := hg0.cutoff
    normal := rfl
    linear := hg0.linear
    preserves := hg0.preserves
    inverse := hg0.inverse
    phase_coordinate := hg0.phase_coordinate
    inverse_active := hActive
    smooth := hg0.smooth
    compact := hg0.compact
    support := hg0.support
    partition := hg0.partition
    count := hg0.count }
  refine ⟨hg,?_,rfl,rfl,rfl⟩
  exact round3Parameter_original_profiles_stage_rebase Ref hd g0 Forward Inverse Meta hProfiles
    F H V normal domain neighborhood g R hg rfl (fun _ _ => rfl) (fun _ _ => rfl)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterAfterNormalFamily
#print axioms GlobalEmbedding.Continuation.round3Parameter_after_normal_geometry_and_profiles
