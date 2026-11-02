import NormalPolar.JointSecondaryProfiles

/-! Exact identities for the family produced from the same raw mixed sources.
This is an output proposition. It records the actual two forcing fields and
complete finite wave, not derivative or metric estimates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M Ep Label Sub : Type*} {m N : ℕ}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord Label

def JointSecondaryFamilySpec
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (geometry : Rec → Sub → ActualSecondaryRawGeometry F hF n j ell Mg W)
    (host : Rec → Sub → OpenPartialHomeomorph M D)
    (cutoff : Rec → Sub → Ep × M → ℝ)
    (phase : Label → Ep × M → ℝ) (R Q : Label → Ep × M → V) (tau : ℝ)
    (data : Rec → Sub → ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W) : Prop :=
  ∀ rec b,
    let chart := (geometry rec b).chart
    let source := (geometry rec b).c
    let h := (OpenPartialHomeomorph.refl Ep).prod (host rec b)
    let H := actualParameterPrimaryQuadratic phase R Q tau (host rec b) rec.val
    let HR := actualSecondaryInverseForcing (h.symm.trans chart) (cutoff rec b ∘ h.symm)
      (fun z => actualRealTensorAssembly (H z))
    let HI := actualSecondaryInverseForcing (h.symm.trans chart) (cutoff rec b ∘ h.symm)
      (fun z => actualImaginaryTensorAssembly (H z))
    (data rec b).base.c = source ∧ (data rec b).base.chart = chart ∧
    (data rec b).base.phase = jointSecondarySignedPhase phase rec.val ∧
    (data rec b).base.support = (geometry rec b).support ∧
    (data rec b).base.sample = (geometry rec b).sample ∧
    (data rec b).base.hR = HR ∧ (data rec b).base.hI = HI ∧
    ∀ tau' length, (data rec b).base.wave tau' length =
      actualSecondarySupportedWave F hF source HR HI chart
        (jointSecondarySignedPhase phase rec.val) tau' length

end GlobalEmbedding.Continuation

