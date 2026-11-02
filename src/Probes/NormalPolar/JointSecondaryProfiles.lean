import NormalPolar.JointSecondaryPiece
import NormalPolar.ActualProbeSecondaryParameterForcing

/-! Original primitive choices for all signed mixed secondary pieces. This
record contains actual host/adapted charts, ordinary subordinate cutoffs and
raw background/prescribed inputs. It has no chosen forcing, CH, completed wave,
remainder or first-state estimate fields. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M Ep Tr Λ Β Sub : Type*} {m N p r : ℕ}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord (Λ ⊕ Fin r)

def jointSecondarySignedPhase {Label : Type*} (phase : Label → Ep × M → ℝ)
    (rec : (Label × Label) × Fin 4) (z : Ep × M) : ℝ :=
  ![phase rec.1.1 z+phase rec.1.2 z,phase rec.1.1 z-phase rec.1.2 z,
    -phase rec.1.1 z+phase rec.1.2 z,-phase rec.1.1 z-phase rec.1.2 z] rec.2

structure JointSecondarySourceProfiles
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (phase : Fin r → Ep × M → ℝ)
    (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : Ep → Fin p → ℝ)
    (W : Set (Ep × M)) (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (nInput nSolve q probeLength j Rsub Lprimary : ℕ)
    (reserve Bnd Mg Kcut Bchi Bnu Ku Mphase tau ell delta Delta : ℝ)
    (Tbackground Tprobe Tinv : ℕ → ℝ) where
  geometry : Rec → Sub → ActualSecondaryRawGeometry F hF nSolve j ell Mg W
  host : Rec → Sub → OpenPartialHomeomorph M D
  host_maximal : ∀ rec b, host rec b ∈ maximalAtlas IM ∞ M
  host_source : ∀ rec b, (geometry rec b).chart.source ⊆
    ((OpenPartialHomeomorph.refl Ep).prod (host rec b)).source
  cutoff : Rec → Sub → Ep × M → ℝ
  cutoff_support : ∀ rec b, incrementsGlobalRelativeSupport W (cutoff rec b) ∩
    (K rec.val.1.1 ∩ K rec.val.1.2) ⊆ (geometry rec b).support
  partition : ∀ rec z, z ∈ K rec.val.1.1 ∩ K rec.val.1.2 → ∑ b, cutoff rec b z = 1
  phase_identity : ∀ rec b, (geometry rec b).phase =
    jointSecondarySignedPhase (Sum.elim g.phase phase) rec.val
  cutoff_smooth : ∀ rec b, ContDiffOn ℝ ∞
    (cutoff rec b ∘ ((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm)
    (((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm.trans (geometry rec b).chart).source
  inverse_smooth : ∀ rec b, ContDiffOn ℝ ∞
    (((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm.trans (geometry rec b).chart).symm
    (((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm.trans (geometry rec b).chart).target
  background : ∀ rec b, ParameterRound2GlobalMeanRawProfiles (Tr := Tr)
    nInput (q+2) nSolve Rsub Lprimary reserve Bnd Mg Tbackground F hF g input inputbar W
    (fun l => K (Sum.inl l)) (host rec b)
    (((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm.trans (geometry rec b).chart).source
    ((((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm.trans (geometry rec b).chart).symm ''
      (geometry rec b).sample) tau ell Delta
  prescribed : ∀ rec b, ActualPrescribedObservationProfiles F hF c chi nu a W (fun l => K (Sum.inr l))
    nInput (nSolve+1) ell Mg Bchi Bnu (fun z : X => (z.1,(host rec b).symm z.2))
    (((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm.trans (geometry rec b).chart).source
    ((((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm.trans (geometry rec b).chart).symm ''
      (geometry rec b).sample) Tprobe phase Mphase
  cutoff_jets : ∀ rec b k, k ≤ nSolve → ∀ z ∈ (geometry rec b).sample,
    ell^k*‖iteratedFDeriv ℝ k (cutoff rec b ∘ ((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm)
      ((((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm.trans (geometry rec b).chart).symm z)‖ ≤ Kcut
  inverse_jets : ∀ rec b k, 1 ≤ k → k ≤ nSolve+1 → ∀ z ∈ (geometry rec b).sample,
    ell^(k-1)*‖iteratedFDeriv ℝ k
      (((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm.trans (geometry rec b).chart).symm z‖ ≤ Tinv k

  parameter_smooth : ∀ rec b, ContDiffOn ℝ ∞ (fun z : X => u z.1)
    (((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm.trans (geometry rec b).chart).source
  parameter_jets : ∀ rec b k, k ≤ nSolve →
    ∀ z ∈ (((OpenPartialHomeomorph.refl Ep).prod (host rec b)).symm.trans (geometry rec b).chart).symm ''
      (geometry rec b).sample,
    ell^k*‖iteratedFDeriv ℝ k (fun y : X => u y.1) z‖ ≤ Ku

end GlobalEmbedding.Continuation

