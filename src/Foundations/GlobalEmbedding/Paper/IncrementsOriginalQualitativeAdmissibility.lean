import GlobalEmbedding.Paper.IncrementsOriginalNativeCoordinates
import GlobalEmbedding.Paper.GoodCovector
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Original local domain, smoothness, Good and unit-free input conditions

Source: main.tex590–611 and672–675; original finite-increment assumptions.
These predicates specify ORIGINAL INPUT properties of the SAME native raw data.
Joint support is relative to parameterOpen, never arbitrary outside extensions.
No solver/mean/correction/result field or selected inverse bound is present.
This is an admissibility PREFIX: positive symmetric-fiber decomposition,
transition/radius source-equivalence and the full profile remain explicit gates.
-/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]

local notation "IX" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "IY" => 𝓘(ℝ, EuclideanSpace ℝ (Fin d))
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin d))
  𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The ORIGINAL joint parameter-open neighborhood. The compact evaluation set
is not a differentiation domain. Source: finite auxiliary parameters. -/
def incrementsOriginalParameterRegion (D : IncrementsOriginalNativeData n d N M P) :
    Set (P × M) := D.parameterOpen ×ˢ Set.univ

/-- Actual joint cutoff support RELATIVE to the original parameter-open region.
It may be only relatively closed in P×M; no outside extension is constrained.
Source: original support preservation and joint parameter clause. -/
def incrementsOriginalRelativeCutoffSupport (D : IncrementsOriginalNativeData n d N M P)
    (ν : Fin D.primaryCount) : Set (P × M) :=
  Subtype.val '' tsupport
    (fun z : incrementsOriginalParameterRegion D ↦ D.cutoff ν z.val)

/-- Relative support lies in the ORIGINAL joint region by its native subtype.
This is not a compactness assertion. Source: original joint support convention. -/
theorem incrementsOriginalRelativeCutoffSupport_subset
    (D : IncrementsOriginalNativeData n d N M P) (ν : Fin D.primaryCount) :
    incrementsOriginalRelativeCutoffSupport D ν ⊆ incrementsOriginalParameterRegion D := by
  rintro z ⟨y, hy, rfl⟩
  exact y.property

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

/-- Original domain/atlas/support conditions only. Radius/compact-source claims
are deliberately NOT inferred from the weak raw atlas. Source: setup590–611. -/
structure IncrementsOriginalDomainConditions (D : IncrementsOriginalNativeData n d N M P) :
    Prop where
  source_dim : 2 ≤ n
  target_dim : n * (n + 1) / 2 + 1 ≤ N
  parameter_open : IsOpen D.parameterOpen
  parameter_compact : IsCompact D.parameterSet
  parameter_subset : D.parameterSet ⊆ D.parameterOpen
  atlas_smooth : IsSmoothBufferedAtlas D.atlas
  parameter_charts_smooth : ∀ i, D.parameterChart i ∈ IsManifold.maximalAtlas IY ∞ P
  source_norm_subset : ∀ i, D.sourceNormDomain i ⊆ (D.atlas.chart i).target
  source_inner_norm : ∀ i x, x ∈ D.atlas.inner i → D.atlas.chart i x ∈ D.sourceNormDomain i
  parameter_norm_subset : ∀ i, D.parameterNormDomain i ⊆ (D.parameterChart i).target
  parameter_cover : ∀ p ∈ D.parameterSet, ∃ i,
    p ∈ (D.parameterChart i).source ∧ D.parameterChart i p ∈ D.parameterNormDomain i
  primary_open : ∀ ν, IsOpen (D.primaryDomain ν)
  cutoff_support_local : ∀ ν,
    incrementsOriginalRelativeCutoffSupport D ν ⊆ D.primaryDomain ν

/-- Actual ORIGINAL joint smooth input conditions on their original open domains.
H is the native tensor's actual coordinate pullback, not independent matrices.
No output smoothness or coefficient estimate is an input. Source: lem:increments. -/
structure IncrementsOriginalSmoothInputs (D : IncrementsOriginalNativeData n d N M P) :
    Prop where
  F_joint : ContMDiffOn IJ 𝓘(ℝ, V) ∞ D.F (incrementsOriginalParameterRegion D)
  H_coordinates : ∀ i, ContDiffOn ℝ ∞
    (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H i)
    (incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
      (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
        incrementsOriginalParameterRegion D)
  phase_joint : ∀ ν, ContMDiffOn IJ 𝓘(ℝ, ℝ) ∞ (D.phase ν)
    (D.primaryDomain ν ∩ incrementsOriginalParameterRegion D)
  cutoff_joint : ∀ ν, ContMDiffOn IJ 𝓘(ℝ, ℝ) ∞ (D.cutoff ν)
    (D.primaryDomain ν ∩ incrementsOriginalParameterRegion D)
  normal_joint : ∀ ν, ContMDiffOn IJ 𝓘(ℝ, V) ∞ (D.freeNormal ν)
    (D.primaryDomain ν ∩ incrementsOriginalParameterRegion D)

omit [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P] in
/-- Slice smoothness is DERIVED from the original joint input; it is not another
original assumption. This only applies native smooth composition with (p,id).
Source: source-only geometry of a joint parameter family in lem:increments. -/
theorem incrementsOriginal_slice_contMDiff (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (p : P) (hp : p ∈ D.parameterOpen) :
    ContMDiff IX 𝓘(ℝ, V) ∞ (fun x ↦ D.F (p, x)) := by
  intro x
  have hW : IsOpen (incrementsOriginalParameterRegion D) :=
    hd.parameter_open.prod isOpen_univ
  have hx : (p, x) ∈ incrementsOriginalParameterRegion D := ⟨hp, Set.mem_univ x⟩
  have hj := hs.F_joint.contMDiffAt (hW.mem_nhds hx)
  exact hj.comp x (contMDiffAt_const.prodMk contMDiffAt_id)

/-- ORIGINAL qualitative phase requirements, using ONLY canonical GoodCovector.
Its first conjunct already includes noncriticality. Doubled/signed covectors
are literal differential combinations on the actual smooth input domains;
no derivative linearity on arbitrary outside extensions is asserted.
Distinct primary interactions are required only on actual JOINT support pairs.
Source: primary/doubled/interacting phases, main.tex599–601. -/
structure IncrementsOriginalPhaseConditions (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D) :
    Prop where
  primary_good : ∀ ν z (hz : z ∈ D.primaryDomain ν ∩ incrementsOriginalParameterRegion D),
    GoodCovector (I := IX) (fun x ↦ D.F (z.1, x))
      (incrementsOriginal_slice_contMDiff D hd hs z.1 hz.2.1) z.2
      (incrementsOriginalPhaseCovector D ν z.1 z.2)
  doubled_good : ∀ ν z (hz : z ∈ D.primaryDomain ν ∩ incrementsOriginalParameterRegion D),
    GoodCovector (I := IX) (fun x ↦ D.F (z.1, x))
      (incrementsOriginal_slice_contMDiff D hd hs z.1 hz.2.1) z.2
      ((2 : ℝ) • incrementsOriginalPhaseCovector D ν z.1 z.2)
  interaction_good : ∀ ν μ, ν ≠ μ → ∀ sign : Bool, ∀ z
    (hz : z ∈ incrementsOriginalRelativeCutoffSupport D ν ∩
      incrementsOriginalRelativeCutoffSupport D μ),
    GoodCovector (I := IX) (fun x ↦ D.F (z.1, x))
      (incrementsOriginal_slice_contMDiff D hd hs z.1
        ((incrementsOriginalRelativeCutoffSupport_subset D ν hz.1).1)) z.2
      (incrementsOriginalPhaseCovector D ν z.1 z.2 +
        (if sign then (1 : ℝ) else -1) • incrementsOriginalPhaseCovector D μ z.1 z.2)

/-- The GIVEN ORIGINAL unit free normal, in its actual Euclidean norm and actual
native normal space, annihilates the true second form on the literal phase kernel.
No normal choice, new normal bundle or PiSUP-unit convention is introduced.
Source: provided unit free normals in main.tex601 and original beta-kernel input. -/
structure IncrementsOriginalFreeNormalConditions
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D) :
    Prop where
  unit : ∀ ν z, z ∈ D.primaryDomain ν ∩ incrementsOriginalParameterRegion D →
    ‖D.freeNormal ν z‖ = 1
  normal : ∀ ν z, z ∈ D.primaryDomain ν ∩ incrementsOriginalParameterRegion D →
    D.freeNormal ν z ∈ normalSpace (I := IX) (fun x ↦ D.F (z.1, x)) z.2
  free : ∀ ν z (hz : z ∈ D.primaryDomain ν ∩ incrementsOriginalParameterRegion D)
    (u v : (incrementsOriginalPhaseCovector D ν z.1 z.2).ker),
    inner ℝ ((trueSecondForm (I := IX) (fun x ↦ D.F (z.1, x))
      (incrementsOriginal_slice_contMDiff D hd hs z.1 hz.2.1) z.2
        (symmetricSquareProduct (TangentSpace IX z.2) u.val v.val)) : V)
      (D.freeNormal ν z) = 0

end GlobalEmbedding.Paper
