import GlobalEmbedding.Paper.BufferedAtlas
import GlobalEmbedding.Paper.InducedMetric
import GlobalEmbedding.Paper.PaperCoordinateNormBridge

/-!
# Native coordinate views for the original finite-increment target draft

Source: main.tex225–238,590–675; W1 concrete-data-ABI sections1–4.
These are only literal views of the SAME native maps/tensors in the original
product charts. No norm, geometric carrier, solver or estimate is introduced.
The original full target and formula are still review drafts, not proved here.
-/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {n d N c : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]

/-- The source part of the actual full source/parameter coordinate vector.
Source: original total product-coordinate norms in lem:increments. -/
def incrementsOriginalSourcePoint (y : Fin (n + d) → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun r ↦ y (Fin.castAdd d r)

/-- The parameter part of the SAME full coordinate vector, including dimension zero.
Source: original finite auxiliary parameter clause of lem:increments. -/
def incrementsOriginalParameterPoint (y : Fin (n + d) → ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun r ↦ y (Fin.natAdd n r)

/-- The literal native inverse product chart. Parameter charts need cover only the
specified parameter norm domain, not all of the parameter manifold.
Source: original finite source/parameter atlas norm convention. -/
def incrementsOriginalJointPoint
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (i : Fin A.count × Fin c) (y : Fin (n + d) → ℝ) : P × M :=
  ((B i.2).symm (incrementsOriginalParameterPoint y),
    (A.chart i.1).symm (incrementsOriginalSourcePoint y))

/-- The actual open differentiation domain of the product chart. Its openness is
a native chart/projection fact, not compact-parameter within differentiation.
Source: original chart norm domains in lem:increments. -/
def incrementsOriginalDifferentiation
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (i : Fin A.count × Fin c) : Set (Fin (n + d) → ℝ) :=
  {y | incrementsOriginalSourcePoint y ∈ (A.chart i.1).target ∧
    incrementsOriginalParameterPoint y ∈ (B i.2).target}

/-- The original SUP domain remains separate from differentiation. Omega and Q
are the actual source/parameter chart norm domains; K is the compact evaluation
parameter set. No compactness or closedness is imposed on Omega or the atlas.
Source: original buffered/full-parameter norm convention. -/
def incrementsOriginalEvaluation
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (Omega : Fin A.count → Set (EuclideanSpace ℝ (Fin n)))
    (Q : Fin c → Set (EuclideanSpace ℝ (Fin d))) (K : Set P)
    (i : Fin A.count × Fin c) : Set (Fin (n + d) → ℝ) :=
  {y | y ∈ incrementsOriginalDifferentiation A B i ∧
    incrementsOriginalSourcePoint y ∈ Omega i.1 ∧
    incrementsOriginalParameterPoint y ∈ Q i.2 ∧
    (incrementsOriginalJointPoint A B i y).1 ∈ K}

/-- Literal target coordinate values of the SAME original native map, with no
Euclidean/Pi isometry assertion. Source: original map norm in lem:increments. -/
def incrementsOriginalMapCoordinates
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (f : P × M → EuclideanSpace ℝ (Fin N))
    (i : Fin A.count × Fin c) (y : Fin (n + d) → ℝ) : Fin N → ℝ :=
  EuclideanSpace.equiv (Fin N) ℝ (f (incrementsOriginalJointPoint A B i y))

/-- The genuine spatial tangent vector obtained from the SAME inverse source
chart. It does not differentiate a parameter variable.
Source: actual tensor pullbacks and source-only inducedMetric differentiation. -/
def incrementsOriginalSourceVector
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))) (i : Fin A.count)
    (y : Fin (n + d) → ℝ) (r : Fin n) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((A.chart i).symm (incrementsOriginalSourcePoint y)) :=
  mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (A.chart i).symm (incrementsOriginalSourcePoint y)
    ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (incrementsOriginalSourcePoint y)).symm (EuclideanSpace.single r 1))

/-- ALL ordered components of the SAME native tensor in the true source chart
directions, flattened by the native finite-product equivalence. Norm derivatives
still see the FULL source/parameter vector y. No supplied matrix replaces T.
Source: literal tensor norm and metric error in (6.1). -/
def incrementsOriginalTensorCoordinates
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (T : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (i : Fin A.count × Fin c) (y : Fin (n + d) → ℝ) : Fin (n * n) → ℝ :=
  fun k ↦ T (incrementsOriginalJointPoint A B i y).1
    (incrementsOriginalJointPoint A B i y).2
    (incrementsOriginalSourceVector A i.1 y (finProdFinEquiv.symm k).1)
    (incrementsOriginalSourceVector A i.1 y (finProdFinEquiv.symm k).2)

/-- The actual original error tensor, with the SAME native F,U,H and source-only
metric differentiation. Source: (6.1), no abstract residual field or new metric. -/
def incrementsOriginalMetricError
    (F U : P × M → EuclideanSpace ℝ (Fin N))
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (δ : ℝ) (p : P) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  inducedMetric (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (fun y ↦ F (p, y) + U (p, y)) x -
    inducedMetric (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (fun y ↦ F (p, y)) x - δ ^ 2 • H p x

open scoped ENNReal

/-- ORIGINAL primitive data for the finite-increment statement, with their actual
native fields and domains. This raw record does NOT assert full admissibility:
the original immersion/goodness/decomposition/regularity conditions must still
be defined and checked. No desired solver/mean/correction/output field is present.
Source: main.tex590–611, original fixed chosen phase/decomposition inputs. -/
structure IncrementsOriginalNativeData (n d N : ℕ) (M P : Type*)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [TopologicalSpace P] where
  /-- The actual given source atlas, not a new source carrier. -/
  atlas : BufferedAtlas M (EuclideanSpace ℝ (Fin n))
  /-- Original enlarged source norm domains in the actual source coordinates. -/
  sourceNormDomain : Fin atlas.count → Set (EuclideanSpace ℝ (Fin n))
  /-- The finite parameter chart family only covers the stated evaluation set. -/
  parameterCount : ℕ
  /-- The actual parameter charts. -/
  parameterChart : Fin parameterCount → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d))
  /-- Original parameter norm pieces, not differentiation within compact sets. -/
  parameterNormDomain : Fin parameterCount → Set (EuclideanSpace ℝ (Fin d))
  /-- Original compact parameter evaluation set; its compactness is a separate condition. -/
  parameterSet : Set P
  /-- Original open parameter neighborhood; its openness is a separate condition. -/
  parameterOpen : Set P
  /-- The SAME native background map. -/
  F : P × M → EuclideanSpace ℝ (Fin N)
  /-- The SAME original target tensor, not unrelated matrix components. -/
  H : (p : P) → (x : M) →
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)
  /-- The given reference tensor of the original decomposition neighborhood. -/
  reference : (p : P) → (x : M) →
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)
  /-- Actual finite primary count, never an extra uniform numerical bound. -/
  primaryCount : ℕ
  /-- Original local phase representatives; arbitrary outside values impose no conditions. -/
  phase : Fin primaryCount → P × M → ℝ
  /-- Original cutoffs. -/
  cutoff : Fin primaryCount → P × M → ℝ
  /-- Original provided Euclidean normal fields, with unit/free conditions checked separately. -/
  freeNormal : Fin primaryCount → P × M → EuclideanSpace ℝ (Fin N)
  /-- Original open neighborhoods where the corresponding phase/normal data are used. -/
  primaryDomain : Fin primaryCount → Set (P × M)
  /-- Original linear tensor functionals, with their true native tensor argument. -/
  linearArgument : Fin primaryCount → (p : P) → (x : M) →
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) →ₗ[ℝ] ℝ
  /-- The SAME original symmetric-fiber neighborhood. Openness is still a genuine
  coordinate-topology condition, not an open set in all bilinear forms. -/
  tensorNeighborhood : (p : P) → (x : M) →
    Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) //
      A.IsSymm}

/-- Literal original scalar coordinate values. Source: original cutoff norm in
lem:increments. This is a component view, not an alternate scalar norm. -/
def incrementsOriginalScalarCoordinates (D : IncrementsOriginalNativeData n d N M P)
    (f : P × M → ℝ) (i : Fin D.atlas.count × Fin D.parameterCount)
    (y : Fin (n + d) → ℝ) : Fin 1 → ℝ :=
  fun _ ↦ f (incrementsOriginalJointPoint D.atlas D.parameterChart i y)

/-- The ORIGINAL spatial covector d_source phi, derived from the actual native
phase slice. Total parameter derivatives belong to its later coordinate norm;
no parameter derivative is inserted into this covector itself.
Source: chosen phases in main.tex599–601. -/
def incrementsOriginalPhaseCovector (D : IncrementsOriginalNativeData n d N M P)
    (ν : Fin D.primaryCount) (p : P) (x : M) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ :=
  (tangentSpaceCastModel 𝓘(ℝ, ℝ) (D.phase ν (p, x))).toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) (fun z ↦ D.phase ν (p, z)) x)

/-- The SAME actual spatial covector in all original source chart slots. Its
norm differentiates the FULL n+d vector, as required for finite parameters.
Source: original phase field in the finite input profile. -/
def incrementsOriginalPhaseCovectorCoordinates (D : IncrementsOriginalNativeData n d N M P)
    (ν : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount)
    (y : Fin (n + d) → ℝ) : Fin n → ℝ :=
  fun r ↦ incrementsOriginalPhaseCovector D ν
    (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
    (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2
    (incrementsOriginalSourceVector D.atlas i.1 y r)

/-- Restrict differentiation to the ORIGINAL phase/normal neighborhood. This
does not impose smoothness on arbitrary outside extensions of the provided
normal field. Source: original local primary data in lem:increments. -/
def incrementsOriginalPrimaryDifferentiation (D : IncrementsOriginalNativeData n d N M P)
    (ν : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount) :
    Set (Fin (n + d) → ℝ) :=
  incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
    (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹' D.primaryDomain ν

/-- The SAME primary SUP domain, inside the original differentiation domain.
Source: original local phase/normal input norm domains. -/
def incrementsOriginalPrimaryEvaluation (D : IncrementsOriginalNativeData n d N M P)
    (ν : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount) :
    Set (Fin (n + d) → ℝ) :=
  incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
      D.parameterNormDomain D.parameterSet i ∩
    (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹' D.primaryDomain ν

/-- Actual CORE of the ORIGINAL input profile, with the SAME cumulative weighted
paper MAX. It includes base2 F, base0 H, and the actual original cutoff, provided
normal and spatial phase-covector fields on their original local domains.

This is explicitly NOT the full profile: actual adapted transition/inverse and
linear-functional coefficient fields remain to be added. No derived inverse,
chosen-phase margin, mean or solver output is an input. Finiteness is not assumed
or faked by toReal. Source: main.tex590–675 and W1's explicit original profile. -/
def incrementsOriginalCoreInputProfile (D : IncrementsOriginalNativeData n d N M P)
    (j : ℕ) (ell : ℝ) : ℝ≥0∞ :=
  let O := incrementsOriginalDifferentiation D.atlas D.parameterChart
  let S := incrementsOriginalEvaluation D.atlas D.parameterChart
    D.sourceNormDomain D.parameterNormDomain D.parameterSet
  max (paperAtlasWeighted 2 j ell
    (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F) O S)
    (max (paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H) O S)
      (⨆ ν : Fin D.primaryCount,
        let Oν := incrementsOriginalPrimaryDifferentiation D ν
        let Sν := incrementsOriginalPrimaryEvaluation D ν
        max (paperAtlasWeighted 0 j ell
          (incrementsOriginalScalarCoordinates D (D.cutoff ν)) Oν Sν)
          (max (paperAtlasWeighted 0 j ell
            (incrementsOriginalMapCoordinates D.atlas D.parameterChart (D.freeNormal ν)) Oν Sν)
            (paperAtlasWeighted 0 j ell (incrementsOriginalPhaseCovectorCoordinates D ν) Oν Sν))))

end GlobalEmbedding.Paper
