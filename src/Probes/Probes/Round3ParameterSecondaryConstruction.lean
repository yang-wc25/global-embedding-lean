import Probes.Round3ParameterPrimaryConstruction

/-! # The same secondary correction for an arbitrary parameter space

The two genuine spatial Jacobians remain in the transformed forcing.  The
finite complex solver and reconstructed channels are reused without changes.
The output is one literal primary plus secondary map on the entire physical
parameter space, with no observation-order argument and no output cutoff.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {P M : Type*}
  [TopologicalSpace P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Label SubPrimary SubSecondary : Type*} [Fintype Label] [DecidableEq Label]
  [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => P × D
local notation "𝓙" => 𝓘(ℝ,D)

local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
local notation "Source" => Fin (m+1) → Fin (m+1) → ℝ

def round3ParameterInverseForcingTensor
    (e : OpenPartialHomeomorph X X) (cutoff : X → ℝ) (H : X → Tensor) : X → Tensor :=
  fun z => cutoff (e.symm z) • (H (e.symm z)).bilinearComp
    (actualJointSpatialJacobian e.symm z) (actualJointSpatialJacobian e.symm z)

def round3ParameterInverseForcing
    (e : OpenPartialHomeomorph X X) (cutoff : X → ℝ) (H : X → Tensor) : X → Source :=
  fun z => actualTensorBasisCoefficients (round3ParameterInverseForcingTensor e cutoff H z)

def round3ParameterSupportedWave
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (c : P → D → M) (hR hI : X → Source)
    (a : OpenPartialHomeomorph (P × M) X) (psi : P × M → ℝ)
    (tau : ℝ) (length : ℕ) : P × M → V :=
  let ZR := actualSecondaryRealChannel F hF c hR hI tau length
  let ZI := actualSecondaryImagChannel F hF c hR hI tau length
  fun y => Real.cos (psi y / tau) • (if y ∈ a.source then ZR (a y) else 0) -
    Real.sin (psi y / tau) • (if y ∈ a.source then ZI (a y) else 0)

/-- Pure actual choices, without derivative-order, budget or observer fields. -/
structure Round3ParameterSecondaryChoice (P M : Type*) [TopologicalSpace P]
    [TopologicalSpace M] (m : ℕ) where
  host : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m+1)))
  chart : OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1)))
  c : P → EuclideanSpace ℝ (Fin (m+1)) → M
  cutoff : P × M → ℝ

def round3ParameterSecondaryQuadratic
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (e : OpenPartialHomeomorph M D)
    (r : (Label × Label) × Fin 4) :=
  incrementsSecondaryQuadraticForcing
    (fun nu p x => g.phase nu (p,e.symm x)) tau (fun _ _ _ _ => 1)
    (fun nu p beta x => delta • round3ParameterPrimaryExtension F hF g input length tau true nu beta (p,e.symm x))
    (fun nu p beta x => delta • round3ParameterPrimaryExtension F hF g input length tau false nu beta (p,e.symm x))
    (fun i _ => EuclideanSpace.single i 1) r.1.1 r.1.2 r.2

def round3ParameterSecondaryPhase
    (F : P → M → V)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (r : (Label × Label) × Fin 4) (y : P × M) : ℝ :=
  ![g.phase r.1.1 y+g.phase r.1.2 y,g.phase r.1.1 y-g.phase r.1.2 y,
    -g.phase r.1.1 y+g.phase r.1.2 y,-g.phase r.1.1 y-g.phase r.1.2 y] r.2

def round3ParameterSecondaryRealForcing
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m) :=
  let b := (OpenPartialHomeomorph.refl P).prod choice.host
  round3ParameterInverseForcing (b.symm.trans choice.chart) (choice.cutoff ∘ b.symm)
    (fun z => actualRealTensorAssembly (round3ParameterSecondaryQuadratic F hF g input length tau delta choice.host r z))

def round3ParameterSecondaryImagForcing
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m) :=
  let b := (OpenPartialHomeomorph.refl P).prod choice.host
  round3ParameterInverseForcing (b.symm.trans choice.chart) (choice.cutoff ∘ b.symm)
    (fun z => actualImaginaryTensorAssembly (round3ParameterSecondaryQuadratic F hF g input length tau delta choice.host r z))

def round3ParameterSecondaryPiece
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m) : P × M → V :=
  round3ParameterSupportedWave F hF choice.c
    (round3ParameterSecondaryRealForcing F hF g input length tau delta r choice)
    (round3ParameterSecondaryImagForcing F hF g input length tau delta r choice)
    choice.chart (round3ParameterSecondaryPhase F g r) tau length

def round3ParameterSecondarySum
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m) :
    P × M → V :=
  actualSecondaryRefinedNonzeroSum (fun r a =>
    if h : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 then
      round3ParameterSecondaryPiece F hF g input length tau delta r (choice ⟨r,h⟩ a) else 0)


/-- One actual increment, fixed before any derivative order or observation chart. -/
def round3ParameterIncrementMap
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m) :
    P × M → V :=
  fun y => delta • round3ParameterPrimaryWave F hF g input length tau y +
    round3ParameterSecondarySum F hF g input length tau delta choice y

end GlobalEmbedding.Continuation
