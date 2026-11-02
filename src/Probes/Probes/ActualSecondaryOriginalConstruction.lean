import Probes.ActualSecondaryRawQuadraticConstruction
import Probes.ActualSecondaryConstructedSum

/-! The literal secondary map is selected once. Its host charts, adapted
charts and ordinary cutoffs are independent of every derivative order and
observation chart. Every later estimate concerns this SAME finite map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Label SubPrimary SubSecondary : Type*} [Fintype Label] [DecidableEq Label]
  [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

/-- Pure actual choices, without derivative-order, budget or observer fields. -/
structure ActualOriginalSecondaryChoice (Ep M : Type*) [NormedAddCommGroup Ep]
    [TopologicalSpace M] (m : ℕ) where
  host : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m+1)))
  chart : OpenPartialHomeomorph (Ep × M) (Ep × EuclideanSpace ℝ (Fin (m+1)))
  c : Ep → EuclideanSpace ℝ (Fin (m+1)) → M
  cutoff : Ep × M → ℝ

def actualOriginalSecondaryQuadratic
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (e : OpenPartialHomeomorph M D)
    (r : (Label × Label) × Fin 4) :=
  incrementsSecondaryQuadraticForcing
    (fun nu p x => g.phase nu (p,e.symm x)) tau (fun _ _ _ _ => 1)
    (fun nu p beta x => delta • incrementsGlobalPrimaryExtension F hF g input length tau true nu beta (p,e.symm x))
    (fun nu p beta x => delta • incrementsGlobalPrimaryExtension F hF g input length tau false nu beta (p,e.symm x))
    (fun i _ => EuclideanSpace.single i 1) r.1.1 r.1.2 r.2

def actualOriginalSecondaryPhase
    (F : Ep → M → V)
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (r : (Label × Label) × Fin 4) (y : Ep × M) : ℝ :=
  ![g.phase r.1.1 y+g.phase r.1.2 y,g.phase r.1.1 y-g.phase r.1.2 y,
    -g.phase r.1.1 y+g.phase r.1.2 y,-g.phase r.1.1 y-g.phase r.1.2 y] r.2

def actualOriginalSecondaryRealForcing
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (choice : ActualOriginalSecondaryChoice Ep M m) :=
  let b := (OpenPartialHomeomorph.refl Ep).prod choice.host
  actualSecondaryInverseForcing (b.symm.trans choice.chart) (choice.cutoff ∘ b.symm)
    (fun z => actualRealTensorAssembly (actualOriginalSecondaryQuadratic F hF g input length tau delta choice.host r z))

def actualOriginalSecondaryImagForcing
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (choice : ActualOriginalSecondaryChoice Ep M m) :=
  let b := (OpenPartialHomeomorph.refl Ep).prod choice.host
  actualSecondaryInverseForcing (b.symm.trans choice.chart) (choice.cutoff ∘ b.symm)
    (fun z => actualImaginaryTensorAssembly (actualOriginalSecondaryQuadratic F hF g input length tau delta choice.host r z))

def actualOriginalSecondaryPiece
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (choice : ActualOriginalSecondaryChoice Ep M m) : Ep × M → V :=
  actualSecondarySupportedWave F hF choice.c
    (actualOriginalSecondaryRealForcing F hF g input length tau delta r choice)
    (actualOriginalSecondaryImagForcing F hF g input length tau delta r choice)
    choice.chart (actualOriginalSecondaryPhase F g r) tau length

def actualOriginalSecondarySum
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m) :
    Ep × M → V :=
  actualSecondaryRefinedNonzeroSum (fun r a =>
    if h : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 then
      actualOriginalSecondaryPiece F hF g input length tau delta r (choice ⟨r,h⟩ a) else 0)

 theorem actual_constructed_secondary_is_same_original_sum
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (n j length : ℕ) (ell Mg CH tau delta : ℝ) (W : Set (Ep × M))
    (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
    (data : ActualSecondarySignedRecord Label → SubSecondary → ActualSecondaryPieceData F hF n j ell Mg CH delta W)
    (hc : ∀ r a, (data r a).c = (choice r a).c)
    (hchart : ∀ r a, (data r a).chart = (choice r a).chart)
    (hphase : ∀ r a, (data r a).phase = actualOriginalSecondaryPhase F g r.val)
    (hreal : ∀ r a, (data r a).hR = actualOriginalSecondaryRealForcing F hF g input length tau delta r.val (choice r a))
    (himag : ∀ r a, (data r a).hI = actualOriginalSecondaryImagForcing F hF g input length tau delta r.val (choice r a)) :
    actualConstructedSecondarySum F hF data tau length = actualOriginalSecondarySum F hF g input length tau delta choice := by
  have hw : ∀ r a, (data r a).wave tau length = actualOriginalSecondaryPiece F hF g input length tau delta r.val (choice r a) := by
    intro r a
    simp only [ActualSecondaryPieceData.wave,actualOriginalSecondaryPiece,hc,hchart,hphase,hreal,himag]
  unfold actualConstructedSecondarySum actualOriginalSecondarySum
  congr 1
  funext r a
  unfold actualConstructedSecondaryFamily
  split_ifs with h
  · exact hw ⟨r,h⟩ a
  · rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_constructed_secondary_is_same_original_sum
