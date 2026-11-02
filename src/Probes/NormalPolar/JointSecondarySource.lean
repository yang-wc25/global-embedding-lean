import NormalPolar.JointSecondaryFamily

/-! The produced joint data is bound to the literal physical secondary source.

The source uses the same original chart and actual negative quadratic tensor.
All primitive field identities follow from construction. Consequently the
entire supported wave, including its zero extension, is one fixed function.
-/

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

theorem jointSecondary_raw_geometry_chart_preserves
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M))
    (d : ActualSecondaryRawGeometry F hF n j ell Mg W) :
    Round3ParameterChartPreserves d.chart := by
  intro z hz
  have h := congrArg Prod.fst (d.inverse (d.chart z) (d.chart.map_source hz))
  rw [d.chart.left_inv hz] at h
  exact h.symm

def jointSecondarySourceOfRawGeometry
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M))
    (d : ActualSecondaryRawGeometry F hF n j ell Mg W)
    (host : OpenPartialHomeomorph M D) (cutoff : Ep × M → ℝ)
    (phase : Label → Ep × M → ℝ) (R Q : Label → Ep × M → V)
    (tau : ℝ) (rec : (Label × Label) × Fin 4) :
    ActualProbeSecondaryParameterSource Ep M m :=
  actualParameterSecondarySourceOfPrimary phase R Q tau rec
    { host := host, chart := d.chart, c := d.c, cutoff := cutoff }
    (jointSecondary_raw_geometry_chart_preserves F hF n j ell Mg W d)

variable
    (F : Ep → M → (EuclideanSpace ℝ (Fin N))) (hF : ∀ b, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,(EuclideanSpace ℝ (Fin N))) ∞ (F b))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (geometry : (ActualSecondarySignedRecord Label) → Sub → ActualSecondaryRawGeometry F hF n j ell Mg W)
    (host : (ActualSecondarySignedRecord Label) → Sub → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m+1))))
    (cutoff : (ActualSecondarySignedRecord Label) → Sub → Ep × M → ℝ)
    (phase : Label → Ep × M → ℝ) (R Q : Label → Ep × M → (EuclideanSpace ℝ (Fin N))) (tau : ℝ)
    (data : (ActualSecondarySignedRecord Label) → Sub → ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (spec : JointSecondaryFamilySpec F hF n j ell Mg CH delta W
      geometry host cutoff phase R Q tau data)

include spec

theorem jointSecondary_piece_eq_physical_source
    (rec : Rec) (b : Sub) (tau' : ℝ) (length : ℕ) :
    (data rec b).base.wave tau' length =
      (jointSecondarySourceOfRawGeometry F hF n j ell Mg W (geometry rec b)
        (host rec b) (cutoff rec b) phase R Q tau rec.val).wave F hF tau' length := by
  rcases spec rec b with ⟨hc,hchart,hphase,hs,hsample,hr,hi,hw⟩
  rw [hw tau' length]
  rfl

theorem jointSecondary_sum_eq_physical_source
    (tau' : ℝ) (length : ℕ) :
    actualConstructedSecondarySum F hF (fun rec b => (data rec b).base) tau' length =
      actualParameterSecondarySourceSum F hF
        (fun rec b => jointSecondarySourceOfRawGeometry F hF n j ell Mg W (geometry rec b)
          (host rec b) (cutoff rec b) phase R Q tau rec.val) tau' length := by
  unfold actualConstructedSecondarySum actualParameterSecondarySourceSum
    actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
  funext z
  apply Finset.sum_congr rfl
  intro nu _
  apply Finset.sum_congr rfl
  intro mu _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [actualConstructedSecondaryFamily]
  split_ifs with h
  · exact congrFun (jointSecondary_piece_eq_physical_source F hF n j ell Mg CH delta W
      geometry host cutoff phase R Q tau data spec ⟨((nu,mu),q),h⟩ b tau' length) z
  · rfl

theorem jointSecondary_sum_jets_eq_physical_source
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (kappa : Y → Ep × M) (tau' : ℝ) (length k : ℕ) (y : Y) :
    iteratedFDeriv ℝ k (actualConstructedSecondarySum F hF (fun rec b => (data rec b).base)
      tau' length ∘ kappa) y =
    iteratedFDeriv ℝ k (actualParameterSecondarySourceSum F hF
      (fun rec b => jointSecondarySourceOfRawGeometry F hF n j ell Mg W (geometry rec b)
        (host rec b) (cutoff rec b) phase R Q tau rec.val) tau' length ∘ kappa) y := by
  rw [jointSecondary_sum_eq_physical_source F hF n j ell Mg CH delta W
    geometry host cutoff phase R Q tau data spec tau' length]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_sum_eq_physical_source
#print axioms GlobalEmbedding.Continuation.jointSecondary_sum_jets_eq_physical_source
