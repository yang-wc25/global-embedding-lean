import Repair.EntranceCanonicalRawSecondaryPiece
import Smoothing.ParameterRound2SecondaryRawPieceIndex
import Probes.ActualSecondaryOriginalForcingSupport
import Probes.ActualIncrementSecondaryRelativeForcing

/-! The numerical bound is selected BEFORE the secondary finite index type.
The proof obtains it directly from the single-piece producer, with no
Classical.choice depending on SubSecondary. Raw original fields construct every actual signed secondary piece in its
fixed host chart. The entire finite family has one uniform constant. The
returned finite displacement is exactly the choice made before derivative
orders and observation charts, including every ordered signed nonzero record.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
universe uCanonicalM
variable {m N : ℕ} {Ep M Tr : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

 theorem repairEntranceCanonical_secondary_family
    (nInput nSolve q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∀ (M : Type uCanonicalM) [TopologicalSpace M] [ChartedSpace D M]
      [IsManifold 𝓙 ∞ M] [BoundarylessManifold 𝓙 M], ∀ (Label SubPrimary SubSecondary : Type*)
      [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary], ∀
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (Ep × M)) (primary : Label → Set (Ep × M)) (j : ℕ) (ell delta tau Delta : ℝ)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
      (geom : ActualSecondarySignedRecord Label → SubSecondary → ActualSecondaryRawGeometry F hF nSolve j ell Mg W)
      (hcChoice : ∀ r a, (geom r a).c = (choice r a).c)
      (hChartChoice : ∀ r a, (geom r a).chart = (choice r a).chart)
      (hPhaseChoice : ∀ r a, (geom r a).phase = actualOriginalSecondaryPhase F g r.val)
      (hHost : ∀ r a, ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ (choice r a).host (choice r a).host.source)
      (hHostInv : ∀ r a, ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ (choice r a).host.symm (choice r a).host.target)
      (hHostSource : ∀ r a, (geom r a).chart.source ⊆
        ((OpenPartialHomeomorph.refl Ep).prod (choice r a).host).source)
      (hSupport : ∀ r a, tsupport (fun y : W => (choice r a).cutoff y.val) ∩
        Subtype.val ⁻¹' (incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
          incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2)) ⊆
        Subtype.val ⁻¹' (geom r a).support),
      let host := fun r a => (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      let transition := fun r a => (host r a).symm.trans (geom r a).chart
      let cutoff := fun r a => (choice r a).cutoff ∘ (host r a).symm
      ∀ (hCut : ∀ r a, ContDiffOn ℝ ∞ (cutoff r a) (transition r a).source)
        (hInv : ∀ r a, ContDiffOn ℝ ∞ (transition r a).symm (transition r a).target)
        (raw : ∀ r a, ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) nSolve Rsub Lprimary
          reserve Bnd Mg T F hF g input inputbar W primary (choice r a).host (transition r a).source
          ((transition r a).symm '' (geom r a).sample) tau ell Delta)
        (hcut : ∀ r a k, k ≤ nSolve → ∀ z ∈ (geom r a).sample,
          ell^k*‖iteratedFDeriv ℝ k (cutoff r a) ((transition r a).symm z)‖ ≤ Kcut)
        (hinv : ∀ r a k, 1 ≤ k → k ≤ nSolve+1 → ∀ z ∈ (geom r a).sample,
          ell^(k-1)*‖iteratedFDeriv ℝ k (transition r a).symm z‖ ≤ Tinv k),
      ∃ data : ActualSecondarySignedRecord Label → SubSecondary →
          ActualSecondaryPhysicalPieceData F hF nSolve j ell Mg CH delta W,
        (∀ r a, (data r a).base.c = (choice r a).c ∧
          (data r a).base.chart = (choice r a).chart ∧
          (data r a).base.phase = actualOriginalSecondaryPhase F g r.val ∧
          (data r a).base.support = (geom r a).support ∧
          (data r a).base.sample = (geom r a).sample ∧
          (data r a).base.hR = actualOriginalSecondaryRealForcing F hF g input (q+2) tau delta r.val (choice r a) ∧
          (data r a).base.hI = actualOriginalSecondaryImagForcing F hF g input (q+2) tau delta r.val (choice r a)) ∧
        actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau (q+2) =
          actualOriginalSecondarySum F hF g input (q+2) tau delta choice := by
  obtain ⟨CH,hCH,hpiece⟩ := repairEntranceCanonical_secondary_piece
    (m := m) (N := N) (Ep := Ep) (Tr := Tr)
    nInput nSolve q Rsub Lprimary hq horder reserve Bnd Mg Kcut hc hBnd hMg hKcut T Tinv hT hTinv
  refine ⟨CH,hCH,?_⟩
  intro M _ _ _ _
  intro Label SubPrimary SubSecondary _ _ _ _ F hF g input inputbar W primary j ell delta tau Delta choice geom hcChoice hChartChoice hPhaseChoice
    hHost hHostInv hHostSource hSupport host transition cutoff hCut hInv raw hcut hinv
  have hex : ∀ r a, ∃ out : ActualSecondaryPhysicalPieceData F hF nSolve j ell Mg CH delta W,
      out.base.c = (choice r a).c ∧ out.base.chart = (choice r a).chart ∧
      out.base.phase = actualOriginalSecondaryPhase F g r.val ∧
      out.base.support = (geom r a).support ∧ out.base.sample = (geom r a).sample ∧
      out.base.hR = actualOriginalSecondaryRealForcing F hF g input (q+2) tau delta r.val (choice r a) ∧
      out.base.hI = actualOriginalSecondaryImagForcing F hF g input (q+2) tau delta r.val (choice r a) := by
    intro r a
    have hs : ∀ y ∈ (host r a).target, (host r a).symm y ∈ W →
        y ∈ tsupport (cutoff r a) →
        (host r a).symm y ∈ incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
          incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2) →
        (host r a).symm y ∈ (geom r a).support := by
      intro y hy hyW hySupport hyPair
      have hs0 : tsupport (fun z : W => (choice r a).cutoff z.val) ⊆
          Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (choice r a).cutoff := by
        intro z hz
        exact ⟨z,hz,rfl⟩
      have hrel := actual_secondary_host_cutoff_relative_support (host r a) (choice r a).cutoff W
        (incrementsGlobalRelativeSupport W (choice r a).cutoff) (raw r a).prim.hW hs0 y hy hyW hySupport
      obtain ⟨z,hz,hzy⟩ := hrel
      have hz' : z = (⟨(host r a).symm y,hyW⟩ : W) := Subtype.ext hzy
      have hz0 : (⟨(host r a).symm y,hyW⟩ : W) ∈
          tsupport (fun z : W => (choice r a).cutoff z.val) := by simpa only [hz'] using hz
      exact hSupport r a ⟨hz0,hyPair⟩
    obtain ⟨out,hc0,hchart,hphase,hsup,hsample,hr,hi,hw⟩ := hpiece M F hF g input inputbar W primary j ell delta tau Delta
      (geom r a) (choice r a).host (hHost r a) (hHostInv r a) (hHostSource r a)
      r.val.1.1 r.val.1.2 r.val.2 (hPhaseChoice r a) (cutoff r a) (hCut r a) (hInv r a) hs
      (raw r a) (hcut r a) (hinv r a)
    refine ⟨out,hc0.trans (hcChoice r a),hchart.trans (hChartChoice r a),hphase,hsup,hsample,?_,?_⟩
    · simpa only [actualOriginalSecondaryRealForcing,actualOriginalSecondaryQuadratic,
        hChartChoice r a] using hr
    · simpa only [actualOriginalSecondaryImagForcing,actualOriginalSecondaryQuadratic,
        hChartChoice r a] using hi
  choose data hd using hex
  refine ⟨data,hd,?_⟩
  exact actual_constructed_secondary_is_same_original_sum F hF g input nSolve j (q+2) ell Mg CH tau delta W
    choice (fun r a => (data r a).base) (fun r a => (hd r a).1) (fun r a => (hd r a).2.1)
    (fun r a => (hd r a).2.2.1) (fun r a => (hd r a).2.2.2.2.2.1)
    (fun r a => (hd r a).2.2.2.2.2.2)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntranceCanonical_secondary_family
