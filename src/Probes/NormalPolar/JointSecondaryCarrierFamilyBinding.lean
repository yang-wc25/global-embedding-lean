import NormalPolar.JointSecondaryCarrierFamily
import NormalPolar.JointMixedBinding

/-! The actual raw-produced complete secondary family satisfies every
original observer forcing binding. Common amplitude support is obtained from
the true background primitive and prescribed source; both observer tensor
slots are transported from the same produced host forcing. -/
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
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord (Λ ⊕ Fin r)


def jointCarrier_family_observer_binding_from_primitives
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : (l : Fin r) → Pieces l → Ep → D → M) (chi : (l : Fin r) → Pieces l → X → ℝ)
    (nu : (l : Fin r) → (s : Pieces l) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (Ep × M) X) (phase : Fin r → Ep × M → ℝ)
    (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : Ep → Fin p → ℝ)
    (W : Set (Ep × M)) (primaryDomain : Λ → Set (Ep × M))
    (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (pieceK : (l : Fin r) → Pieces l → Set (Ep × M))
    (nInput nSolve q probeLength j Rsub Lprimary : ℕ)
    (reserve Bnd Mg Kcut Bchi Bnu Ku Mphase tau ell delta Delta CH : ℝ)
    (Tbackground Tprobe Tinv : ℕ → ℝ)
    (profiles : JointGroupedSecondaryCarrierProfiles (Sub := Sub) (Tr := Tr) F hF g c chi nu a phase
      input inputbar u W primaryDomain K pieceK nInput nSolve q probeLength j Rsub Lprimary
      reserve Bnd Mg Kcut Bchi Bnu Ku Mphase tau ell delta Delta Tbackground Tprobe Tinv)
    (background : ParameterRound2GlobalMeanPrimitives F hF g input W primaryDomain)
    (nSource jSource : ℕ)
    (prescribed : ∀ l s, ActualPrescribedSpatialRawProfiles F hF (c l s) (chi l s) (nu l s) (a l s)
      W (pieceK l s) nSource jSource ell Mg Bchi Bnu)
    (weight : Fin r → ℝ)
    (data : Rec → Sub → ActualSecondaryPhysicalPieceData F hF nSolve j ell Mg CH delta W)
    (hspec : JointSecondaryFamilySpec F hF nSolve j ell Mg CH delta W
      profiles.geometry profiles.host profiles.cutoff (Sum.elim g.phase phase)
      (jointGroupedCombinedAmplitude F hF g label c
        (fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l))
        tau delta (q+2) probeLength a input u false)
      (jointGroupedCombinedAmplitude F hF g label c
        (fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l))
        tau delta (q+2) probeLength a input u true) tau data)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (hTransition : ∀ rec b, ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data rec b).base.chart)
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data rec b).base.chart).source)
    (hInverse : ∀ rec b, ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data rec b).base.chart).symm
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (data rec b).base.chart).target) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let phases := Sum.elim g.phase phase
    let R := jointGroupedCombinedAmplitude F hF g label c vf tau delta (q+2) probeLength a input u false
    let Q := jointGroupedCombinedAmplitude F hF g label c vf tau delta (q+2) probeLength a input u true
    ∀ rec : Rec,
      let b := (OpenPartialHomeomorph.refl Ep).prod e
      let H := actualParameterPrimaryQuadratic phases R Q tau e rec.val
      ActualSecondaryForcingBinding F hF (fun s => (data rec s).base) b
        (fun z => actualRealTensorAssembly (H z)) (fun z => actualImaginaryTensorAssembly (H z))
        (fun z => jointSecondarySignedPhase phases rec.val (b.symm z)) := by
  intro vf phases R Q rec b H
  have hamp := jointGrouped_common_amplitude_carrier_support F hF g label c chi nu a input
    W primaryDomain K pieceK profiles.piece_support background profiles.background_carrier nSource jSource (q+2) probeLength ell Mg Bchi Bnu tau delta weight prescribed u
  have hchart (s : Sub) : (data rec s).base.chart = (profiles.geometry rec s).chart :=
    (hspec rec s).2.1
  apply jointMixed_observer_binding F hF phases R Q W background.hW K
    (fun l => hamp false l) (fun l => hamp true l)
    nSolve j ell Mg CH tau delta rec.val (fun s => (data rec s).base)
    (profiles.host rec) (profiles.host_maximal rec)
    (fun s y hy => by rw [hchart s] at hy; exact (profiles.host_source rec s hy).2)
    (profiles.cutoff rec)
  · intro s y hy
    rw [hchart s]
    apply (profiles.geometry rec s).support_source
    apply profiles.cutoff_support rec s
    exact ⟨⟨y,hy.1,rfl⟩,hy.2⟩
  · exact profiles.partition rec
  · intro s
    exact (hspec rec s).2.2.1
  · intro s
    rw [hchart s]
    exact (hspec rec s).2.2.2.2.2.1
  · intro s
    rw [hchart s]
    exact (hspec rec s).2.2.2.2.2.2.1
  · exact he
  · exact hTransition rec
  · exact hInverse rec

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointCarrier_family_observer_binding_from_primitives

