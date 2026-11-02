import Probes.Round3PreparedPrimaryFactory
import Probes.ActualOriginalDataConditioning

/-! One actual finite primary packet supplies common positive first and
transverse reserves. The original cutoff functions, host assignments and all
native chart and slice-inverse functions are retained. A genuine common
native first-derivative bound is produced by a finite maximum. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_prepared_primary_common_conditioning
    {Β : Type*} [Fintype Β]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount) (W : Set (Ep × M))
    (piece : ∀ nu : Fin Data.primaryCount, Β → Round3PreparedPrimaryPiece Data baseIndex.2 nu W) :
    ∃ (cF cT Bnative : ℝ)
      (out : ∀ nu : Fin Data.primaryCount, Β → Round3PreparedPrimaryPiece Data baseIndex.2 nu W),
      0 < cF ∧ 0 < cT ∧ 0 < Bnative ∧
      (∀ nu a, (out nu a).host = (piece nu a).host) ∧
      (∀ nu a, (out nu a).cutoff = (piece nu a).cutoff) ∧
      (∀ nu a, ((out nu a).native : X → X) = (piece nu a).native) ∧
      (∀ nu a, ((out nu a).native.symm : X → X) = (piece nu a).native.symm) ∧
      (∀ nu a p, (((out nu a).slices p).symm : D → M) = ((piece nu a).slices p).symm) ∧
      (∀ nu a, (out nu a).Bnative = Bnative) ∧
      (∀ nu a z, z ∈ (out nu a).native.target → ∀ v : D,
        cF*‖v‖^2 ≤ ‖fderiv ℝ
          (actualOriginalOpenParameterSlice Data baseIndex z.1 ∘ ((out nu a).slices z.1).symm) z.2 v‖^2) ∧
      ∀ nu a z, z ∈ (out nu a).native.target → ∀ v : Tdata,
        cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (actualOriginalOpenParameterSlice Data baseIndex z.1)
          (actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex z.1)
          ((out nu a).slices z.1).symm z.2 v‖^2 := by
  obtain ⟨cF,cT,b,e,hcF,hcT,hout⟩ :=
    actual_original_data_host_family_conditioning Data hd hs hp hImm baseIndex
      (fun nu a => (piece nu a).host) (fun nu a => (piece nu a).native)
      (fun nu a => (piece nu a).slices) (fun nu a => (piece nu a).data)
      (fun nu a => (piece nu a).cutoff) (fun nu a => (piece nu a).compact)
      (fun nu a => (piece nu a).support) (fun nu a => (piece nu a).native_source)
      (fun nu a => (piece nu a).active)
  let Bnative := 1+round3PreparedFiniteMaximum (fun a : Fin Data.primaryCount × Β => (piece a.1 a.2).Bnative)
  have hB : 0 < Bnative := by
    have hmax := round3PreparedFiniteMaximum_nonneg (fun a : Fin Data.primaryCount × Β => (piece a.1 a.2).Bnative)
    dsimp only [Bnative]
    linarith
  have hBbound (nu : Fin Data.primaryCount) (a : Β) : (piece nu a).Bnative ≤ Bnative := by
    have hh := round3PreparedFiniteMaximum_bound (fun a : Fin Data.primaryCount × Β => (piece a.1 a.2).Bnative) (nu,a)
    dsimp only [Bnative]
    linarith
  let out : ∀ nu : Fin Data.primaryCount, Β → Round3PreparedPrimaryPiece Data baseIndex.2 nu W :=
    fun nu a => {
      host := (piece nu a).host
      native := b nu a
      slices := e nu a
      cutoff := (piece nu a).cutoff
      data := (hout nu a).2.2.2.2.1
      native_source := (hout nu a).1.trans (piece nu a).native_source
      source_domain := (hout nu a).2.2.2.2.2.2.1.trans (piece nu a).source_domain
      active := fun w hw => (piece nu a).active w ((hout nu a).2.2.2.2.2.2.1 hw)
      compact := (piece nu a).compact
      smooth := (piece nu a).smooth
      support := (hout nu a).2.2.2.2.2.1
      Bnative := Bnative
      positive := hB
      native_first := by
        intro z hz
        rw [(hout nu a).2.2.1]
        exact ((piece nu a).native_first z ((hout nu a).1 hz)).trans (hBbound nu a) }
  refine ⟨cF,cT,Bnative,out,hcF,hcT,hB,fun _ _ => rfl,fun _ _ => rfl,
    fun nu a => (hout nu a).2.2.1,fun nu a => (hout nu a).2.2.2.1,?_,
    fun _ _ => rfl,fun nu a => (hout nu a).2.2.2.2.2.2.2.2.1,
    fun nu a => (hout nu a).2.2.2.2.2.2.2.2.2⟩
  intro nu a p
  exact (hout nu a).2.2.2.2.2.2.2.1 p

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_primary_common_conditioning
