import Probes.Round3PreparedPrimaryConditioning

/-! A complete actual primary reference packet from the original native
inputs. This is an existence theorem with no chosen chart, cutoff, partition,
reserve, or PhysicalGeometry premise. It produces the same literal pieces
that the original primary-family and raw mean constructors consume. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_actual_original_primary_conditioned_preparation
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart baseIndex.2 = OpenPartialHomeomorph.refl Ep)
    (B0 Ts : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B0 j) (hTs : ∀ j, 0 ≤ Ts j) (degree : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas B0 Ts degree)
    (centers : Fin Data.atlas.count → D) (radius : ℝ)
    (hBound : ∀ i, (Data.atlas.chart i) '' Data.atlas.inner i ⊆ closedBall (centers i) radius) :
    ∃ V : Set Ep, IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ Data.parameterOpen ∧
    ∃ (s : Fin Data.primaryCount → Fin Data.atlas.count → Finset X)
      (cF cT Bnative : ℝ)
      (piece : ∀ nu : Fin Data.primaryCount,
        Sigma (fun nu : Fin Data.primaryCount => Sigma (fun host : Fin Data.atlas.count => ↥(s nu host))) →
        Round3PreparedPrimaryPiece Data baseIndex.2 nu (Data.parameterOpen ×ˢ (univ : Set M))),
      0 < cF ∧ 0 < cT ∧ 0 < Bnative ∧
      (∀ nu a, (piece nu a).Bnative = Bnative) ∧
      (∀ nu a y, y ∈ tsupport (piece nu a).cutoff → y.2 ∈ Data.atlas.inner (piece nu a).host) ∧
      (∀ nu y, y ∈ incrementsGlobalRelativeSupport (V ×ˢ (univ : Set M))
          (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart baseIndex.2).symm z.1,z.2)) →
        ∀ᶠ w in 𝓝 y, ∑ a, (piece nu a).cutoff w = 1) ∧
      (∀ nu y, (Finset.univ.filter (fun a => y ∈ tsupport (piece nu a).cutoff)).card ≤
        (degree+1)*5^Module.finrank ℝ X) ∧
      (∀ nu a z, z ∈ (piece nu a).native.target → ∀ v : D,
        cF*‖v‖^2 ≤ ‖fderiv ℝ
          (actualOriginalOpenParameterSlice Data baseIndex z.1 ∘ ((piece nu a).slices z.1).symm) z.2 v‖^2) ∧
      ∀ nu a z, z ∈ (piece nu a).native.target → ∀ v : Tdata,
        cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (actualOriginalOpenParameterSlice Data baseIndex z.1)
          (actualOriginalOpenParameterSlice_contMDiff Data hd hs baseIndex z.1)
          ((piece nu a).slices z.1).symm z.2 v‖^2 := by
  obtain ⟨V,hV,hKV,hVO,s,piece,hInner,hGerm,hCount⟩ :=
    round3_actual_original_primary_preparation Data hd hs hp baseIndex hId B0 Ts hB0 hTs degree
      RS centers radius hBound
  obtain ⟨cF,cT,Bnative,out,hcF,hcT,hB,hHost,hCut,hNative,hInverse,hSlices,hBsame,hFirst,hTransverse⟩ :=
    round3_prepared_primary_common_conditioning Data hd hs hp hImm baseIndex
      (Data.parameterOpen ×ˢ (univ : Set M)) piece
  refine ⟨V,hV,hKV,hVO,s,cF,cT,Bnative,out,hcF,hcT,hB,hBsame,?_,?_,?_,hFirst,hTransverse⟩
  · intro nu a y hy
    rw [hHost]
    exact hInner nu a y (by rwa [hCut] at hy)
  · intro nu y hy
    simpa only [hCut] using hGerm nu y hy
  · intro nu y
    simpa only [hCut] using hCount nu y

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_actual_original_primary_conditioned_preparation
