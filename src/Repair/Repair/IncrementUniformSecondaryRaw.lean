import Repair.IncrementNativeSignedReserve
import Probes.Round3PreparedParameterRawPieceFromHost

/-!
# The actual secondary raw factory with a uniform signed reserve

This is the existing physical raw factory, including its exact sample,
support, slice map and every scaled-jet profile.  Its transverse reserve is
now constructed from the numerical template cover and the derivative of the
original signed phase.  Neither a solver output nor a transverse-frame
estimate is an input to this factory.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology TensorProduct Classical ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule

private local instance uniformRawRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private local instance uniformRawSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)

variable {K : Set ((SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
  EuclideanSpace ℝ (Fin N)) × (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ))}

theorem increment_uniform_secondary_raw_piece_from_host
    (C : UniformActualGoodDictionaryCover K) (R B : ℝ) (hB : 0 < B)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (actualOriginalParameterSignedPhase Data i r.val) e)
    (rho : Ep × M → ℝ) (hRho : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ rho W)
    (hSourceDomain : (actualHostAdaptedChart (Data.atlas.chart i.1) b).source ⊆ W)
    (hNative : b.source ⊆ actualOriginalNativeOpen Data i)
    (hCarrier : tsupport rho ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W ⊆
      (actualHostAdaptedChart (Data.atlas.chart i.1) b).source)
    (hInner : ∀ y ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      y.2 ∈ Data.atlas.inner i.1)
    (Tinv Kcut Tobs : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hKcut : ∀ k, 0 ≤ Kcut k) (hTobs : ∀ k, 0 ≤ Tobs k)
    (hProfiles : ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ observer k z,
      parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (observer,i.2) →
      (z.1,(Data.atlas.chart observer).symm z.2) ∈
        tsupport rho ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W →
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer)).symm.trans
        (actualHostAdaptedChart (Data.atlas.chart i.1) b)
      ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Tobs k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Tinv k)
    (hCut : ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ n k, k ≤ n → ∀ z,
      parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i →
      ell^k*‖iteratedFDeriv ℝ k (fun y : X => rho (y.1,(Data.atlas.chart i.1).symm y.2)) z‖ ≤ Kcut n)
    (hForward : ∀ y ∈ b.source, ‖fderiv ℝ b y‖ ≤ B)
    (hUpper : ∀ y ∈ b.source,
      ‖round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Data i)
        (fun _ => Data.atlas.chart i.1) y‖ ≤ R)
    (hSigned : ∀ y ∈ b.source,
      ∃ t : C.indices, ∃ a : EdgePair (Module.finrank ℝ D+1), ∃ w : ℝ,
        w ≠ 0 ∧
        round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Data i)
          (fun _ => Data.atlas.chart i.1) y ∈ (C.template t).operatorDomain ∧
        ‖w⁻¹ • fderiv ℝ (fun x : D =>
          actualOriginalParameterSignedPhase Data i r.val (y.1,(Data.atlas.chart i.1).symm x)) y.2 -
          (C.template t).covectors a‖ < incrementUniformSignedRadius C R) :
    ∃ out : Round3PreparedParameterRawPiece Data hd hs i r W
      (fun observer : Fin Data.atlas.count => Data.atlas.chart observer)
      (fun observer => (parameterTensorModelEquiv (m+1) d) ⁻¹'
        incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet (observer,i.2)),
      out.choice = ⟨Data.atlas.chart i.1,actualHostAdaptedChart (Data.atlas.chart i.1) b,
        (fun p x => (e p).symm x),rho⟩ ∧
      out.Tinv = Tinv ∧ out.Kcut = Kcut ∧ out.Tobs = Tobs ∧
      out.cT = incrementSecondaryFrameReserve C R (B^2) ∧ out.Bnative = 1+Tobs 1 := by
  apply round3_prepared_parameter_raw_piece_from_host Data hd hs hImm i r W b e hdata
    rho hRho hSourceDomain hNative hCarrier hInner Tinv Kcut Tobs hTinv hKcut hTobs
    hProfiles hCut (incrementSecondaryFrameReserve C R (B^2))
    (incrementSecondaryFrameReserve_pos C R (B^2) (sq_pos_of_pos hB))
  intro z hz v
  obtain ⟨t,a,w,hw,hTemplate,hClose⟩ := hSigned (b.symm z) (b.map_target hz)
  exact increment_original_host_signed_frame_reserve C R B hB
    (actualOriginalOpenParameterSlice Data i)
    (actualOriginalOpenParameterSlice_contMDiff Data hd hs i)
    (Data.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1) b
    (actualOriginalParameterSignedPhase Data i r.val) e hdata
    (actualOriginalNativeOpen Data i) (actualOriginalNativeOpen_isOpen Data hd i)
    (actualOriginalOpenParameterSlice_native_contDiffOn Data hd hs i)
    hNative hForward z hz t a w hw (hUpper _ (b.map_target hz)) hTemplate hClose v

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.increment_uniform_secondary_raw_piece_from_host
