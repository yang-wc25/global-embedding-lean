import Repair.EntranceUniformReferenceProfiles

/-!
# The same primary packet with numerical reference profiles

The chart certificates below describe actual native functions, sampling
locations, and the original kernel restriction.  They contain no adapted
first/transverse/Hessian reserve.  The producer obtains these reserves from
the original C2 bound and ellipticity, and constructs the old whole-reference
interface with exactly the same pieces and fixed numerical profiles.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology Classical ENNReal TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule

private local instance entrancePacketRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance entrancePacketSquareNormed {E : Type*}
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
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

/-- Numerical certificates of the actual selected charts, expressed before
any adapted geometric output.  `kernel` uses the actual phase differential
and the original Sym² norm, including foreign-host chart compositions. -/
structure RepairUniformReferenceChartInputs
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (Forward Inverse : ℕ → ℝ) (mu : ℝ) : Prop where
  forward : ∀ nu i a j z, z ∈ (packet.piece nu i a).native.source →
    ‖iteratedFDeriv ℝ j (packet.piece nu i a).native z‖ ≤ Forward j
  inverse : ∀ nu i a j z, z ∈ (packet.piece nu i a).native.target →
    ‖iteratedFDeriv ℝ j (packet.piece nu i a).native.symm z‖ ≤ Inverse j
  source_samples : ∀ nu i a z, z ∈ (packet.piece nu i a).native.source →
    parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet ((packet.piece nu i a).host,i.2)
  source_inner : ∀ nu i a y,
    y ∈ (actualHostAdaptedChart (Ref.atlas.chart (packet.piece nu i a).host)
      (packet.piece nu i a).native).source → y.2 ∈ Ref.atlas.inner (packet.piece nu i a).host
  kernel : ∀ nu i a z, z ∈ (packet.piece nu i a).native.target → ∀ w,
    mu*‖w‖ ≤ ‖covectorRestriction
      (round4ActualPhaseOperatorInChart
        (fun p x => Ref.F ((Ref.parameterChart i.2).symm p,x))
        (fun _ => Ref.atlas.chart (packet.piece nu i a).host) ((packet.piece nu i a).native.symm z))
      (fderiv ℝ (fun x : D => Ref.phase nu
        ((Ref.parameterChart i.2).symm ((packet.piece nu i a).native.symm z).1,
          (Ref.atlas.chart (packet.piece nu i a).host).symm x))
        ((packet.piece nu i a).native.symm z).2) w‖

/-- One numerical C2/ellipticity/kernel budget constructs all adapted
reference reserves.  No finite minimum or maximum over the actual charts
appears in the output constants, and no chart is replaced or reselected. -/
theorem repairEntrance_uniform_reference_profiles
    (Forward Inverse : ℕ → ℝ) (hForward : ∀ j, 0 ≤ Forward j) (hInverse : ∀ j, 0 ≤ Inverse j)
    (mu lower C2 : ℝ) (hmu : 0 < mu) (hLower : 0 < lower) (hC2 : 0 ≤ C2)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ Ref.F)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (hMapFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet) ≠ ⊤)
    (hMap : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet)).toReal ≤ C2)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (chart : RepairUniformReferenceChartInputs Ref theta packet Forward Inverse mu) :
    ∃ profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet,
      profiles.piece = packet.piece ∧
      profiles.cF = lower/(1+Forward 1)^2 ∧
      profiles.cT = (mu/((1+Forward 1)^2*actualIncrementSortedSymmetricConstant m))^2 ∧
      profiles.MH = actualFirstFrameTransferCost Inverse 1*(actualOriginalMapJetCost (m+1) d N 0*C2) ∧
      profiles.Tinv = Inverse ∧ profiles.Tforward = Forward := by
  let B := 1+Forward 1
  have hB : 0 < B := by dsimp only [B]; have := hForward 1; linarith
  let K := actualOriginalMapJetCost (m+1) d N 0*C2
  have hK : 0 ≤ K := mul_nonneg (actualOriginalMapJetCost_nonneg (m+1) d N 0) hC2
  let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
    Ref.parameterNormDomain Ref.parameterSet
  have hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart i :=
    fun _ _ hy => hy.1
  have hCoords := parameterRound2_originalMapCoordinates_contDiffOn Ref.atlas Ref.parameterChart
    hd.atlas_smooth hd.parameter_charts_smooth Ref.F (by simpa only [modelWithCornersSelf_prod] using hFjoint)
  let Fn := fun (i : Fin Ref.atlas.count × Fin Ref.parameterCount) p x =>
    Ref.F ((Ref.parameterChart i.2).symm p,x)
  have hFn (i : Fin Ref.atlas.count × Fin Ref.parameterCount) (p : Ep) :
      ContMDiff 𝓙 𝓘(ℝ,V) ∞ (Fn i p) :=
    hFjoint.comp (contMDiff_const.prodMk contMDiff_id)
  have hJoint (nu : Fin Ref.primaryCount) (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
      (a : packet.s nu i) :
      ContDiffOn ℝ ∞ (fun z : X => Fn i z.1 ((Ref.atlas.chart (packet.piece nu i a).host).symm z.2))
        (packet.piece nu i a).native.source :=
    round4_original_native_host_joint_smooth Ref.atlas Ref.parameterChart Ref.F S hSO hCoords
      ((packet.piece nu i a).host,i.2) (packet.piece nu i a).native.source (chart.source_samples nu i a)
  have hNativeForward (nu : Fin Ref.primaryCount) (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
      (a : packet.s nu i) (y : X) (hy : y ∈ (packet.piece nu i a).native.source) :
      ‖fderiv ℝ (packet.piece nu i a).native y‖ ≤ B := by
    have h := chart.forward nu i a 1 y hy
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans (by dsimp only [B]; linarith)
  have hLow (nu : Fin Ref.primaryCount) (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
      (a : packet.s nu i) := repairEntrance_native_original_low_budgets
    (Fn i) (Ref.atlas.chart (packet.piece nu i a).host) (hd.atlas_smooth.chart_mem _)
    (packet.piece nu i a).native _ (packet.piece nu i a).slices (packet.piece nu i a).data
    (packet.piece nu i a).native.source (packet.piece nu i a).native.open_source (hJoint nu i a)
    subset_rfl lower B K hLower hB hK Inverse hInverse (by
      intro z hz v
      have hSample := (actual_original_native_evaluation_iff Ref hd
        ((packet.piece nu i a).host,i.2) z).mp (chart.source_samples nu i a z hz)
      exact hEll.lower ((Ref.parameterChart i.2).symm z.1) hSample.2.2
        (packet.piece nu i a).host z.2 hSample.1 v) (by
      intro k hk z hz
      exact round3_original_C2_native_jets Ref.atlas Ref.parameterChart Ref.F S hSO hCoords
        hMapFinite C2 hMap ((packet.piece nu i a).host,i.2) k hk z (chart.source_samples nu i a z hz))
    (hNativeForward nu i a) (chart.inverse nu i a)
  have hFrame (nu : Fin Ref.primaryCount) (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
      (a : packet.s nu i) (z : X) (hz : z ∈ (packet.piece nu i a).native.target) :=
    repairEntrance_native_original_transverse_reserve
      (Fn i) (hFn i) (Ref.atlas.chart (packet.piece nu i a).host) (hd.atlas_smooth.chart_mem _)
      (packet.piece nu i a).native _ (packet.piece nu i a).slices (packet.piece nu i a).data
      (packet.piece nu i a).native.source (packet.piece nu i a).native.open_source (hJoint nu i a)
      subset_rfl mu B hmu.le hB (hNativeForward nu i a) z hz (chart.kernel nu i a z hz)
  let profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet := {
    piece := packet.piece
    host := fun _ _ _ => rfl
    cutoff := fun _ _ _ => rfl
    forward := fun _ _ _ => rfl
    inverse := fun _ _ _ => rfl
    slices := fun _ _ _ _ => rfl
    cF := lower/B^2
    cT := (mu/(B^2*actualIncrementSortedSymmetricConstant m))^2
    MH := actualFirstFrameTransferCost Inverse 1*K
    cF_pos := div_pos hLower (sq_pos_of_pos hB)
    cT_pos := sq_pos_of_pos (div_pos hmu (mul_pos (sq_pos_of_pos hB)
      (actualIncrementSortedSymmetricConstant_pos m)))
    MH_nonneg := mul_nonneg (actualFirstFrameTransferCost_nonneg _ hInverse 1) hK
    Tinv := Inverse
    Tforward := Forward
    Tinv_nonneg := hInverse
    Tforward_nonneg := hForward
    first := fun nu i a => (hLow nu i a).1
    transverse := by
      intro nu i a z hz v
      have hOpen : (Ref.parameterChart i.2).symm z.1 ∈ Ref.parameterOpen :=
        hd.parameter_subset (by rw [hAll]; exact mem_univ _)
      have hSlice : actualOriginalOpenParameterSlice Ref i z.1 = Fn i z.1 :=
        actualOriginalOpenParameterSlice_eq Ref i z.1 hOpen
      have hFrameEq (f g : M → V) (hf : ContMDiff 𝓙 𝓘(ℝ,V) ∞ f)
          (hg : ContMDiff 𝓙 𝓘(ℝ,V) ∞ g) (heq : f = g) :
          incrementsModeAmbientTransverseFrame f hf ((packet.piece nu i a).slices z.1).symm z.2 =
          incrementsModeAmbientTransverseFrame g hg ((packet.piece nu i a).slices z.1).symm z.2 := by
        subst g
        rfl
      rw [hFrameEq _ _ _ (hFn i z.1) hSlice]
      exact hFrame nu i a z hz v
    hessian := fun nu i a => (hLow nu i a).2
    inverse_jets := chart.inverse
    forward_jets := chart.forward
    source_inner := chart.source_inner }
  exact ⟨profiles,rfl,rfl,rfl,rfl,rfl,rfl⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_uniform_reference_profiles
