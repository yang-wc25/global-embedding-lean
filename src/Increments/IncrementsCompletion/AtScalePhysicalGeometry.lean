import IncrementsCompletion.AtScaleSourceIdentity
import Repair.FullIncrementNovOpenPhysicalGeometry

/-! Actual original primary physical geometry from the unchanged actual
fields and transverse reserve. The current-scale refinement is not used to
infer any all-scale preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
variable {Sub : Type*} [Fintype Sub]

theorem incrementsCompletion_at_scale_physical_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (V0 : Set P) (cT : ℝ) (hcT : 0 < cT) (Tinv Forward Meta : ℕ → ℝ) (Rsub : ℕ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (preparedScale : ℝ)
    (prep : IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub preparedScale i)
    (G : Set (P × M)) (hG : IsOpen G) :
    Nonempty (ActualOriginalPrimaryPhysicalGeometry
      (fun p => fullIncrementNovOriginalSourceSlice Data ((Data.parameterChart i.2).symm p))
      (fun p => fullIncrementNov_original_source_slice_smooth Data hd hs ((Data.parameterChart i.2).symm p))
      (round3ParameterNativePrimary (fullIncrementNovOriginalSourceSlice Data)
        (round3Parameter_restrictPrimaryFamily (fullIncrementNovOriginalSourceSlice Data)
          (fullIncrementNovOriginalOpenFamily Data g hTarget) G hG) (Data.parameterChart i.2))) := by
  let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)
  have phys := actualOriginalPrimaryFamily_physical_geometry Data hd hs hn i prep.host prep.native
    prep.slices prep.data gN.eta prep.active hImm G hG cT hcT prep.transverse
  dsimp only at phys
  have hSame := incrementsCompletion_at_scale_open_family_native_eq Data hd hs hn g hTarget
    (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub i preparedScale prep
  dsimp only [gN] at phys
  rw [hSame] at phys
  have hW := fullIncrementNov_original_neighborhood_eq_native_domain Data i.2 G
  rw [round3Parameter_native_primary_restriction_commutes]
  simp only [hW] at phys
  exact phys

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_physical_geometry
