import Repair.FullIncrementNovOpenPreparedMean

/-!
# Actual-scale internal mean preparation

This internal record keeps every original field, domain and bound unchanged.
Its refinement certificate concerns only the actual scale ell. No later
argument may infer refinement at a different scale. This removes an unused
all-scale intermediate premise; it does not manufacture the original
uniform numerical budgets. The frozen all-scale definition is unchanged.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
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
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

structure IncrementsCompletionAtScaleMeanPreparation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (G : Set (P × M)) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub : ℕ) (ell : ℝ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) where
  host : Fin Data.primaryCount → Sub → Fin Data.atlas.count
  native : Fin Data.primaryCount → Sub → OpenPartialHomeomorph X X
  slices : Fin Data.primaryCount → Sub → Ep → OpenPartialHomeomorph M D
  data : ∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (host nu a)) (native nu a)
    (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (slices nu a)
  active : ∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (native nu a)).source →
    ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data
  native_open : ∀ nu a, (native nu a).source ⊆ actualOriginalNativeOpen Data (host nu a,i.2)
  same_fields :
    let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)
    let actual := actualOriginalPrimaryFamily Data hd hs hn i host native slices data gN.eta active
    actual.phase = gN.phase ∧ actual.cutoff = gN.cutoff ∧ actual.normal = gN.normal ∧
      actual.linearArgument = gN.linearArgument ∧ actual.eta = gN.eta ∧
      actual.chart = gN.chart ∧ actual.inverse = gN.inverse
  refinement :
    Round3ParameterRefinementSamples Data i.2 (actualOriginalOpenParameterSlice Data i)
      (actualOriginalPrimaryFamily Data hd hs hn i host native slices data
        (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta active)
      host native (actualOriginalParameterNeighborhood Data i.2 G)
      ell Tinv Forward Meta Rsub Data.primaryCount
  transverse : ∀ nu a z, z ∈ (native nu a).target → ∀ v : Tdata, cT*‖v‖^2 ≤
    ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data i z.1)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1) (slices nu a z.1).symm z.2 v‖^2

/-- The previous stronger preparation restricts to its actual scale, with
all seven computational fields and every original domain unchanged. -/
def incrementsCompletion_original_preparation_at_scale
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (G : Set (P × M)) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub : ℕ)
    (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (prep : FullIncrementNovOpenNativeMeanPreparation Data hd hs hn g G cT Tinv Forward Meta Rsub i) :
    IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g G cT Tinv Forward Meta Rsub ell i where
  host := prep.host
  native := prep.native
  slices := prep.slices
  data := prep.data
  active := prep.active
  native_open := prep.native_open
  same_fields := prep.same_fields
  refinement := prep.refinement ell hell hell1
  transverse := prep.transverse

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_preparation_at_scale
