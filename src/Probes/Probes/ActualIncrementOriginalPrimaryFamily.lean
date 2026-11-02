import Probes.ActualIncrementOriginalOpenSlice
import Probes.ActualIncrementHostGeometryInputs
import Probes.ActualIncrementFreeNormalKernel
import GlobalEmbedding.Paper.IncrementsGlobalPrimaryMeanBinding

/-! Construct the ORIGINAL global-primary-family record on one genuine
parameter chart, directly from the SAME native original data and the SAME
produced host charts/slices. No phase, normal or tensor-functional binding is
an additional premise. Global assembly across distinct parameter charts is
separate; this declaration makes no replacement of the native parameter P. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)

theorem actual_original_parameter_chart_normal_mem
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (p : Ep) (x : M)
    (hactive : ((Data.parameterChart i.2).symm p,x) ∈
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :
    Data.freeNormal nu ((Data.parameterChart i.2).symm p,x) ∈
      normalSpace (I := 𝓙) (actualOriginalOpenParameterSlice Data i p) x := by
  have hF : actualOriginalOpenParameterSlice Data i p =
      fun y => Data.F ((Data.parameterChart i.2).symm p,y) :=
    actualOriginalOpenParameterSlice_eq Data i p hactive.2.1
  have hN := congrArg (fun f : M → V => normalSpace (I := 𝓙) f x) hF
  rw [hN]
  exact hn.normal nu ((Data.parameterChart i.2).symm p,x) hactive

variable {Β : Type*} [Fintype Β]

def actualOriginalPrimaryFamily
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M Es)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :
    IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) (actualOriginalOpenParameterSlice Data i) where
  phase := fun nu z => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)
  cutoff := fun nu z => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)
  normal := fun nu z => Data.freeNormal nu ((Data.parameterChart i.2).symm z.1,z.2)
  linearArgument := fun nu p x => Data.linearArgument nu ((Data.parameterChart i.2).symm p) x
  eta := eta
  chart := fun nu beta => actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)
  inverse := fun nu beta p x => (e nu beta p).symm x
  normal_mem := by
    intro nu beta z hz
    have ht : z ∈ (b nu beta).target := by rwa [← (hdata nu beta).1]
    have hsrc := actual_host_slice_source_point _ _ _ _ (hdata nu beta) z ht
    exact actual_original_parameter_chart_normal_mem Data hd hs hn i nu z.1 _
      (hactive nu beta _ hsrc)

/-- The tensor input is the literal original native bilinear tensor at the
same parameter-chart inverse. Its tangent arguments are unchanged. -/
def actualOriginalParameterTensorSlice
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (A : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (p : Ep) (x : M) : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) :=
  A ((Data.parameterChart i.2).symm p) x

theorem actualOriginalPrimaryFamily_inverse
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M Es)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (nu : Fin Data.primaryCount) (beta : Β) (z : X) :
    let g := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    (hz : z ∈ (g.chart nu beta).target) →
      (g.chart nu beta).symm z = (z.1,g.inverse nu beta z.1 z.2) := by
  intro g hz
  rcases hdata nu beta with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  exact hpair z (by rwa [← hat])

theorem actualOriginalPrimaryFamily_phase_adapted
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M Es)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (nu : Fin Data.primaryCount) (beta : Β) (z : X) :
    let g := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    (hz : z ∈ (g.chart nu beta).target) →
      g.phase nu (z.1,g.inverse nu beta z.1 z.2) = z.2 0 := by
  intro g hz
  rcases hdata nu beta with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  exact hphase z (by rwa [← hat])

theorem actualOriginalPrimaryFamily_normal_unit
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M Es)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (nu : Fin Data.primaryCount) (beta : Β) (z : X) :
    let g := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    (hz : z ∈ (g.chart nu beta).target) →
      ‖g.normal nu (z.1,g.inverse nu beta z.1 z.2)‖ = 1 := by
  intro g hz
  have ht : z ∈ (b nu beta).target := by rwa [← (hdata nu beta).1]
  have hsrc := actual_host_slice_source_point _ _ _ _ (hdata nu beta) z ht
  exact hn.unit nu _ (hactive nu beta _ hsrc)

theorem actualOriginalPrimaryFamily_tensor_argument
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M Es)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (A : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (nu : Fin Data.primaryCount) (p : Ep) (x : M) :
    let g := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    g.linearArgument nu p x (actualOriginalParameterTensorSlice Data i A p x) =
      Data.linearArgument nu ((Data.parameterChart i.2).symm p) x
        (A ((Data.parameterChart i.2).symm p) x) := by
  rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualOriginalPrimaryFamily
#print axioms GlobalEmbedding.Continuation.actualOriginalPrimaryFamily_inverse
#print axioms GlobalEmbedding.Continuation.actualOriginalPrimaryFamily_phase_adapted
#print axioms GlobalEmbedding.Continuation.actualOriginalPrimaryFamily_normal_unit
#print axioms GlobalEmbedding.Continuation.actualOriginalPrimaryFamily_tensor_argument
