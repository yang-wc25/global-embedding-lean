import Probes.ActualIncrementOriginalPrimaryFamily

/-! Original free-normal conditions supply the actual beta kernel of the
SAME constructed family and its literal conditional LocalFree at every point.
The original sqrt2*tau amplitude, signs and finite-source definition are kept. -/
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

variable {Β : Type*} [Fintype Β]

private theorem actual_transverse_kernel_congr
    (f g : M → V) (hf : ContMDiff 𝓙 𝓘(ℝ,V) ∞ f) (hg : ContMDiff 𝓙 𝓘(ℝ,V) ∞ g)
    (hfg : f = g) (chart : Es → M) (x : Es) (n : V)
    (hnf : n ∈ normalSpace (I := 𝓙) f (chart x))
    (hng : n ∈ normalSpace (I := 𝓙) g (chart x))
    (hk : incrementsTransversePairing g hg (chart x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart x a.succ) ⟨n,hng⟩ = 0) :
    incrementsTransversePairing f hf (chart x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart x a.succ) ⟨n,hnf⟩ = 0 := by
  cases hfg
  exact hk

theorem actualOriginalPrimaryFamily_normal_kernel
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
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let g := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    ∀ (hz : z ∈ (g.chart nu beta).target),
      incrementsTransversePairing (F z.1) (hF z.1) (g.inverse nu beta z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse nu beta z.1) z.2 a.succ)
        ⟨g.normal nu (z.1,g.inverse nu beta z.1 z.2),g.normal_mem nu beta z hz⟩ = 0 := by
  intro F hF g hz
  have hd0 := hdata nu beta
  have ht : z ∈ (b nu beta).target := by rwa [← hd0.1]
  have hsrc := actual_host_slice_source_point _ _ _ _ hd0 z ht
  have hact := hactive nu beta _ hsrc
  rcases hd0 with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  let p := (Data.parameterChart i.2).symm z.1
  let chart := e nu beta z.1
  have hx : z.2 ∈ chart.target := by rw [het]; exact ht
  have hmap : ∀ x ∈ chart.target, (p,chart.symm x) ∈ Data.primaryDomain nu := by
    intro x hx
    have hsx : (z.1,chart.symm x) ∈
        (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source := by
      have hh := chart.map_target hx
      rwa [hes] at hh
    exact (hactive nu beta _ hsx).1
  have hadapt : ∀ x ∈ chart.target, Data.phase nu (p,chart.symm x) = x 0 := by
    intro x hx
    have hx' : x ∈ (e nu beta z.1).target := hx
    rw [het z.1] at hx'
    exact hphase (z.1,x) hx' 
  have horig := actual_original_free_normal_transverse_kernel Data hd hs hn nu p hact.2.1
    chart (he z.1) chart.target chart.open_target subset_rfl hmap hadapt z.2 hx
  have hFeq : F z.1 = fun y => Data.F (p,y) :=
    actualOriginalOpenParameterSlice_eq Data i z.1 hact.2.1
  exact actual_transverse_kernel_congr (F z.1) (fun y => Data.F (p,y)) (hF z.1)
    (incrementsOriginal_slice_contMDiff Data hd hs p hact.2.1) hFeq chart.symm z.2
    (Data.freeNormal nu (p,chart.symm z.2)) (g.normal_mem nu beta z hz)
    (hn.normal nu (p,chart.symm z.2) hact) horig

theorem actualOriginalPrimaryFamily_localFree_kernel
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
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (tau : ℝ) (nu : Fin Data.primaryCount) (beta : Β) (p : Ep) (x : Es) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let g := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    incrementsTransversePairing (F p) (hF p) (g.inverse nu beta p x)
      (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse nu beta p) x a.succ)
      (incrementsGlobalPrimaryLocalFree F g input tau nu beta p x) = 0 := by
  intro F hF g
  classical
  by_cases hz : (p,x) ∈ (g.chart nu beta).target
  · have hk := actualOriginalPrimaryFamily_normal_kernel Data hd hs hn i host b e hdata
      eta hactive nu beta (p,x) hz
    change incrementsTransversePairing (F p) (hF p) (g.inverse nu beta p x)
      (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse nu beta p) x a.succ)
      ⟨g.normal nu (p,g.inverse nu beta p x),g.normal_mem nu beta (p,x) hz⟩ = 0 at hk
    simp only [incrementsGlobalPrimaryLocalFree,dif_pos hz,map_smul]
    rw [hk,smul_zero]
  · simp only [incrementsGlobalPrimaryLocalFree,dif_neg hz,map_zero]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualOriginalPrimaryFamily_normal_kernel
#print axioms GlobalEmbedding.Continuation.actualOriginalPrimaryFamily_localFree_kernel
