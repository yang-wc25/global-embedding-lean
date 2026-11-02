import NormalPolar.PassiveOriginalCanonicalHost
import NormalPolar.PassiveOriginalPrimaryGeometry
import Probes.Round3ParameterMeanPreparationOfFields

/-! Actual canonical native host data for the same passive primary family.
Only genuine zero-parameter host pieces are inputs. The new host data,
active domains, exact family-chart binding and unchanged spatial inverses
are constructed for every original parameter observer. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P Sub : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "E₀" => EuclideanSpace ℝ (Fin 0)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem passiveOriginal_primary_native_hosts
    (seed : IncrementsOriginalNativeData (m+1) 0 N M E₀)
    (hd₀ : IncrementsOriginalDomainConditions seed)
    (B : BufferedAtlas P Ep) (Q : Fin B.count → Set Ep)
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m)
      (Λ := Fin seed.primaryCount) (Β := Sub) (fun p x => seed.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry seed g R)
    (host : Fin seed.primaryCount → Sub → Fin seed.atlas.count)
    (b₀ : Fin seed.primaryCount → Sub → OpenPartialHomeomorph (E₀ × D) (E₀ × D))
    (e₀ : Fin seed.primaryCount → Sub → E₀ → OpenPartialHomeomorph M D)
    (hdata : ∀ nu a, ActualOriginalHostSliceData (seed.atlas.chart (host nu a)) (b₀ nu a)
      (fun z : E₀ × M => seed.phase nu (0,z.2)) (e₀ nu a))
    (hChart : ∀ nu a, actualHostAdaptedChart (seed.atlas.chart (host nu a)) (b₀ nu a) = g.chart nu a)
    (hInverse : ∀ nu a x, (e₀ nu a 0).symm x = g.inverse nu a 0 x)
    (hInner : ∀ nu a w, w ∈ (g.chart nu a).source → w.2 ∈ seed.atlas.inner (host nu a))
    (ip : Fin B.count) :
    let Data := passiveOriginalData (0 : E₀) seed B Q
    let gp := passiveParameterPrimary (P := P) (0 : E₀) (fun p x => seed.F (p,x)) g
    let bn := fun nu a => passiveOriginalCanonicalNativeHost (B.chart ip) (b₀ nu a)
    ∃ en : Fin seed.primaryCount → Sub → Ep → OpenPartialHomeomorph M D,
      (∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (host nu a)) (bn nu a)
        (fun z : Ep × M => Data.phase nu ((Data.parameterChart ip).symm z.1,z.2)) (en nu a)) ∧
      (∀ nu a, actualHostAdaptedChart (Data.atlas.chart (host nu a)) (bn nu a) =
        (round3ParameterNativePrimary (fun p x => Data.F (p,x)) gp (Data.parameterChart ip)).chart nu a) ∧
      (∀ nu a p x, (en nu a p).symm x = gp.inverse nu a ((Data.parameterChart ip).symm p) x) ∧
      (∀ nu a, (bn nu a).source ⊆ actualOriginalNativeOpen Data (host nu a,ip)) ∧
      (∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (bn nu a)).source →
        ((Data.parameterChart ip).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (bn nu a)).source →
        w.2 ∈ Data.atlas.inner (host nu a)) ∧
      (∀ nu a p, ((en nu a p).symm : D → M) = (e₀ nu a 0).symm) := by
  intro Data gp bn
  choose en hData hInv hForw using fun nu a => passiveOriginal_canonical_host_lift
    (B.chart ip) (seed.atlas.chart (host nu a)) (hd₀.atlas_smooth.chart_mem (host nu a))
    (b₀ nu a) (fun z : E₀ × M => seed.phase nu (0,z.2)) (e₀ nu a) (hdata nu a)
  have hEq (nu) (a) : actualHostAdaptedChart (Data.atlas.chart (host nu a)) (bn nu a) =
      (round3ParameterNativePrimary (fun p x => Data.F (p,x)) gp (Data.parameterChart ip)).chart nu a := by
    change actualHostAdaptedChart (seed.atlas.chart (host nu a))
      (passiveOriginalCanonicalNativeHost (B.chart ip) (b₀ nu a)) =
        round3ParameterChartPullback (B.chart ip) (passiveParameterChart (P := P) (0 : E₀) (g.chart nu a))
    rw [passiveOriginalCanonicalNativeHost_factorization,hChart nu a]
  have hSrc (nu) (a) (w : Ep × M)
      (hw : w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (bn nu a)).source) :
      ((0 : E₀),w.2) ∈ (g.chart nu a).source := by
    rw [hEq nu a] at hw
    exact ((round3ParameterChartPullback_source (B.chart ip)
      (passiveParameterChart (P := P) (0 : E₀) (g.chart nu a)) w).mp hw).2.1
  refine ⟨en,hData,hEq,?_,?_,?_,fun nu a w hw => hInner nu a _ (hSrc nu a w hw),hInv⟩
  · intro nu a p x
    rw [hInv nu a p]
    exact hInverse nu a x
  · intro nu a z hz
    have hzB := (passiveOriginalCanonicalNativeHost_source (B.chart ip) (b₀ nu a) z).mp hz
    have hc : z.2 ∈ (seed.atlas.chart (host nu a)).target :=
      ((actual_host_slice_geometry_inputs (seed.atlas.chart (host nu a))
        (hd₀.atlas_smooth.chart_mem (host nu a)) (b₀ nu a)
        (fun z : E₀ × M => seed.phase nu (0,z.2)) (e₀ nu a) (hdata nu a)).1 hzB.2).2
    refine ⟨?_,?_⟩
    · change ((parameterTensorModelEquiv (m+1) d).symm
          (parameterTensorModelEquiv (m+1) d z)).2 ∈ (Data.atlas.chart (host nu a)).target ∧
        ((parameterTensorModelEquiv (m+1) d).symm
          (parameterTensorModelEquiv (m+1) d z)).1 ∈ (Data.parameterChart ip).target
      simpa only [Data,passiveOriginalData,ContinuousLinearEquiv.symm_apply_apply] using And.intro hc hzB.1
    · change incrementsOriginalJointPoint Data.atlas Data.parameterChart (host nu a,ip)
        (parameterTensorModelEquiv (m+1) d z) ∈ incrementsOriginalParameterRegion Data
      rw [actual_original_jointPoint_native]
      exact ⟨mem_univ _,mem_univ _⟩
  · intro nu a w hw
    have hw0 := hSrc nu a w hw
    have ht := (g.chart nu a).map_source hw0
    have hA := geom.inverse_active nu a _ ht
    have hpoint : ((g.chart nu a (0,w.2)).1,
        g.inverse nu a (g.chart nu a (0,w.2)).1 (g.chart nu a (0,w.2)).2) = ((0 : E₀),w.2) :=
      (geom.inverse nu a _ ht).symm.trans ((g.chart nu a).left_inv hw0)
    rw [hpoint] at hA
    exact ⟨hA.1,mem_univ _,mem_univ _⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_primary_native_hosts
