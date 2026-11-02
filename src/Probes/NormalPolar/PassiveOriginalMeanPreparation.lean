import NormalPolar.PassiveOriginalPrimaryNative
import NormalPolar.PassiveOriginalPrimaryProfiles

/-! A real whole-parameter native mean preparation. Genuine original
zero-parameter host pieces supply the actual canonical host/slices and their
transverse reserve. Original compact samples produce the common transition
profiles before ell; the result is the preparation of the very same passive
primary family, with no mean or increment estimate among the inputs. -/

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
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem passiveOriginal_mean_preparation
    (seed : IncrementsOriginalNativeData (m+1) 0 N M E₀)
    (hd₀ : IncrementsOriginalDomainConditions seed)
    (hF₀ : ContMDiff IM 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => seed.F (0,x)))
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B) (Q : Fin B.count → Set Ep)
    (hSamples : ∀ i, IsCompact (incrementsOriginalEvaluation seed.atlas B.chart
      seed.sourceNormDomain Q univ i))
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
    (cT : ℝ)
    (hTransverse : ∀ nu a z, z ∈ (b₀ nu a).target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => seed.F (0,x)) hF₀ (e₀ nu a 0).symm z.2 v‖^2) :
    let Data := passiveOriginalData (0 : E₀) seed B Q
    let gp := passiveParameterPrimary (P := P) (0 : E₀) (fun p x => seed.F (p,x)) g
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
      (hn : IncrementsOriginalFreeNormalConditions Data hd hs),
    ∃ Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      Round3ParameterOriginalChartProfiles Data gp Forward Inverse Meta ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
        Nonempty (Round3ParameterOriginalNativeMeanPreparation Data hd hs hn gp ell cT Inverse
          (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
          (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R Data.primaryCount i) := by
  intro Data gp hd hs hn
  have hSmooth (nu) (a) :
      ContMDiffOn ((𝓘(ℝ,E₀)).prod IM) ((𝓘(ℝ,E₀)).prod IM) ∞
        (g.chart nu a) (g.chart nu a).source ∧
      ContMDiffOn ((𝓘(ℝ,E₀)).prod IM) ((𝓘(ℝ,E₀)).prod IM) ∞
        (g.chart nu a).symm (g.chart nu a).target := by
    rw [← hChart nu a]
    constructor
    · have hpost : ContMDiff 𝓘(ℝ,E₀ × D) ((𝓘(ℝ,E₀)).prod IM) ∞
          (fun z : E₀ × D => z) := contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
      exact hpost.comp_contMDiffOn (hdata nu a).2.1
    · have hpre : ContMDiff ((𝓘(ℝ,E₀)).prod IM) 𝓘(ℝ,E₀ × D) ∞
          (fun z : E₀ × D => z) := contMDiff_fst.prodMk_space contMDiff_snd
      exact (hdata nu a).2.2.1.comp hpre.contMDiffOn (fun z hz => hz)
  obtain ⟨Forward,Inverse,Meta,hF,hI,hM,hProfiles⟩ := passiveOriginal_primary_profiles
    (0 : E₀) seed hd₀ B hB Q hSamples g R geom hSmooth
  refine ⟨Forward,Inverse,Meta,hF,hI,hM,hProfiles,?_⟩
  intro ell hell hell1 i
  have hg := passiveOriginal_primary_geometry (0 : E₀) seed B Q g R geom
  obtain ⟨en,hDN,hCN,hIN,hNO,hActive,hINN,hSlice⟩ := passiveOriginal_primary_native_hosts
    seed hd₀ B Q g R geom host b₀ e₀ hdata hChart hInverse hInner i.2
  let bn := fun nu a => passiveOriginalCanonicalNativeHost (B.chart i.2) (b₀ nu a)
  apply round3Parameter_actual_mean_preparation_of_global_fields Data hd hs hn rfl gp R hg
    Forward Inverse Meta hProfiles ell cT hell hell1 i host bn en hDN hActive hNO hINN hCN hIN
  intro nu a z hz v
  have hz₀ := ((passiveOriginalCanonicalNativeHost_target (B.chart i.2) (b₀ nu a) z).mp hz).2
  have hb := hTransverse nu a (0,z.2) hz₀ v
  have hBase : actualOriginalOpenParameterSlice Data i z.1 = (fun x => seed.F (0,x)) := by
    rw [actualOriginalOpenParameterSlice_eq Data i z.1 (show (Data.parameterChart i.2).symm z.1 ∈ Data.parameterOpen from mem_univ _)]
    rfl
  have he : ((en nu a z.1).symm : D → M) = (e₀ nu a 0).symm := hSlice nu a z.1
  simpa only [hBase,he] using hb

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_mean_preparation
