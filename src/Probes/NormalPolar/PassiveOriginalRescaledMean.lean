import NormalPolar.PassiveOriginalReferenceMean
import NormalPolar.PassiveRescaledPrimary
import NormalPolar.PassiveRescaledPhaseNormal

/-! One original conditioned packet and one chart-budget sequence serve
every reference contraction c >= 1/2. The canonical physical P family has
the same literal charts, cutoffs, slices, norm samples and labels throughout.
The uniform transverse reserve is the original cT/4. -/

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
local notation "IM" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem passiveOriginal_reference_base_smooth
    (seed : IncrementsOriginalNativeData (m+1) 0 N M E₀)
    (hd : IncrementsOriginalDomainConditions seed) (hs : IncrementsOriginalSmoothInputs seed)
    (hAll : seed.parameterSet = univ) (base : Fin seed.atlas.count × Fin seed.parameterCount) :
    ContMDiff IM 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => seed.F (0,x)) := by
  rw [← passiveOriginal_seed_open_slice seed hd hAll base 0]
  exact actualOriginalOpenParameterSlice_contMDiff seed hd hs base 0

theorem passiveOriginal_reference_rescaled_mean_preparation
    (seed : IncrementsOriginalNativeData (m+1) 0 N M E₀)
    (hd₀ : IncrementsOriginalDomainConditions seed) (hs₀ : IncrementsOriginalSmoothInputs seed)
    (hn₀ : IncrementsOriginalFreeNormalConditions seed hd₀ hs₀)
    (hAll : seed.parameterSet = univ)
    (base : Fin seed.atlas.count × Fin seed.parameterCount)
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl E₀)
    (R : ℕ) (packet : Round3PreparedReferencePrimaryPacket seed hd₀ hs₀ hn₀ base Sub R)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B) (Q : Fin B.count → Set Ep)
    (hSamples : ∀ i, IsCompact (incrementsOriginalEvaluation seed.atlas B.chart
      seed.sourceNormDomain Q univ i)) :
    let Data := passiveOriginalData (0 : E₀) seed B Q
    let g := passiveOriginalReferencePrimary seed hd₀ hs₀ hn₀ base R packet
    let gp := passiveParameterPrimary (P := P) (0 : E₀) (fun p x => seed.F (p,x)) g
    let hF₀ := passiveOriginal_reference_base_smooth seed hd₀ hs₀ hAll base
    let hF := fun _ : P => hF₀
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
      (hn : IncrementsOriginalFreeNormalConditions Data hd hs),
    ∃ Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      Round3ParameterOriginalChartProfiles Data gp Forward Inverse Meta ∧
      ∀ (c : ℝ) (hc : 1/2 ≤ c),
        let hcz : c ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hc)
        let DataC := passiveRescaledData Data c
        let gC := passiveRescaledPrimary (fun p x => Data.F (p,x)) hF gp c hcz
        let hdC := passiveRescaledData_domains Data hd c
        let hsC := passiveRescaledData_smooth Data hs c
        let hnC := passiveRescaledData_free_normals Data hd hs hn c hcz
        ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
          Nonempty (Round3ParameterOriginalNativeMeanPreparation DataC hdC hsC hnC gC ell (packet.cT/4)
            Inverse (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
            (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R Data.primaryCount i) := by
  intro Data g gp hF₀ hF hd hs hn
  obtain ⟨Forward,Inverse,Meta,hFwd,hInv,hMeta,hProfiles,hPrep⟩ :=
    passiveOriginal_reference_mean_preparation seed hd₀ hs₀ hn₀ hAll base hId R packet
      B hB Q hSamples hd hs hn
  have hg := passiveOriginal_reference_primary_geometry seed hd₀ hs₀ hn₀ base R packet hAll hId
  have hgP := passiveOriginal_primary_geometry (P := P) (0 : E₀) seed B Q g R hg
  have hdata (nu) (a) : ActualOriginalHostSliceData (seed.atlas.chart (packet.piece nu a).host)
      (packet.piece nu a).native (fun z : E₀ × M => seed.phase nu (0,z.2))
      (packet.piece nu a).slices := by
    have he : (fun z : E₀ × M => seed.phase nu ((seed.parameterChart base.2).symm z.1,z.2)) =
        (fun z : E₀ × M => seed.phase nu (0,z.2)) := by
      funext z
      rw [Subsingleton.elim ((seed.parameterChart base.2).symm z.1) (0 : E₀)]
    simpa only [he] using (packet.piece nu a).data
  have hchart := passiveOriginalReferencePrimary_chart seed hd₀ hs₀ hn₀ base R packet hId
  refine ⟨Forward,Inverse,Meta,hFwd,hInv,hMeta,hProfiles,?_⟩
  intro c hc hcz DataC gC hdC hsC hnC ell hell hell1 i
  obtain ⟨en,hDN,hCN,hIN,hNO,hActive,hINN,hSlice⟩ := passiveOriginal_primary_native_hosts
    seed hd₀ B Q g R hg (fun nu a => (packet.piece nu a).host)
    (fun nu a => (packet.piece nu a).native) (fun nu a => (packet.piece nu a).slices)
    hdata (fun nu a => (hchart nu a).symm)
    (fun nu a x => (passiveOriginalReferencePrimary_inverse seed hd₀ hs₀ hn₀ base R packet hId nu a 0 x).symm)
    (fun nu a w hw => packet.source_inner nu a w ((hchart nu a) ▸ hw)) i.2
  let bn := fun nu a => passiveOriginalCanonicalNativeHost (B.chart i.2) (packet.piece nu a).native
  apply round3Parameter_actual_mean_preparation_of_global_fields DataC hdC hsC hnC rfl gC R
    (passiveRescaled_primary_geometry Data hF gp R hgP c hcz) Forward Inverse Meta
    (passiveRescaled_primary_profiles Data hF gp Forward Inverse Meta hProfiles c hcz)
    ell (packet.cT/4) hell hell1 i (fun nu a => (packet.piece nu a).host) bn en
    hDN hActive hNO hINN hCN hIN
  intro nu a z hz v
  have hz₀ := ((passiveOriginalCanonicalNativeHost_target (B.chart i.2)
    (packet.piece nu a).native z).mp hz).2
  have hTR (w : Tdata) : packet.cT*‖w‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => seed.F (0,x)) hF₀
        ((packet.piece nu a).slices 0).symm z.2 w‖^2 := by
    have hb := packet.transverse nu a (0,z.2) hz₀ w
    simpa only [passiveOriginal_seed_open_slice seed hd₀ hAll base 0] using hb
  have hQtr := passiveRescaled_transverse_quarter_reserve (fun x => seed.F (0,x)) hF₀
    ((packet.piece nu a).slices 0).symm z.2 packet.cT hTR c hc v
  have hBase : actualOriginalOpenParameterSlice DataC i z.1 = c • (fun x => seed.F (0,x)) := by
    rw [actualOriginalOpenParameterSlice_eq DataC i z.1
      (show (DataC.parameterChart i.2).symm z.1 ∈ DataC.parameterOpen from mem_univ _)]
    rfl
  have he : ((en nu a z.1).symm : D → M) = ((packet.piece nu a).slices 0).symm := hSlice nu a z.1
  simpa only [hBase,he] using hQtr

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_reference_rescaled_mean_preparation
