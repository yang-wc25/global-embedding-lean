import Smoothing.Round3OuterParameterNormalCover
import Smoothing.Round3OuterStableGlobalImmersion
import Probes.Round3PreparedPrimaryPhaseLegality

/-! The same genuine cross-parameter primary slices give the new map's
actual primary Good covectors and global immersion. The reference metric
only supplies the original active-cutoff cover. New immersion and Good
certificates are conclusions of true first and transverse reserves. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance hostCoverFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance

theorem round3_parameter_primary_good_from_actual_cover
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hK : Data.parameterSet = univ)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (A : Fin Data.primaryCount → Type*)
    (host : ∀ nu, Fin Data.parameterCount → A nu → Fin Data.atlas.count)
    (b : ∀ nu, Fin Data.parameterCount → A nu → OpenPartialHomeomorph X X)
    (e : ∀ nu, Fin Data.parameterCount → A nu → Ep → OpenPartialHomeomorph M D)
    (hData : ∀ nu ip a, ActualOriginalHostSliceData (Data.atlas.chart (host nu ip a)) (b nu ip a)
      (fun w : Ep × M => Data.phase nu ((Data.parameterChart ip).symm w.1,w.2)) (e nu ip a))
    (hCover : ∀ nu ip (w : Ep × M), w.1 ∈ (Data.parameterChart ip).target →
      ((Data.parameterChart ip).symm w.1,w.2) ∈ Data.primaryDomain nu →
      ∃ a, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)).source)
    (cT : ℝ) (hcT : 0 < cT)
    (hFrame : ∀ nu ip a z, z ∈ (b nu ip a).target → ∀ v : Tdata,
      cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
        (fun x => Data.F ((Data.parameterChart ip).symm z.1,x))
        (hF ((Data.parameterChart ip).symm z.1)) (e nu ip a z.1).symm z.2 v‖^2) :
    ∀ nu z (hz : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data),
      GoodCovector (fun x => Data.F (z.1,x))
        (incrementsOriginal_slice_contMDiff Data hd hs z.1 hz.2.1) z.2
        (incrementsOriginalPhaseCovector Data nu z.1 z.2) := by
  intro nu z hz
  obtain ⟨ip,hp,hpn⟩ := hd.parameter_cover z.1 (by rw [hK]; exact mem_univ _)
  have hLeft := (Data.parameterChart ip).left_inv hp
  let w : Ep × M := (Data.parameterChart ip z.1,z.2)
  obtain ⟨a,ha⟩ := hCover nu ip w ((Data.parameterChart ip).map_source hp) (by
    change ((Data.parameterChart ip).symm (Data.parameterChart ip z.1),z.2) ∈ Data.primaryDomain nu
    rw [hLeft]
    exact hz.1)
  have hpsi := actual_original_phase_mdifferentiableAt Data hd hs nu z.1 z.2 hz
  have hGood := round3_prepared_host_good_of_reserve (Data.atlas.chart (host nu ip a)) (b nu ip a)
    (fun y : Ep × M => Data.phase nu ((Data.parameterChart ip).symm y.1,y.2))
    (e nu ip a) (hData nu ip a)
    (fun p x => Data.F ((Data.parameterChart ip).symm p,x))
    (fun p => hF ((Data.parameterChart ip).symm p)) cT hcT (hFrame nu ip a) w ha
    (by simpa only [w,hLeft] using hpsi)
  dsimp only [w] at hGood
  rw [hLeft] at hGood
  exact hGood

theorem round3_parameter_global_immersion_from_actual_cover
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hK : Data.parameterSet = univ)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (hReference : ∀ p ∈ Data.parameterOpen, ∀ x, Data.reference p x ≠ 0)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (A : Fin Data.primaryCount → Type*)
    (host : ∀ nu, Fin Data.parameterCount → A nu → Fin Data.atlas.count)
    (b : ∀ nu, Fin Data.parameterCount → A nu → OpenPartialHomeomorph X X)
    (e : ∀ nu, Fin Data.parameterCount → A nu → Ep → OpenPartialHomeomorph M D)
    (hData : ∀ nu ip a, ActualOriginalHostSliceData (Data.atlas.chart (host nu ip a)) (b nu ip a)
      (fun w : Ep × M => Data.phase nu ((Data.parameterChart ip).symm w.1,w.2)) (e nu ip a))
    (hCover : ∀ nu ip (w : Ep × M), w.1 ∈ (Data.parameterChart ip).target →
      ((Data.parameterChart ip).symm w.1,w.2) ∈ Data.primaryDomain nu →
      ∃ a, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)).source)
    (cF : ℝ) (hcF : 0 < cF)
    (hFirst : ∀ nu ip a z, z ∈ (b nu ip a).target → ∀ v : D,
      cF*‖v‖^2 ≤ ‖fderiv ℝ ((fun x => Data.F ((Data.parameterChart ip).symm z.1,x)) ∘
        (e nu ip a z.1).symm) z.2 v‖^2) :
    IncrementsOriginalSliceImmersionInputs Data := by
  refine ⟨?_⟩
  intro p hpO x
  obtain ⟨nu,hchi⟩ := round3_original_reference_active_cutoff Data hDecomp p hpO x (hReference p hpO x)
  have hRel : (p,x) ∈ incrementsOriginalRelativeCutoffSupport Data nu := by
    rw [parameterRound2_original_relativeSupport_eq Data hd.parameter_open]
    exact ⟨⟨hpO,mem_univ _⟩,subset_tsupport _ hchi⟩
  have hDomain := hd.cutoff_support_local nu hRel
  obtain ⟨ip,hp,hpn⟩ := hd.parameter_cover p (by rw [hK]; exact mem_univ _)
  have hLeft := (Data.parameterChart ip).left_inv hp
  let w : Ep × M := (Data.parameterChart ip p,x)
  obtain ⟨a,ha⟩ := hCover nu ip w ((Data.parameterChart ip).map_source hp) (by
    change ((Data.parameterChart ip).symm (Data.parameterChart ip p),x) ∈ Data.primaryDomain nu
    rwa [hLeft])
  let chart := actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)
  let z := chart w
  have hz : z ∈ (b nu ip a).target := by rw [← (hData nu ip a).1]; exact chart.map_source ha
  have hg := actual_host_slice_geometry_inputs (Data.atlas.chart (host nu ip a))
    (hd.atlas_smooth.chart_mem (host nu ip a)) (b nu ip a) _ (e nu ip a) (hData nu ip a)
  have hi := actual_increment_immersion_of_chart_reserve
    (fun x => Data.F ((Data.parameterChart ip).symm z.1,x))
    (hF ((Data.parameterChart ip).symm z.1)) (e nu ip a z.1)
    ((hData nu ip a).2.2.2.2.1 z.1) z.2 (hg.2.2.2.1 z hz).1 cF hcF (hFirst nu ip a z hz)
  rcases hData nu ip a with ⟨hat,haa,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  have hphysical : (z.1,(e nu ip a z.1).symm z.2) = w :=
    (hpair z hz).symm.trans (chart.left_inv ha)
  have hzp : z.1 = Data.parameterChart ip p := congrArg Prod.fst hphysical
  have hzx : (e nu ip a z.1).symm z.2 = x := congrArg Prod.snd hphysical
  rw [hzx,hzp,hLeft] at hi
  exact hi

#print axioms round3_parameter_primary_good_from_actual_cover
#print axioms round3_parameter_global_immersion_from_actual_cover
end GlobalEmbedding.Continuation
