import NormalPolar.GroupedObservationSlice
import NormalPolar.GroupedPrescribedResponseNorms
import Main.GeneralLegalWaveObserverProfiles
import ProbesClosure.GeneralGroupedIdentity
import NormalPolar.ActualRepairSamplingAtlas

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}
namespace GeneralLegalWaveRawFamily

/-- One actual constant for every contraction and scale, in the unchanged
original sampled norm and every original paired parameter direction. The
finite cardinal bounds are used only for the linear norm sum; each true
subordinate support remains in the raw reconstruction. -/
theorem exists_original_parameter_norms
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (Omega : Fin A.count → Set D) (hcompact : ∀ i, IsCompact (Omega i))
    (htarget : ∀ i, Omega i ⊆ (A.chart i).target) (length : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau ell : ℝ),
      0 < tau → tau ≤ ell → ell ≤ 1 → 0 ≤ delta →
    ∀ (u direction : ProbeParameters r),
      probeAtlasCj (actualRepairSamplingAtlas A Omega) 1
        (fun x => fderiv ℝ (fun v => family.groupedPairMap c hc delta tau length v x) u direction) ≤
          ENNReal.ofReal (C*delta*‖direction‖) ∧
      probeAtlasCj (actualRepairSamplingAtlas A Omega) 2
        (fun x => fderiv ℝ (fun v => family.groupedPairMap c hc delta tau length v x) u direction) ≤
          ENNReal.ofReal (C*delta/tau*‖direction‖) := by
  obtain ⟨T,Pphase,hpos,hprofiles⟩ :=
    family.exists_observation_profiles_samples A hA Omega hcompact htarget
  let n := 2+1+length
  let Mg := family.geometryBudget (max n 2)
  let Bchi := family.cutoffBudget n
  let Bnu := family.normalBudget n
  let R := ∑ l : Fin r, (family.piece l).seed.refinement.count
  let C0 := globalWavePrescribedResponseCost m N n length 2 (r*R) T weight Mg Bchi Bnu (Pphase 2)
  let C := max (probeAtlasFromNativeConstant (m+1) N 1*C0)
    (probeAtlasFromNativeConstant (m+1) N 2*C0)
  have hMg : 0 ≤ Mg := (family.positive _).1.le
  have hChi : 0 ≤ Bchi := (family.positive _).2.1.le
  have hNu : 0 ≤ Bnu := (family.positive _).2.2.le
  have hT : ∀ k, 0 ≤ T k := fun k => (hpos k).1.le
  have hC0 : 0 ≤ C0 := globalWavePrescribedResponseCost_nonneg
    m N n length 2 (r*R) T weight Mg Bchi Bnu (Pphase 2) hT hMg hChi hNu
  have hC1 : probeAtlasFromNativeConstant (m+1) N 1*C0 ≤ C := le_max_left _ _
  have hC2 : probeAtlasFromNativeConstant (m+1) N 2*C0 ≤ C := le_max_right _ _
  refine ⟨C,(mul_nonneg (probeAtlasFromNativeConstant_nonneg _ _ _) hC0).trans hC1,?_⟩
  intro c hc delta tau ell htau htaul hell1 hdelta u direction
  have hell : 0 ≤ ell := htau.le.trans htaul
  let As := actualRepairSamplingAtlas A Omega
  have hAs : IsSmoothBufferedAtlas As := actualRepairSamplingAtlas_smooth A hA Omega htarget
  let Fz : Z → M → V := fun _ => c • F
  let hFz := fun _ : Z => contMDiff_const_rescale F hF c
  let cz : (l : Fin r) → Fin (family.piece l).seed.refinement.count → Z → D → M :=
    fun l s => (family.piece l).seed.coordinate s
  let chiz := fun l s => (family.piece l).seed.cutoffCoordinates s
  let nuz := fun l s => (family.piece l).seed.scaledNormal c hc s
  let az := fun l s => (family.piece l).seed.physicalChart s
  let pieceK := fun l s => (family.piece l).seed.carrier s
  let phase := fun l (z : Z × M) => weight l*(waves l).phase z.2
  have prof (i : Fin As.count) : Nonempty (JointGroupedPrescribedObservationProfiles
      Fz hFz cz chiz nuz az univ pieceK n 2 ell Mg Bchi Bnu
      (fun y => ((0 : Z),(As.chart i).symm y)) (As.chart i).target
      ((As.chart i) '' As.support i) T phase (Pphase 2)) := by
    let joint := Classical.choice (hprofiles c hc n 2 ell hell hell1 i)
    have hs : ((univ : Set Z) ×ˢ Omega i) ⊆ univ ×ˢ (A.chart i).target :=
      Set.prod_mono (subset_refl _) (htarget i)
    let sliced := joint.fixedParameter (0 : Z) hs hell
    have hd : ((fun y : D => ((0 : Z),y)) ⁻¹' (univ ×ˢ (A.chart i).target)) =
        (A.chart i).target := by ext y; simp
    have he : ((fun y : D => ((0 : Z),y)) ⁻¹' (univ ×ˢ Omega i)) = Omega i := by
      ext y; simp
    refine ⟨?_⟩
    simpa only [Fz,hFz,cz,chiz,nuz,az,pieceK,Mg,Bchi,Bnu,phase,
      As,actualRepairSamplingAtlas_chart,
      actualRepairSamplingAtlas_coordinate_support A Omega htarget i,hd,he] using sliced
  have hL (i : Fin As.count) (y : D) (_ : y ∈ (As.chart i) '' As.support i) :
      (Finset.univ.filter (fun _l : Fin r => ((0 : Z),(As.chart i).symm y) ∈ (univ : Set (Z × M)))).card ≤ r := by
    simp
  have hR (i : Fin As.count) (l : Fin r) (y : D) (_ : y ∈ (As.chart i) '' As.support i) :
      (Finset.univ.filter (fun s => ((0 : Z),(As.chart i).symm y) ∈ pieceK l s)).card ≤ R := by
    calc
      _ ≤ (Finset.univ : Finset (Fin (family.piece l).seed.refinement.count)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = (family.piece l).seed.refinement.count := by simp
      _ ≤ R := Finset.single_le_sum (f := fun q : Fin r => (family.piece q).seed.refinement.count)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have hb := groupedPrescribed_native_original_norms
    (round4PairedParameterIndex r).toEmbedding Fz hFz cz chiz nuz az univ
    (fun _ : Fin r => univ) pieceK isOpen_univ (fun _ _ => subset_univ _)
    n length (by omega) tau ell delta weight Mg Bchi Bnu htau htaul hell1 hMg hdelta hChi hNu
    As hAs (0 : Z) (fun _ => mem_univ _) T hT phase (Pphase 2)
    (fun i => Classical.choice (prof i)) r R
    (by intro i y hy; simp)
    (by
      intro i l y hy
      calc
        _ ≤ (Finset.univ : Finset (Fin (family.piece l).seed.refinement.count)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = (family.piece l).seed.refinement.count := by simp
        _ ≤ R := Finset.single_le_sum (f := fun q : Fin r => (family.piece q).seed.refinement.count)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)) u direction
  change probeAtlasCj As 1 _ ≤ _ ∧ probeAtlasCj As 2 _ ≤ _
  constructor
  · exact hb.1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hdelta) (norm_nonneg _)))
  · exact hb.2.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hdelta) htau.le) (norm_nonneg _)))

end GeneralLegalWaveRawFamily
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.exists_original_parameter_norms
