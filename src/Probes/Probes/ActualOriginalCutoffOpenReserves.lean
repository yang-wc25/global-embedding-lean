import Probes.ActualIncrementCompactOpenReserves
import Probes.ActualOriginalHostCompactCutoffs
import Probes.ActualIncrementHostGeometryInputs

/-! Native chosen-frame conditioning on the actual produced host cutoff.
The compact carrier is the image of this cutoff's genuine absolute support
under the same constructed adapted chart. Qualitative immersion and Good
produce numerical first/transverse reserves on a real open neighborhood.
No CompactSpace M or tangent Riemannian structure is added.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_original_host_cutoff_open_reserves
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hFjoint : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Function.uncurry F) W)
    (hpsi : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ psi W)
    (hSourceW : (actualHostAdaptedChart c b).source ⊆ W)
    (eta : Ep × M → ℝ) (hCompact : IsCompact (tsupport eta))
    (hSupport : tsupport eta ⊆ (actualHostAdaptedChart c b).source)
    (hinj : ∀ z ∈ (actualHostAdaptedChart c b).source,
      Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) z.2))
    (hgood : ∀ z ∈ (actualHostAdaptedChart c b).source,
      GoodCovector (F z.1) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => psi (z.1,x)) z.2))) :
    ∃ (cF cT : ℝ) (O0 : Set X), 0 < cF ∧ 0 < cT ∧ IsOpen O0 ∧
      (actualHostAdaptedChart c b) '' tsupport eta ⊆ O0 ∧ O0 ⊆ b.target ∧
      (∀ z ∈ O0, ∀ v : D,
        cF*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2) ∧
      ∀ z ∈ O0, ∀ v : Tdata,
        cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2 := by
  let a := actualHostAdaptedChart c b
  have hg := actual_host_slice_geometry_inputs c hc b psi e hdata
  have hpoint := actual_host_slice_source_point c b psi e hdata
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  let K := a '' tsupport eta
  have hK : IsCompact K := hCompact.image_of_continuousOn (a.continuousOn.mono hSupport)
  have hKO : K ⊆ b.target := by
    rintro _ ⟨z,hz,rfl⟩
    rw [← hat]
    exact a.map_source (hSupport hz)
  have hci : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞ (fun z => (e z.1).symm z.2) b.target := by
    have hh := (contMDiff_snd.comp_contMDiffOn hai).mono (by rw [hat] : b.target ⊆ a.target)
    apply hh.congr
    intro z hz
    exact (congrArg Prod.snd (hpair z hz)).symm
  exact actual_increment_joint_compact_open_reserves F hF e he (fun p x => psi (p,x))
    W b.target b.open_target hFjoint hpsi hci (fun z hz => (hg.2.2.2.1 z hz).1)
    (fun z hz => hSourceW (hpoint z hz)) hW
    (fun z hz => hinj _ (hpoint z hz)) hadapt
    (fun z hz => hgood _ (hpoint z hz)) K hK hKO

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_host_cutoff_open_reserves
