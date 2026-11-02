import Probes.Round3ParameterCrossNativeData
import Probes.Round3PreparedActualStableTarget
import Probes.ActualOriginalHostTargetRestriction

/-! Whole-parameter stable targets for a fixed actual reference primary piece.
The parameter manifold is arbitrary.  The physical map is pulled back through
the actual parameter chart, and stability is required on the whole existing
cutoff support.  The resulting chart keeps all functions and all cutoff support;
there is no parameter-neighborhood shrink and no new parameter cutoff. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
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
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_whole_primary_stable_target
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (ip : Fin Ref.parameterCount) (nu : Fin Ref.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Ref ip nu W)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (hJoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
    (cF cT mu : ℝ) (hcF : 0 < cF) (hcT : 0 < cT) (hmu : 0 < mu)
    (hPointwise : ∀ y, y ∈ tsupport piece.cutoff →
      let z := actualHostAdaptedChart (Ref.atlas.chart piece.host) piece.native y
      let p := (Ref.parameterChart ip).symm z.1
      (∀ v : D, cF*‖v‖^2 ≤ ‖fderiv ℝ (F p ∘ (piece.slices z.1).symm) z.2 v‖^2) ∧
      (∀ v : Tdata, cT*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F p) (hF p) (piece.slices z.1).symm z.2 v‖^2) ∧
      mu ≤ ‖actualFreeNormalProjectionRaw
        (fderiv ℝ (F p ∘ (piece.slices z.1).symm) z.2)
        (incrementsModeAmbientTransverseFrame (F p) (hF p) (piece.slices z.1).symm z.2)
        (Ref.freeNormal nu (p,(piece.slices z.1).symm z.2))‖) :
    ∃ (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D),
      (b : X → X) = piece.native ∧ (b.symm : X → X) = piece.native.symm ∧
      (∀ p, ((e p).symm : D → M) = (piece.slices p).symm) ∧
      b.source ⊆ piece.native.source ∧
      ActualOriginalHostSliceData (Ref.atlas.chart piece.host) b
        (fun z : Ep × M => Ref.phase nu ((Ref.parameterChart ip).symm z.1,z.2)) e ∧
      tsupport piece.cutoff ⊆ (actualHostAdaptedChart (Ref.atlas.chart piece.host) b).source ∧
      (actualHostAdaptedChart (Ref.atlas.chart piece.host) b).source ⊆
        (actualHostAdaptedChart (Ref.atlas.chart piece.host) piece.native).source ∧
      (∀ z ∈ b.target, ∀ v : D,
        (cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F ((Ref.parameterChart ip).symm z.1) ∘ (e z.1).symm) z.2 v‖^2) ∧
      (∀ z ∈ b.target, ∀ v : Tdata,
        (cT/4)*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (F ((Ref.parameterChart ip).symm z.1)) (hF ((Ref.parameterChart ip).symm z.1))
          (e z.1).symm z.2 v‖^2) ∧
      ∀ z ∈ b.target, mu/2 ≤ ‖actualFreeNormalProjectionRaw
        (fderiv ℝ (F ((Ref.parameterChart ip).symm z.1) ∘ (e z.1).symm) z.2)
        (incrementsModeAmbientTransverseFrame
          (F ((Ref.parameterChart ip).symm z.1)) (hF ((Ref.parameterChart ip).symm z.1))
          (e z.1).symm z.2)
        (Ref.freeNormal nu ((Ref.parameterChart ip).symm z.1,(e z.1).symm z.2))‖ := by
  let B := Ref.parameterChart ip
  let a := actualHostAdaptedChart (Ref.atlas.chart piece.host) piece.native
  let Fn := fun p x => F (B.symm p) x
  let K := a '' tsupport piece.cutoff
  have hKt : K ⊆ piece.native.target := by
    rintro z ⟨y,hy,rfl⟩
    rw [← piece.data.1]
    exact a.map_source (piece.support hy)
  have hBtarget : ∀ z ∈ a.source, z.1 ∈ B.target := by
    intro z hz
    have hnative := piece.native_source hz.2
    exact ((round3Parameter_originalNativeOpen_iff Ref (piece.host,ip) _).mp hnative).2.1
  have hNativeF : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞
      (Function.uncurry Fn) a.source :=
    actual_original_parameter_pullback_smooth Ref hd ip (Function.uncurry F) univ
      hJoint.contMDiffOn a.source hBtarget (fun _ _ => mem_univ _)
  have hNativeNormal : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞
      (fun y : Ep × M => Ref.freeNormal nu (B.symm y.1,y.2)) a.source :=
    actual_original_parameter_pullback_smooth Ref hd ip (Ref.freeNormal nu)
      (Ref.primaryDomain nu ∩ incrementsOriginalParameterRegion Ref) (hs.normal_joint nu)
      a.source hBtarget piece.active
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  have hJointNative : ContDiffOn ℝ ∞
      (fun z : X => Fn z.1 ((piece.slices z.1).symm z.2)) piece.native.target := by
    have hh := (hNativeF.comp (hai.mono (by rw [hat]))
      (fun z (hz : z ∈ piece.native.target) => a.map_target (by rwa [hat]))).contDiffOn
    apply hh.congr
    intro z hz
    change Fn z.1 ((piece.slices z.1).symm z.2) = Fn (a.symm z).1 (a.symm z).2
    rw [hpair z hz]
  let normal := fun z : X => Ref.freeNormal nu (B.symm z.1,(piece.slices z.1).symm z.2)
  have hNormalNative : ContDiffOn ℝ ∞ normal piece.native.target := by
    have hh := (hNativeNormal.comp (hai.mono (by rw [hat]))
      (fun z (hz : z ∈ piece.native.target) => a.map_target (by rwa [hat]))).contDiffOn
    apply hh.congr
    intro z hz
    change Ref.freeNormal nu (B.symm z.1,(piece.slices z.1).symm z.2) =
      Ref.freeNormal nu (B.symm (a.symm z).1,(a.symm z).2)
    rw [hpair z hz]
  obtain ⟨O,hO,hKO,hOt,hFirst,hFrame,hNormal,hImm,hRaw⟩ :=
    round3_prepared_actual_stable_target (Ref.atlas.chart piece.host) (hd.atlas_smooth.chart_mem piece.host)
      piece.native _ piece.slices piece.data Fn (fun p => hF (B.symm p)) hJointNative
      normal hNormalNative K hKt cF cT mu hcF hcT hmu
      (by rintro z ⟨y,hy,rfl⟩; exact (hPointwise y hy).1)
      (by rintro z ⟨y,hy,rfl⟩; exact (hPointwise y hy).2.1)
      (by rintro z ⟨y,hy,rfl⟩; exact (hPointwise y hy).2.2)
  obtain ⟨b,e,hTarget,hSource,hb,hbi,hData,hAdaptedSource,hSlices⟩ :=
    actual_original_host_restrict_target (Ref.atlas.chart piece.host) (hd.atlas_smooth.chart_mem piece.host)
      piece.native _ piece.slices piece.data O hO hOt
  refine ⟨b,e,hb,hbi,hSlices,hSource,hData,?_,?_,?_,?_,?_⟩
  · intro y hy
    rw [hAdaptedSource]
    exact ⟨piece.support hy,hKO ⟨y,hy,rfl⟩⟩
  · rw [hAdaptedSource]
    exact inter_subset_left
  · intro z hz
    rw [hSlices]
    exact hFirst z (by rwa [hTarget] at hz)
  · intro z hz
    rw [hSlices]
    exact hFrame z (by rwa [hTarget] at hz)
  · intro z hz
    rw [hSlices]
    exact hNormal z (by rwa [hTarget] at hz)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_whole_primary_stable_target
