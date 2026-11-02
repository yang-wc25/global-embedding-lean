import Probes.Round4PrescribedGlobalWave

/-!
# The actual prescribed wave needs phase regularity only on its carrier charts

The actual amplitudes and their finite external-parameter columns are
unchanged. On the original closed relative carrier, its open source chart
supplies the phase germ. Outside that carrier, the actual reconstructed
amplitudes vanish on a common neighborhood before any spatial derivative is
taken. Thus all original observed jets and their parameter responses are
valid without a smooth extension of an inactive local phase.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff BigOperators Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Pspace" => Fin p → ℝ

theorem round4_prescribed_global_wave_joint_smooth_local_phase
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) (W ∩ (a l).source))
    : ContMDiffOn ((𝓘(ℝ,Pspace)).prod ((𝓘(ℝ,Ep)).prod I)) 𝓘(ℝ,V) ∞
      (fun z : Pspace × (Ep × M) => round4PrescribedGlobalWave label F hF c vf phase tau length a z.1 z.2)
      (univ ×ˢ W) := by
  classical
  have ha (l : Fin r) (ch : Bool) := round4_prescribed_global_parameter_joint_smooth ch label l F hF
    (c l) (vf l) tau length (a l) W (K l) hW (hK l) (hKsource l) (hchart l)
    (hA l) (hB l) (hG l) (hJ l) (hT l) (hBR l) (hvf l) (hinput l)
  have hprojection : ContMDiff ((𝓘(ℝ,Pspace)).prod ((𝓘(ℝ,Ep)).prod I))
      ((𝓘(ℝ,Ep)).prod I) ∞ (Prod.snd : Pspace × (Ep × M) → Ep × M) := contMDiff_snd
  have hzero (l : Fin r) (ch : Bool) (u : Pspace) (z : Ep × M)
      (hz : z ∈ W) (hn : z ∉ K l) :
      round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l) tau length (a l) u z = 0 := by
    have hs := (round4_prescribed_global_amplitude_smooth ch label l F hF (c l) (vf l)
      tau length (a l) W (K l) hW (hK l) (hKsource l) (hchart l)
      (hA l) (hB l) (hG l) (hJ l) (hT l) (hBR l) (hvf l) (hinput l) u).2
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y : W => round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l)
        tau length (a l) u y) (x := ⟨z,hz⟩) (fun h => hn (hs h))
  intro z hz
  apply ContMDiffWithinAt.sum
  intro l _
  by_cases hk : z.2 ∈ K l
  · have hp := ((hphase l).contMDiffAt
        ((hW.inter (a l).open_source).mem_nhds ⟨hz.2,hKsource l hk⟩)).comp z
        hprojection.contMDiffAt
    exact ((Real.contDiff_cos.comp_contMDiffWithinAt (hp.div_const tau).contMDiffWithinAt).smul
      (ha l false z hz)).sub
      ((Real.contDiff_sin.comp_contMDiffWithinAt (hp.div_const tau).contMDiffWithinAt).smul
        (ha l true z hz))
  · let O : Set (Ep × M) := Subtype.val '' (Subtype.val ⁻¹' K l : Set W)ᶜ
    have hO : IsOpen O := hW.isOpenMap_subtype_val _ (hK l).isOpen_compl
    have hzO : z.2 ∈ O := ⟨⟨z.2,hz.2⟩,hk,rfl⟩
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
    filter_upwards [(hO.preimage continuous_snd).mem_nhds hzO] with y hy
    obtain ⟨w,hw,he⟩ := hy
    have hyW : y.2 ∈ W := he ▸ w.property
    have hyK : y.2 ∉ K l := he ▸ hw
    change Real.cos (phase l y.2/tau) •
      round4PrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) y.1 y.2 -
      Real.sin (phase l y.2/tau) •
      round4PrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) y.1 y.2 = 0
    simp only [hzero l false y.1 y.2 hyW hyK,hzero l true y.1 y.2 hyW hyK,smul_zero,sub_zero]


theorem round4_prescribed_global_observed_contDiffOn_local_phase
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) (W ∩ (a l).source))
    (b : Ep) (obs : D → M) (O : Set D)
    (hobs : ContMDiffOn 𝓘(ℝ,D) I ∞ obs O) (hOW : ∀ y ∈ O, (b,obs y) ∈ W)
    (u : Pspace) :
    ContDiffOn ℝ ∞ (fun y => round4PrescribedGlobalWave label F hF c vf phase tau length a u (b,obs y)) O := by
  have hw := round4_prescribed_global_wave_joint_smooth_local_phase label F hF c vf phase tau length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase
  have he : ContMDiffOn 𝓘(ℝ,D) ((𝓘(ℝ,Pspace)).prod ((𝓘(ℝ,Ep)).prod I)) ∞
      (fun y => (u,(b,obs y))) O := contMDiffOn_const.prodMk (contMDiffOn_const.prodMk hobs)
  exact (hw.comp he (fun y hy => ⟨mem_univ _,hOW y hy⟩)).contDiffOn

theorem round4_prescribed_global_observed_jet_response_local_phase
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) (W ∩ (a l).source))
    (b : Ep) (obs : D → M) (O : Set D) (hO : IsOpen O)
    (hobs : ContMDiffOn 𝓘(ℝ,D) I ∞ obs O) (hOW : ∀ y ∈ O, (b,obs y) ∈ W)
    (j : ℕ) (u : Pspace) (x : D) (hx : x ∈ O) :
    let wave := fun v y => round4PrescribedGlobalWave label F hF c vf phase tau length a v (b,obs y)
    let J := probeColumnMap (fun q => iteratedFDeriv ℝ j (wave (Pi.single q 1)) x)
    iteratedFDeriv ℝ j (wave u) x = J u ∧
      HasFDerivAt (fun v => iteratedFDeriv ℝ j (wave v) x) J u := by
  intro wave J
  have hc (q : Fin p) : ContDiffAt ℝ j (wave (Pi.single q 1)) x :=
    ((round4_prescribed_global_observed_contDiffOn_local_phase label F hF c vf phase tau length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase
      b obs O hobs hOW (Pi.single q 1)).contDiffAt (hO.mem_nhds hx)).of_le (by simp)
  have heq (v : Pspace) : wave v = finiteProbeSource (fun q => wave (Pi.single q 1)) v := by
    funext y
    exact round4PrescribedGlobalWave_columns label F hF c vf phase tau length a hA hB hBR hvf v (b,obs y)
  have hj (v : Pspace) : iteratedFDeriv ℝ j (wave v) x = J v := by
    rw [heq]
    exact iteratedFDeriv_finiteProbeSource (fun q => wave (Pi.single q 1)) v j x hc
  refine ⟨hj u,?_⟩
  have hf : (fun v => iteratedFDeriv ℝ j (wave v) x) = J := funext hj
  rw [hf]
  exact J.hasFDerivAt

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_wave_joint_smooth_local_phase
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_observed_contDiffOn_local_phase
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_observed_jet_response_local_phase
