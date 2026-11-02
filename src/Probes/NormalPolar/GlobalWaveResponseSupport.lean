import NormalPolar.GlobalWaveResponseCompactCharts

/-!
# Actual global column support and native zero jets off its carrier

Support comes from the primitive normal amplitude and the complete finite
solver, including all reconstructed terms. Local zero is established before
any derivative is taken. The full native parameter Hessian then vanishes by
commutation for the same jointly smooth global family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
  GlobalEmbedding.Continuation
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem globalWave_native_paired_column
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

    (u : ProbeParameters r) (i : Fin r) (sine : Bool) (z : Ep × M) :
    fderiv ℝ (fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (probeParameterEmbedding label v) z) u (Pi.single (i,sine) 1) =
      round4PrescribedGlobalWave label F hF c vf phase tau length a
        (Pi.single (label (i,sine)) 1) z := by
  have hd := (round4PrescribedGlobalWave_hasFDerivAt label F hF c vf phase tau length a
    hA hB hBR hvf (probeParameterEmbedding label u) z).differentiableAt
  rw [fderiv_probeParameterEmbedding_single label
    (fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a v z)
    u hd (i,sine)]
  exact round4PrescribedGlobalWave_response_column label F hF c vf phase tau length a
    hA hB hBR hvf (probeParameterEmbedding label u) z (label (i,sine))

theorem globalWave_single_column_support
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

    (i : Fin r) (sine : Bool) :
    tsupport (fun z : W => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (Pi.single (label (i,sine)) 1) z) ⊆ Subtype.val ⁻¹' K i := by
  have hsupp (imag : Bool) := (round4_prescribed_global_amplitude_smooth imag label i
    F hF (c i) (vf i) tau length (a i) W (K i) hW (hK i) (hKsource i) (hchart i)
    (hA i) (hB i) (hG i) (hJ i) (hT i) (hBR i) (hvf i) (hinput i)
    (Pi.single (label (i,sine)) 1)).2
  apply closure_minimal _ (hK i)
  intro z hz
  by_contra hn
  have hzero (imag : Bool) : round4PrescribedGlobalAmplitude imag label i F hF (c i) (vf i)
      tau length (a i) (Pi.single (label (i,sine)) 1) z = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y : W =>
      round4PrescribedGlobalAmplitude imag label i F hF (c i) (vf i)
        tau length (a i) (Pi.single (label (i,sine)) 1) y)
      (fun hm => hn (hsupp imag hm))
  apply hz
  change round4PrescribedGlobalWave label F hF c vf phase tau length a
    (Pi.single (label (i,sine)) 1) z = 0
  rw [round4PrescribedGlobalWave_single_mode,hzero false,hzero true]
  simp

/-- A relative support bound on an open domain gives an ambient zero germ. -/
theorem globalWave_zero_germ_of_relative_tsupport
    {X₀ Y : Type*} [TopologicalSpace X₀] [Zero Y]
    (W K : Set X₀) (hW : IsOpen W) (hK : IsClosed (Subtype.val ⁻¹' K : Set W))
    (f : X₀ → Y) (hsupp : tsupport (fun y : W => f y) ⊆ Subtype.val ⁻¹' K)
    (x : X₀) (hx : x ∈ W) (hn : x ∉ K) : f =ᶠ[𝓝 x] 0 := by
  let O : Set X₀ := Subtype.val '' (Subtype.val ⁻¹' K : Set W)ᶜ
  have hO : IsOpen O := hW.isOpenMap_subtype_val _ hK.isOpen_compl
  have hxO : x ∈ O := ⟨⟨x,hx⟩,hn,rfl⟩
  filter_upwards [hO.mem_nhds hxO] with y hy
  rcases hy with ⟨z,hz,rfl⟩
  exact image_eq_zero_of_notMem_tsupport (f := fun y : W => f y) (fun hm => hz (hsupp hm))

theorem globalWave_native_response_zero_off_carrier
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

    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (eta : Z → Ep × M) (O : Set Z) (hO : IsOpen O)
    (heta : ContMDiffOn 𝓘(ℝ,Z) ((𝓘(ℝ,Ep)).prod I) ∞ eta O)
    (hmap : MapsTo eta O W) (z : Z) (hz : z ∈ O)
    (u : ProbeParameters r) (i : Fin r) (sine : Bool) (hn : eta z ∉ K i) :
    let wave := fun v y => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (probeParameterEmbedding label v) (eta y)
    fderiv ℝ (fun v => wave v z) u (Pi.single (i,sine) 1) = 0 ∧
      fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (wave v)) z) u (Pi.single (i,sine) 1) = 0 := by
  intro wave
  let column := fun q => round4PrescribedGlobalWave label F hF c vf phase tau length a
    (Pi.single (label (i,sine)) 1) q
  have hsupp := globalWave_single_column_support label F hF c vf phase tau length a W K hW hK
    hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase i sine
  have hzcol := globalWave_zero_germ_of_relative_tsupport W (K i) hW (hK i) column hsupp
    (eta z) (hmap hz) hn
  have hresp (y : Z) : fderiv ℝ (fun v => wave v y) u (Pi.single (i,sine) 1) = column (eta y) :=
    globalWave_native_paired_column label F hF c vf phase tau length a W K hW hK hKsource
      hchart hA hB hG hJ hT hBR hvf hinput hphase u i sine (eta y)
  have hzero : (fun y => fderiv ℝ (fun v => wave v y) u (Pi.single (i,sine) 1)) =ᶠ[𝓝 z] 0 := by
    have he := hzcol.comp_tendsto (heta.contMDiffAt (hO.mem_nhds hz)).continuousAt
    filter_upwards [he] with y hy
    rw [hresp]
    exact hy
  refine ⟨hzero.eq_of_nhds,?_⟩
  have hGW := round4_prescribed_global_wave_joint_smooth_local_phase label F hF c vf phase tau length a
    W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase
  have hparam : ContMDiff 𝓘(ℝ,ProbeParameters r) 𝓘(ℝ,Fin p → ℝ) ∞
      (probeParameterEmbedding label) :=
    (probeParameterEmbedding label).toContinuousLinearMap.contDiff.contMDiff
  have hfst : ContMDiffOn 𝓘(ℝ,ProbeParameters r × Z) 𝓘(ℝ,ProbeParameters r) ∞
      (Prod.fst : ProbeParameters r × Z → ProbeParameters r) (Set.univ ×ˢ O) :=
    contDiff_fst.contMDiff.contMDiffOn
  have hsnd : ContMDiffOn 𝓘(ℝ,ProbeParameters r × Z) 𝓘(ℝ,Z) ∞
      (Prod.snd : ProbeParameters r × Z → Z) (Set.univ ×ˢ O) :=
    contDiff_snd.contMDiff.contMDiffOn
  have hcoords := (hparam.comp_contMDiffOn hfst).prodMk
    (heta.comp hsnd (fun q hq => hq.2))
  have hjoint : ContDiffOn ℝ ∞ (Function.uncurry wave) (Set.univ ×ˢ O) :=
    (hGW.comp hcoords (fun q hq => ⟨mem_univ _,hmap hq.2⟩)).contDiffOn
  have hcomm := actual_parameter_spatial_second_fderiv_comm (isOpen_univ.prod hO)
    (Function.uncurry wave) hjoint u z (Pi.single (i,sine) 1) ⟨mem_univ _,hz⟩
  simp only [Function.uncurry_apply_pair] at hcomm
  rw [hcomm]
  apply fderiv_of_notMem_tsupport
  intro hm
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) (tsupport_fderiv_subset ℝ hm)

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_single_column_support
#print axioms GlobalEmbedding.NormalPolar.globalWave_native_response_zero_off_carrier
