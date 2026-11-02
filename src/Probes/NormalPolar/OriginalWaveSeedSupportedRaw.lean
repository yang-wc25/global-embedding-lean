import NormalPolar.GlobalWaveResponsePrescribedSource
import NormalPolar.GlobalWaveResponsePrescribedPrimitives
import NormalPolar.OriginalWaveSeedSupportedOriginal

/-! The original-wave leading responses from actual source geometry. The
five native source jet budgets and phase budget are derived from the real
joint raw profiles and adapted chart. The input binding contains only
identities of primitive objects and source/carrier domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
  GlobalEmbedding.Continuation
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade
variable {m N p r length : ℕ} {M Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private local instance rawOriginalHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance rawOriginalHessianNorm : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance rawOriginalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- The raw physical mode is the same original legal wave. No response or
reconstructed-amplitude estimate occurs in this binding. -/
structure GlobalWaveSupportedProbeBinding
    (theta : Fin r → M → ℝ) (amplitude : Fin r → M → V)
    (carrier : Fin r → Set M)
    (source : Fin r → OpenPartialHomeomorph M D) (weight : Fin r → ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (ell Mg Bchi Bnu : ℝ)
    (raw : ∀ l, ActualPrescribedSpatialRawProfiles F hF (c l) (chi l) (nu l) (a l) W (K l)
      (2+length+1) 2 ell Mg Bchi Bnu) (b : Ep) where
  geometry : ∀ l, ActualPrescribedPhysicalGeometry F hF (c l) (nu l) (a l) (phase l)
  source_inside : ∀ l, (a l).source ⊆ W
  coordinates : ∀ l y, y ∈ (source l).target → c l b y = (source l).symm y
  target : ∀ l y, y ∈ (source l).target → (b,y) ∈ (a l).target
  phase_original : ∀ l y, y ∈ (source l).target →
    y 0/weight l = theta l ((source l).symm y)
  amplitude_original : ∀ l y, y ∈ (source l).target →
    chi l (b,y) • (nu l b y : V) = amplitude l ((source l).symm y)
  samples : ∀ l x, x ∈ carrier l → (b,source l x) ∈ (raw l).sample
  slice : ∀ x, (b,x) ∈ W
  carrier : ∀ l z, z ∈ K l → z.2 ∈ carrier l

theorem globalWave_supported_responses_from_raw
    (theta : Fin r → M → ℝ) (amplitude : Fin r → M → V)
    (carrier : Fin r → Set M) (hclosed : ∀ l, IsClosed (carrier l))
    (hamplitudeZero : ∀ l x, x ∉ carrier l → amplitude l x = 0)
    (atlas : BufferedAtlas M D) (hAtlas : IsSmoothBufferedAtlas atlas)
    (hcompact : ∀ j, IsCompact (atlas.support j))
    (source : Fin r → OpenPartialHomeomorph M D)
    (hsource : ∀ l, ContMDiffOn IM 𝓘(ℝ,D) ∞ (source l) (source l).source)
    (hcarrier : ∀ l, carrier l ⊆ (source l).source)
    (weight : Fin r → ℝ) (hweight : ∀ l, 0 < weight l)
    (Mg Bchi Bnu : ℝ) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) :
    ∃ B1 B2 : ℝ, 0 < B1 ∧ 0 < B2 ∧ ∀
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (length : ℕ)
    (raw : ∀ l, ActualPrescribedSpatialRawProfiles F hF (c l) (chi l) (nu l) (a l) W (K l)
      (2+length+1) 2 (t^((11:ℝ)/10)) Mg Bchi Bnu)
    (b : Ep)
    (binding : GlobalWaveSupportedProbeBinding theta amplitude carrier source weight F hF c chi nu phase a W K
      (t^((11:ℝ)/10)) Mg Bchi Bnu raw b),
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) (t^(10:ℕ)) (t^((6:ℝ)/5)) (weight l)
    let P := fun (u : ProbeParameters r) x => round4PrescribedGlobalWave label F hF c vf phase
      (t^((6:ℝ)/5)) length a (probeParameterEmbedding label u) (b,x)
    ∀ l,
    let CH := round4PrescribedHessianErrorConstant m N length
      (fun _ : Fin 1 => weight l) (fun _ => 1) (fun _ => Bchi) (fun _ => Bnu) Mg Mg 0
    let C1 := actualPrescribedProbeJetConstant m N p 1 length
      (fun _ : Fin 1 => weight l) (fun _ => 1) (fun _ => Bchi) (fun _ => Bnu) Mg Mg
    let CV := actualRealHomogeneousConstant m N 2 length Mg
      (homogeneousSourceConstant m N (2+length+1) Mg
        (probeNormalAmplitudeConstant (2+length+1) (weight l) Bchi Bnu)) 1
    (∀ j x, x ∈ atlas.support j → ∀ (u : ProbeParameters r) (sine : Bool),
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (P v ∘ (atlas.chart j).symm)) (atlas.chart j x))
        u (Pi.single (l,sine) 1) -
      (t^((44:ℝ)/5)*probeTrig sine (weight l*theta l x/t^((6:ℝ)/5))) •
        phaseRankOneHessian (theta l ∘ (atlas.chart j).symm)
          (amplitude l ∘ (atlas.chart j).symm) (atlas.chart j x)‖ ≤
      t^((44:ℝ)/5)*originalProbeChartModulus |CH| |C1| B1 B2 t) ∧
    (∀ x (u : ProbeParameters r) (sine : Bool),
      ‖fderiv ℝ (fun v => P v x) u (Pi.single (l,sine) 1) -
        (-(t^((56:ℝ)/5))*(weight l^2)⁻¹ * probeTrig sine (weight l*theta l x/t^((6:ℝ)/5))) •
          amplitude l x‖ ≤ t^((56:ℝ)/5)*(|CV| * |t|^((1:ℝ)/10))) := by
  obtain ⟨B1,B2,hB1,hB2,hHessian⟩ := exists_uniform_globalWave_supported_paper_response
    (p:=p) (Ep:=Ep) theta amplitude carrier hclosed hamplitudeZero atlas hAtlas hcompact source hsource hcarrier
  refine ⟨B1,B2,hB1,hB2,?_⟩
  intro label F hF c chi nu phase a W K hW t ht ht1 length raw b binding vf P l CH C1 CV
  have hscale := probe_original_scale_conditions t ht ht1
  have hphase : ∀ i, ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,ℝ) ∞ (phase i) (W ∩ (a i).source) :=
    fun i => (globalWave_physical_local_phase_smooth F hF (c i) (nu i) (a i) (phase i)
      (binding.geometry i) (raw i).chart_smooth).mono inter_subset_right
  have primitive := globalWave_prescribed_primitives_from_raw F hF c chi nu phase a W K hW
    (2+length+1) 2 (t^((11:ℝ)/10)) Mg Bchi Bnu (t^(10:ℕ)) (t^((6:ℝ)/5)) weight raw hphase
  let S : Set D := {y | (b,y) ∈ (raw l).sample}
  have hS : ∀ y ∈ S, (b,y) ∈ (a l).target := fun y hy => (raw l).sample_subset hy
  have hSrc := globalWave_raw_fixed_source_jets F hF (c l) (chi l) (nu l) (a l) W (K l)
    (t^((11:ℝ)/10)) Mg Bchi Bnu hscale.1.le (raw l) b S (fun _ hy => hy)
  have hPh := globalWave_physical_source_phase F hF (c l) (nu l) (a l) (phase l)
    (binding.geometry l) b (weight l) (t^((11:ℝ)/10)) (hweight l)
  refine ⟨?_,?_⟩
  · exact hHessian label F hF c vf phase t ht ht1 length a W K hW primitive.carrier_closed
      primitive.carrier_source primitive.chart_smooth primitive.A_smooth primitive.B_smooth
      primitive.G_smooth primitive.J_smooth primitive.T_smooth primitive.BR_smooth primitive.source_smooth
      primitive.source_support hphase l b (chi l) (nu l) (weight l) (fun y => y 0/weight l) rfl
      (binding.geometry l).inverse (binding.source_inside l) hPh.1 hPh.2.2.1 hPh.2.1.contDiffOn
      (raw l).cutoff_smooth (raw l).normal_smooth S hS Mg Mg Bchi Bnu 1
      (hweight l) hMg hMg hBchi hBnu (raw l).BR_jets (raw l).cutoff_jets (raw l).normal_jets
      hSrc.1 hSrc.2.1 hSrc.2.2.1 hSrc.2.2.2.1 hSrc.2.2.2.2
      (fun k _ y _ => hPh.2.2.2 k y) (binding.coordinates l) (binding.target l)
      (binding.phase_original l) (binding.amplitude_original l)
      (fun _ x _ hx => binding.samples l x hx) binding.slice (binding.carrier l)
  · intro x u sine
    have hv := globalWave_native_value_response_supported label F hF c vf phase
      (t^((6:ℝ)/5)) length a W K hW primitive.carrier_closed primitive.carrier_source
      primitive.chart_smooth primitive.A_smooth primitive.B_smooth primitive.G_smooth
      primitive.J_smooth primitive.T_smooth primitive.BR_smooth primitive.source_smooth
      primitive.source_support hphase l b (chi l) (nu l) (t^(10:ℕ)) (t^((11:ℝ)/10))
      (weight l) (fun y => y 0/weight l) rfl (binding.geometry l).inverse (binding.source_inside l)
      hPh.1 hPh.2.2.1 hPh.2.1.contDiffOn (raw l).cutoff_smooth (raw l).normal_smooth S hS
      Mg Mg Bchi Bnu 1 (pow_nonneg ht.le _) hscale.1 hscale.2.1 hscale.2.2.1 hscale.2.2.2
      (hweight l) hMg hMg hBchi hBnu (raw l).BR_jets (raw l).cutoff_jets (raw l).normal_jets
      hSrc.1 hSrc.2.1 hSrc.2.2.1 hSrc.2.2.2.1 hSrc.2.2.2.2
      (fun k _ y _ => hPh.2.2.2 k y) (carrier l) (theta l) (amplitude l) (hamplitudeZero l) (source l) (hcarrier l)
      (binding.coordinates l) (binding.phase_original l) (binding.amplitude_original l)
      (binding.samples l) binding.slice (binding.carrier l) x u sine
    rw [probe_delta_mul_tau_eq_value_scale t ht,probe_tau_div_original_ell t ht] at hv
    exact hv.trans_eq (by rw [abs_of_pos ht]; ring)

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_supported_responses_from_raw
