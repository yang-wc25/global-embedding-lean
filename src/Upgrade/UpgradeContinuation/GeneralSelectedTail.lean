import UpgradeContinuation.OriginalTailPlan
import UpgradeContinuation.GeneralInitializedSelectedStatement

/-!
# The same selected q440 first map starts its actual infinite repair run

Every selected source, primitive budget, initialized parameter ball, physical
packet, and complete first increment is retained.  The actual fixed-reference
factory chooses one plan on that packet before the scale.  Its epsilon, eta
and first cap are then used by the same selected initial-state constructor.
For every admitted t the returned run starts at exactly that returned first
map, and all original first-map and secondary budgets remain available.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold Bundle GlobalEmbedding.Paper GlobalEmbedding.Offline
open GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar
open scoped ContDiff Topology ENNReal Classical

namespace GlobalEmbedding.Continuation.UpgradeContinuation

universe uM uP
variable {m d N r : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
  [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => ZeroParameter
local notation "IM" => 𝓘(ℝ,D)

private local instance signedFinite {Label : Type*} [Fintype Label] [DecidableEq Label] :
    Fintype (ActualSecondarySignedRecord Label) := by
  unfold ActualSecondarySignedRecord
  infer_instance

/-- The complete same-choice initial statement together with the actual
fixed plan and the actual run at every admitted scale. -/
def GeneralSelectedTailStatement
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (waves : Fin r → OpenSupportedLegalWave F0 hF0)
    (s : OriginalReferenceSupply (m := m) (N := N) F0)
    (B : BufferedAtlas P Ep) (Q : Fin B.count → Set Ep)
    (BP TP : ℕ → ℝ) (b : Fin B.count) (p₀ : P) : Prop :=
    let seed := s.seed
    let Data := passiveOriginalData (0 : Z) seed B Q
    let g0 := passiveOriginalReferencePrimary seed s.domain s.smooth s.freeNormal
      s.baseIndex s.refinementMultiplicity s.primary
    let gp := passiveParameterPrimary (P := P) (0 : Z) (fun p x => seed.F (p,x)) g0
    let K : (Fin seed.primaryCount ⊕ Fin r) → Set M :=
      Sum.elim (fun l => tsupport (fun x => seed.cutoff l (0,x)))
        (fun l => tsupport ((waves l).cutoff : M → ℝ))
    ∃ weight : Fin r → ℝ, (∀ l, 0 < weight l) ∧ Function.Injective weight ∧
    ∃ family : GeneralLegalWaveRawFamily F0 hF0 waves weight,
    let signedPhase := fun (rec : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r)) x =>
      jointSecondarySignedPhase
        (Sum.elim (fun l (z : Ep × M) => seed.phase l (0,z.2))
          (fun l (z : Ep × M) => weight l*(waves l).phase z.2)) rec.val (0,x)
    ∃ (O : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r) → Set M)
      (seeds : (rec : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r)) →
        JointSecondarySignedSeed («Ep» := Ep) F0 hF0 (signedPhase rec)
          (K rec.val.1.1 ∩ K rec.val.1.2) (O rec)),
    ∃ rho : ℝ, ∃ hrho : 0 < rho, ∃ Tp Pphase : ℕ → ℝ,
      (∀ k, 0 < Tp k ∧ 0 < Pphase k) ∧
    let Samples := incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ
    ∃ hSamples : ∀ i, IsCompact (Samples i),
    ∃ numbers : Round3RepairMeanPrimitiveProfiles,
      rho = numbers.rho/2 ∧
      ProbesSelectedPrimarySupplier seed.atlas B Samples hSamples (fun _ _ hy => hy.1)
        F0 hF0 gp Data.primaryDomain Data.H numbers ∧
      ProbesSelectedGeneralProfiles F0 hF0 waves weight family seed.atlas B Samples Tp Pphase ∧
    let Mgp := fun j => family.geometryBudget (max (j+444) (j+1))
    let Bchi := fun j => family.cutoffBudget (j+444)
    let Bnu := fun j => family.normalBudget (j+444)
    let Mphase := fun j => Pphase (j+1)
    let Csrc := jointGroupedPrescribedZeroSourceCost (fun l => Fin (family.piece l).seed.refinement.count)
      m N d d 444 442 Tp weight (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)
    let amplitude := passiveOriginalReserveAmplitude Csrc rho
    let Initialized := jointMixedParameterInitializedAtlas B Csrc rho hrho
    let u := passiveOriginalSmallParameter B amplitude
      (passiveOriginalReserveAmplitude_pos Csrc rho hrho) b p₀
    ∃ radius : ℝ, ∃ hradius : 0 < radius,
    ∃ packet : Round3RepairFixedSmoothingPacket Data s.fixedClass.numerical.BS s.fixedClass.numerical.TS
      BP TP s.fixedClass.numerical.Ds Initialized.supportDegree radius hradius
      (passiveOriginalPhysicalReferenceBudget Data) (passiveOriginalPhysicalFixedBudget Data),
    packet.parameterFamily = tensorChartFamilyOfAtlas Initialized ∧
    packet.referenceMap = (fun z => seed.F (0,z.2)) ∧
    packet.Omega = seed.sourceNormDomain ∧ packet.Q = Q ∧ packet.metric = Data.H ∧
    (∀ v : Fin d → ℝ, ‖v‖ < actualRepairParameterRadius packet.parameterFamily →
      u (actualRepairParameterMap packet.parameterFamily b p₀ v) = v) ∧
    ∃ CU CS : ℝ, 0 ≤ CU ∧ 0 ≤ CS ∧
    (∀ t, 0 ≤ actualProbeSecondaryModulus CS t) ∧
    Filter.Tendsto (actualProbeSecondaryModulus CS) (𝓝[>] 0) (𝓝 0) ∧
    ∃ (ΒRepair SubRepair : Type) (iΒRepair : Fintype ΒRepair) (iSubRepair : Fintype SubRepair),
    ∃ plan : ActualProbeProducedRepairPlan packet ΒRepair SubRepair,
    ∃ t0 : ℝ, ∃ ht0 : 0 < t0, ∃ ht0Half : t0 ≤ 1/2,
      t0 ≤ plan.sigma 0 ∧ ∀ (t : ℝ) (ht : 0 < t) (htt : t ≤ t0)
        (label : (Fin r × Bool) ↪ Fin d),
    let tau := t^((6 : ℝ)/5)
    let ell := t^((11 : ℝ)/10)
    let delta := t^10
    let scale := Real.sqrt (1-delta^2)
    let hscale := actual_probe_contraction_mem_Icc t ht (htt.trans ht0Half)
    let F := fun _ : P => scale • F0
    let hF := fun _ : P => contMDiff_const_rescale F0 hF0 scale
    let g := passiveRescaledPrimary (fun _ : P => F0) (fun _ => hF0) gp scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale)
    let target := (1-(tau^10/delta)^2) • Data.H
    let c : (l : Fin r) → Fin (family.piece l).seed.refinement.count → P → D → M := fun l s (_ : P) =>
      (family.piece l).seed.coordinate s 0
    let chi : (l : Fin r) → Fin (family.piece l).seed.refinement.count → P × D → ℝ := fun l s z =>
      (family.piece l).seed.cutoffCoordinates s (0,z.2)
    let nu : (l : Fin r) → (s : Fin (family.piece l).seed.refinement.count) → (p : P) → (x : D) →
      normalSpace (I := IM) (F p) (c l s p x) := fun l s (_ : P) x => actualRescaledNormal F0 hF0 scale
        (GeneralLegalWaveSeed.contraction_ne_zero scale hscale) ((family.piece l).seed.coordinate s 0 x)
        ((waves l).normal ((family.piece l).seed.coordinate s 0 x))
    let a : (l : Fin r) → Fin (family.piece l).seed.refinement.count → OpenPartialHomeomorph (P × M) (P × D) :=
      fun l s => passiveParameterChart (P := P) (0 : Z) ((family.piece l).seed.physicalChart s)
    let phase := fun l (z : P × M) => weight l*(waves l).phase z.2
    let vf : (l : Fin r) → (s : Fin (family.piece l).seed.refinement.count) → (p : P) → (x : D) →
      normalSpace (I := IM) (F p) (c l s p x) := fun l s p x =>
      (-(delta*tau)/(weight l)^2) • (chi l s (p,x) • nu l s p x)
    let meanProbe := fun p x => jointGroupedParameterPrescribedMean (I := IM) label F hF c vf phase
      tau 442 a (u p) p x
    let background := fun i => actualParameterBackgroundMeanIterate F hF g 442
      tau delta target (fun (_ : Fin 0 → ℝ) => meanProbe) i 0
    let U := actualProbeInitialGroupedIncrement F hF g label c vf phase tau delta
      442 442 442 a (background 441) u (jointSecondarySeedPaddedChoice seeds)
      (jointSecondarySeedPaddedChoice_preserves seeds)
    let secondary := actualParameterSecondarySourceSum F hF
      (actualProbeInitialGroupedSource F hF g label c vf phase tau delta
        442 442 a (background 441) u (jointSecondarySeedPaddedChoice seeds)
        (jointSecondarySeedPaddedChoice_preserves seeds)) tau 442
    ∃ htau1 : tau < 1,
    ∃ initial : Round3RepairClosedState packet plan.budget plan.epsilon plan.eta 10 tau,
      initial.map = actualRepairModelFirstDefectFirstMap packet.referenceMap U delta ∧
      actualProbeInitialSecondaryBallBounds seed.atlas seed.sourceNormDomain Initialized CS t secondary ∧
      (paperAtlasWeighted 2 440 tau (incrementsOriginalMapCoordinates seed.atlas B.chart U)
        (incrementsOriginalDifferentiation seed.atlas B.chart) Samples ≠ ⊤ ∧
        (paperAtlasWeighted 2 440 tau (incrementsOriginalMapCoordinates seed.atlas B.chart U)
          (incrementsOriginalDifferentiation seed.atlas B.chart) Samples).toReal ≤ CU*delta/tau) ∧
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates seed.atlas B.chart U)
        (incrementsOriginalDifferentiation seed.atlas B.chart) Samples ≠ ⊤ ∧
        (paperAtlasCj 2 (incrementsOriginalMapCoordinates seed.atlas B.chart U)
          (incrementsOriginalDifferentiation seed.atlas B.chart) Samples).toReal ≤ CU*delta/tau) ∧
      Nonempty (Round3RepairInfiniteBlocks (Tr := ℝ) (Λ := Fin Data.primaryCount)
        (Β := ΒRepair) (SubSecondary := SubRepair) packet plan.cost plan.Cs plan.sigma
        plan.budget plan.epsilon plan.eta tau (Real.rpow_pos_of_pos ht _) htau1 initial)

/-- The real tail plan removes the remaining repair-run supply premise;
the selected first map and every retained response witness are unchanged. -/
theorem generalReference_selected_initial_tail
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (waves : Fin r → OpenSupportedLegalWave F0 hF0)
    (s : OriginalReferenceSupply (m := m) (N := N) F0)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,Ep) ∞ (B.chart i))
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (BP TP : ℕ → ℝ) (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (selected : ProbesSelectedGeneralInitializedSecondaryStatement
      (BS := s.fixedClass.numerical.BS) (TS := s.fixedClass.numerical.TS)
      (BP := BP) (TP := TP) (Ds := s.fixedClass.numerical.Ds)
      s.seed s.domain s.smooth s.phase s.freeNormal s.immersion s.parameterSet_eq
      s.baseIndex s.parameter_identity s.refinementMultiplicity s.primary
      s.fixedClass.lower s.fixedClass.numerical.reserve
      s.ellipticity s.linearSmooth s.decomposition s.reserve
      B hB hforward Q hQ hQT hF0 waves b p₀ hp₀) :
    GeneralSelectedTailStatement F0 hF0 waves s B Q BP TP b p₀ := by
  unfold GeneralSelectedTailStatement
  intro seed Data g0 gp K
  obtain ⟨weight,hweight,hInjective,family,O,seeds,rho,hrho,Tp,Pphase,hTp,
    hSamples,numbers,hRho,hPrimary,hPrescribed,hPacket⟩ := selected
  refine ⟨weight,hweight,hInjective,family,O,seeds,rho,hrho,Tp,Pphase,hTp,
    hSamples,numbers,hRho,hPrimary,hPrescribed,?_⟩
  intro Mgp Bchi Bnu Mphase Csrc amplitude Initialized u
  obtain ⟨radius,hradius,packet,hFamily,hReference,hOmega,hParameter,hMetric,hLocal,
    CU,CS,hCU,hCS,hSecondaryNonneg,hSecondaryLimit,hInitial⟩ := hPacket
  refine ⟨radius,hradius,packet,hFamily,hReference,hOmega,hParameter,hMetric,hLocal,
    CU,CS,hCU,hCS,hSecondaryNonneg,hSecondaryLimit,?_⟩
  obtain ⟨ΒRepair,SubRepair,iΒRepair,iSubRepair,plan,hTolerance⟩ :=
    originalReference_exists_tail_plan F0 s B Q BP TP hBP hTP Initialized.supportDegree
      radius hradius (passiveOriginalPhysicalReferenceBudget Data)
      (passiveOriginalPhysicalFixedBudget Data) packet hReference hOmega hParameter 1 (by norm_num)
  letI := iΒRepair
  letI := iSubRepair
  obtain ⟨t0,ht0,ht0Half,ht0Cap,hAt⟩ :=
    hInitial plan.epsilon plan.eta (plan.sigma 0) plan.epsilon_pos plan.eta_pos
      (plan.sigma_pos 0) plan.budget plan.reference_budget
  refine ⟨ΒRepair,SubRepair,iΒRepair,iSubRepair,plan,t0,ht0,ht0Half,ht0Cap,?_⟩
  intro t ht htt label tau ell delta scale hscale F hF g target c chi nu a phase vf
    meanProbe background U secondary
  obtain ⟨initial,hmap,hSecondary,hWeighted,hTwo⟩ := hAt t ht htt label
  have ht1 : t ≤ 1 := (htt.trans ht0Half).trans (by norm_num)
  have htauT : tau ≤ t := Real.rpow_le_self_of_le_one ht.le ht1 (by norm_num)
  have htau1 : tau < 1 := htauT.trans_lt ((htt.trans ht0Half).trans_lt (by norm_num))
  refine ⟨htau1,initial,hmap,hSecondary,hWeighted,hTwo,?_⟩
  exact plan.restart tau (Real.rpow_pos_of_pos ht _) htau1
    (htauT.trans (htt.trans ht0Cap)) initial

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.GeneralSelectedTailStatement
#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.generalReference_selected_initial_tail
