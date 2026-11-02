import UpgradeContinuation.OriginalReferenceSupply
import UpgradeContinuation.FixedReferenceTailPlan
import NormalPolar.PassiveOriginalSmooth
import NormalPolar.PassiveOriginalLinear
import NormalPolar.PassiveOriginalGeometry

/-!
# The selected original reference supplies its probe repair plan

The actual original F seed transports its smoothness, phase, free normal,
ellipticity, linear decomposition and reserve to the parameter family of
the selected physical packet.  The complete restart plan is manufactured
on that same packet.  In particular its epsilon, eta and first cap can be
fed back to the strengthened selected-initial-state constructor, whose
packet and whole wave family have already been fixed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold Bundle GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal Classical

namespace GlobalEmbedding.Continuation.UpgradeContinuation

universe uM uP
variable {m d N : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => ZeroParameter
local notation "IM" => 𝓘(ℝ,D)

private local instance signedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

/-- The phase and reserve inputs of the same passive packet follow from
the original reference supply.  All finite types and every future raw
increment are produced inside the conclusion. -/
theorem originalReference_exists_tail_plan
    (F : M → V) (s : OriginalReferenceSupply (m := m) (N := N) F)
    (B : BufferedAtlas P Ep) (Q : Fin B.count → Set Ep)
    (BP TP : ℕ → ℝ) (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j)
    (Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (reference Given : ℕ → ℝ)
    (packet : Round3RepairFixedSmoothingPacket (passiveOriginalData (0 : Z) s.seed B Q)
      s.fixedClass.numerical.BS s.fixedClass.numerical.TS BP TP
      s.fixedClass.numerical.Ds Dp radius hradius reference Given)
    (hReference : packet.referenceMap = fun z => F z.2)
    (hSource : packet.Omega = s.seed.sourceNormDomain) (hParameter : packet.Q = Q)
    (tolerance : ℝ) (hTolerance : 0 < tolerance) :
    ∃ (Β Sub : Type) (iΒ : Fintype Β) (iSub : Fintype Sub),
    ∃ plan : ActualProbeProducedRepairPlan packet Β Sub, plan.epsilon ≤ tolerance := by
  let Data := passiveOriginalData (0 : Z) s.seed B Q
  have hseed : (0 : Z) ∈ s.seed.parameterSet := by rw [s.parameterSet_eq]; trivial
  have hzero : (0 : Z) ∈ s.seed.parameterOpen := s.domain.parameter_subset hseed
  have hb0 : (0 : Z) ∈ (s.seed.parameterChart s.baseIndex.2).target := by
    rw [s.parameter_identity]
    trivial
  let hs := passiveOriginalData_smooth (0 : Z) s.seed s.smooth hzero s.baseIndex.2 hb0 B Q
  let hp := passiveOriginalData_phaseConditions (0 : Z) s.seed s.domain s.smooth s.phase
    hzero B Q packet.domain hs
  let hn := passiveOriginalData_freeNormalConditions (0 : Z) s.seed s.domain s.smooth s.freeNormal
    hzero B Q packet.domain hs
  let hDecomp := passiveOriginalData_decomposition (0 : Z) s.seed B Q s.decomposition hzero
  let hLinear := passiveOriginalData_linearSmooth (0 : Z) s.seed B Q s.baseIndex.2
    s.linearSmooth hzero hb0
  let hImm := passiveOriginalData_immersion (0 : Z) s.seed B Q s.immersion hzero
  let hEll := passiveOriginalData_ellipticity (0 : Z) s.seed B Q s.fixedClass.lower
    s.ellipticity hseed
  let hReserve := passiveOriginalData_reserve (0 : Z) s.seed B Q s.fixedClass.numerical.reserve
    s.reserve hzero hseed
  have hRef : Data.F = packet.referenceMap := hReference.symm
  have hNormSource : Data.sourceNormDomain = packet.Omega := hSource.symm
  have hNormParameter : Data.parameterNormDomain = packet.Q := hParameter.symm
  obtain ⟨primary,secondary,plan,hEpsilon⟩ := probes_exists_fixed_reference_tail_plan Data
    s.fixedClass.numerical.BS s.fixedClass.numerical.TS BP TP
    s.fixedClass.numerical.BS_nonneg s.fixedClass.numerical.TS_nonneg hBP hTP
    s.fixedClass.numerical.Ds Dp radius hradius reference Given packet hRef hNormSource hNormParameter
    rfl hs hp hn hDecomp hLinear hImm s.fixedClass.lower hEll s.fixedClass.numerical.reserve hReserve
    tolerance hTolerance
  exact ⟨_,_,inferInstance,inferInstance,plan,hEpsilon⟩

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.originalReference_exists_tail_plan
