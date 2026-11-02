import Main.GeneralLegalWaveRefinement
import NormalPolar.JointSecondaryOriginalPrimaryCarrier
import NormalPolar.JointSecondaryOriginalPhaseWeights

/-!
Source: the frozen JointSecondaryOriginalMixedData orchestration, generalized only at
the arbitrary smooth cutoff input. Generic compact phase weights, native
differentials and actual signed-seed geometry are reused unchanged.
 The actual original background and the original legal waves form one
finite label family. Prescribed weights act only on the original phase;
the labels, normal values, cutoff carriers and smoothness domains stay fixed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade
open Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N r : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
variable (Data : IncrementsOriginalNativeData (m+1) d N M P)
  (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
  (p : P) (hpO : p ∈ Data.parameterOpen)
  (waves : Fin r → OpenSupportedLegalWave (n := m+1) (fun x => Data.F (p,x))
    (incrementsOriginal_slice_contMDiff Data hd hs p hpO))

def jointSecondaryGeneralMixedCarrier : (Fin Data.primaryCount ⊕ Fin r) → Set M :=
  Sum.elim (jointSecondaryOriginalPrimaryCarrier Data p) (fun l => tsupport ((waves l).cutoff : M → ℝ))

def jointSecondaryGeneralMixedDomain : (Fin Data.primaryCount ⊕ Fin r) → Set M :=
  Sum.elim (jointSecondaryOriginalPrimaryDomain Data p) (fun l => (waves l).domain)

def jointSecondaryGeneralMixedUnweightedPhase : (Fin Data.primaryCount ⊕ Fin r) → M → ℝ :=
  Sum.elim (fun l x => Data.phase l (p,x)) (fun l => (waves l).phase)

def jointSecondaryGeneralMixedPhase (A : ℝ) : (Fin Data.primaryCount ⊕ Fin r) → M → ℝ :=
  Sum.elim (fun l x => Data.phase l (p,x)) (fun l x => A^(l.val+1) * (waves l).phase x)

def jointSecondaryGeneralMixedExponent : (Fin Data.primaryCount ⊕ Fin r) → ℕ :=
  Sum.elim (fun _ => 0) (fun l => l.val+1)

theorem jointSecondaryGeneralMixedCarrier_closed (l : Fin Data.primaryCount ⊕ Fin r) :
    IsClosed (jointSecondaryGeneralMixedCarrier Data hd hs p hpO waves l) := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryCarrier_closed Data hd p hpO l
  | inr l => exact isClosed_tsupport _

theorem jointSecondaryGeneralMixedDomain_open (l : Fin Data.primaryCount ⊕ Fin r) :
    IsOpen (jointSecondaryGeneralMixedDomain Data hd hs p hpO waves l) := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryDomain_open Data hd p l
  | inr l => exact (waves l).domain_open

theorem jointSecondaryGeneralMixedCarrier_domain (l : Fin Data.primaryCount ⊕ Fin r) :
    jointSecondaryGeneralMixedCarrier Data hd hs p hpO waves l ⊆
      jointSecondaryGeneralMixedDomain Data hd hs p hpO waves l := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryCarrier_domain Data hd p l
  | inr l => exact (waves l).support_subset

theorem jointSecondaryGeneralMixedUnweightedPhase_smooth (l : Fin Data.primaryCount ⊕ Fin r) :
    ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ (jointSecondaryGeneralMixedUnweightedPhase Data hd hs p hpO waves l)
      (jointSecondaryGeneralMixedDomain Data hd hs p hpO waves l) := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryPhase_smooth Data hs p hpO l
  | inr l => exact (waves l).phase_smooth

theorem jointSecondaryGeneralMixedPhase_smooth (A : ℝ) (l : Fin Data.primaryCount ⊕ Fin r) :
    ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ (jointSecondaryGeneralMixedPhase Data hd hs p hpO waves A l)
      (jointSecondaryGeneralMixedDomain Data hd hs p hpO waves l) := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryPhase_smooth Data hs p hpO l
  | inr l => exact contMDiffOn_const.mul ((waves l).phase_smooth)

theorem jointSecondaryGeneralMixedUnweightedPhase_good
    (hp : IncrementsOriginalPhaseConditions Data hd hs) (l : Fin Data.primaryCount ⊕ Fin r)
    (x : M) (hx : x ∈ jointSecondaryGeneralMixedCarrier Data hd hs p hpO waves l) :
    GoodCovector (fun y => Data.F (p,y)) (incrementsOriginal_slice_contMDiff Data hd hs p hpO) x
      (mfderiv IM 𝓘(ℝ,ℝ) (jointSecondaryGeneralMixedUnweightedPhase Data hd hs p hpO waves l) x) := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryPhase_good Data hd hs hp p hpO l x hx
  | inr l => exact ((waves l).legal x ((waves l).support_subset hx)).1

theorem jointSecondaryGeneralMixedPhase_covector (A : ℝ)
    (l : Fin Data.primaryCount ⊕ Fin r) (x : M)
    (hx : x ∈ jointSecondaryGeneralMixedDomain Data hd hs p hpO waves l) :
    jointSecondaryPhaseCovector (m := m) (jointSecondaryGeneralMixedPhase Data hd hs p hpO waves A l) x =
      A^(jointSecondaryGeneralMixedExponent (r := r) Data l) •
        jointSecondaryPhaseCovector (m := m)
          (jointSecondaryGeneralMixedUnweightedPhase Data hd hs p hpO waves l) x := by
  cases l with
  | inl l => simp only [jointSecondaryGeneralMixedPhase,jointSecondaryGeneralMixedExponent,
      jointSecondaryGeneralMixedUnweightedPhase,Sum.elim_inl,pow_zero,one_smul]
  | inr l =>
    exact jointSecondaryPhaseCovector_const_mul (waves l).phase x
      (((waves l).phase_smooth.contMDiffAt ((waves l).domain_open.mem_nhds hx)).mdifferentiableAt (by simp))
      (A^(l.val+1))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondaryGeneralMixedUnweightedPhase_good
#print axioms GlobalEmbedding.Continuation.jointSecondaryGeneralMixedPhase_covector
