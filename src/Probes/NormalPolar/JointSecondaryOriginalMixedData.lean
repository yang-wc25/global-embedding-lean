import NormalPolar.JointSecondaryOriginalPrimaryCarrier
import NormalPolar.JointSecondaryOriginalPhaseWeights

/-! The actual original background and the original legal waves form one
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
  (waves : Fin r → LocalLegalWave (n := m+1) (fun x => Data.F (p,x))
    (incrementsOriginal_slice_contMDiff Data hd hs p hpO))

def jointSecondaryOriginalMixedCarrier : (Fin Data.primaryCount ⊕ Fin r) → Set M :=
  Sum.elim (jointSecondaryOriginalPrimaryCarrier Data p) (fun l => tsupport ((waves l).cutoff : M → ℝ))

def jointSecondaryOriginalMixedDomain : (Fin Data.primaryCount ⊕ Fin r) → Set M :=
  Sum.elim (jointSecondaryOriginalPrimaryDomain Data p) (fun l => (waves l).domain)

def jointSecondaryOriginalMixedUnweightedPhase : (Fin Data.primaryCount ⊕ Fin r) → M → ℝ :=
  Sum.elim (fun l x => Data.phase l (p,x)) (fun l => (waves l).phase)

def jointSecondaryOriginalMixedPhase (A : ℝ) : (Fin Data.primaryCount ⊕ Fin r) → M → ℝ :=
  Sum.elim (fun l x => Data.phase l (p,x)) (fun l x => A^(l.val+1) * (waves l).phase x)

def jointSecondaryOriginalMixedExponent : (Fin Data.primaryCount ⊕ Fin r) → ℕ :=
  Sum.elim (fun _ => 0) (fun l => l.val+1)

theorem jointSecondaryOriginalMixedCarrier_closed (l : Fin Data.primaryCount ⊕ Fin r) :
    IsClosed (jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves l) := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryCarrier_closed Data hd p hpO l
  | inr l => exact isClosed_tsupport _

theorem jointSecondaryOriginalMixedDomain_open (l : Fin Data.primaryCount ⊕ Fin r) :
    IsOpen (jointSecondaryOriginalMixedDomain Data hd hs p hpO waves l) := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryDomain_open Data hd p l
  | inr l => exact (waves l).domain_open

theorem jointSecondaryOriginalMixedCarrier_domain (l : Fin Data.primaryCount ⊕ Fin r) :
    jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves l ⊆
      jointSecondaryOriginalMixedDomain Data hd hs p hpO waves l := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryCarrier_domain Data hd p l
  | inr l => exact (waves l).support_subset

theorem jointSecondaryOriginalMixedUnweightedPhase_smooth (l : Fin Data.primaryCount ⊕ Fin r) :
    ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ (jointSecondaryOriginalMixedUnweightedPhase Data hd hs p hpO waves l)
      (jointSecondaryOriginalMixedDomain Data hd hs p hpO waves l) := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryPhase_smooth Data hs p hpO l
  | inr l => exact (waves l).phase_smooth

theorem jointSecondaryOriginalMixedPhase_smooth (A : ℝ) (l : Fin Data.primaryCount ⊕ Fin r) :
    ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ (jointSecondaryOriginalMixedPhase Data hd hs p hpO waves A l)
      (jointSecondaryOriginalMixedDomain Data hd hs p hpO waves l) := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryPhase_smooth Data hs p hpO l
  | inr l => exact contMDiffOn_const.mul ((waves l).phase_smooth)

theorem jointSecondaryOriginalMixedUnweightedPhase_good
    (hp : IncrementsOriginalPhaseConditions Data hd hs) (l : Fin Data.primaryCount ⊕ Fin r)
    (x : M) (hx : x ∈ jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves l) :
    GoodCovector (fun y => Data.F (p,y)) (incrementsOriginal_slice_contMDiff Data hd hs p hpO) x
      (mfderiv IM 𝓘(ℝ,ℝ) (jointSecondaryOriginalMixedUnweightedPhase Data hd hs p hpO waves l) x) := by
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryPhase_good Data hd hs hp p hpO l x hx
  | inr l => exact ((waves l).legal x ((waves l).support_subset hx)).1

theorem jointSecondaryOriginalMixedPhase_covector (A : ℝ)
    (l : Fin Data.primaryCount ⊕ Fin r) (x : M)
    (hx : x ∈ jointSecondaryOriginalMixedDomain Data hd hs p hpO waves l) :
    jointSecondaryPhaseCovector (m := m) (jointSecondaryOriginalMixedPhase Data hd hs p hpO waves A l) x =
      A^(jointSecondaryOriginalMixedExponent (r := r) Data l) •
        jointSecondaryPhaseCovector (m := m)
          (jointSecondaryOriginalMixedUnweightedPhase Data hd hs p hpO waves l) x := by
  cases l with
  | inl l => simp only [jointSecondaryOriginalMixedPhase,jointSecondaryOriginalMixedExponent,
      jointSecondaryOriginalMixedUnweightedPhase,Sum.elim_inl,pow_zero,one_smul]
  | inr l =>
    exact jointSecondaryPhaseCovector_const_mul (waves l).phase x
      (((waves l).phase_smooth.contMDiffAt ((waves l).domain_open.mem_nhds hx)).mdifferentiableAt (by simp))
      (A^(l.val+1))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondaryOriginalMixedUnweightedPhase_good
#print axioms GlobalEmbedding.Continuation.jointSecondaryOriginalMixedPhase_covector
