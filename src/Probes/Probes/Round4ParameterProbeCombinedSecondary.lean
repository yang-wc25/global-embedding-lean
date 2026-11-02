import Probes.Round4ParameterProbeCombinedPrimary

/-! The combined actual background/probe primary array is consumed by the
original constructed-secondary metric identity. Every ordered mixed label
pair and every signed branch is retained. No estimate for the complete metric
error, no normalized defect budget, and no repaired state are assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N p r : ℕ} {Ep M Λ Β : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

variable
    (F : Ep → M → EuclideanSpace ℝ (Fin N))
    (hF : ∀ b, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
      (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → EuclideanSpace ℝ (Fin (m+1)) → M)
    (vf : (l : Fin r) → (b : Ep) → (x : EuclideanSpace ℝ (Fin (m+1))) →
      normalSpace (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × EuclideanSpace ℝ (Fin (m+1))))

omit [NormedSpace ℝ Ep] [DecidableEq Λ] in
/-- The observed common array is literally the same physical global primary
wave. Unit subordinate labels do not remove the true background subordinate
cross terms: they have already been grouped by their common primary phase. -/
theorem round4ParameterProbe_observed_primary_wave
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (u : Fin p → ℝ) (kappa : X → Ep × M) :
    let phi := fun l b x => Sum.elim g.phase phase l (kappa (b,x))
    let R := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false
    let Q := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true
    actualPrimaryJointWave phi tau (fun (_ : Λ ⊕ Fin r) _ (_ : Unit) _ => 1)
      (fun l b _ x => R l (kappa (b,x))) (fun l b _ x => Q l (kappa (b,x))) =
      round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input u ∘ kappa := by
  intro phi R Q
  funext z
  simp only [actualPrimaryJointWave,incrementsPrimaryWave,Finset.univ_unique,
    Finset.sum_singleton,one_smul]
  change (∑ l : Λ ⊕ Fin r, _) = ∑ l : Λ ⊕ Fin r, _
  apply Finset.sum_congr rfl
  intro l _
  exact congrFun (increments_primary_real_mode_eq (fun x => phi l z.1 x) tau
    (fun x => R l (kappa (z.1,x))) (fun x => Q l (kappa (z.1,x)))) z.2

/-- Every actual background/probe interaction belongs to the full secondary
record set in both orders and all four signed branches. No phase cancellation
is silently classified as an opposite-primary mean contribution. -/
theorem round4ParameterProbe_mixed_secondary_records (nu : Λ) (l : Fin r) (q : Fin 4) :
    ((Sum.inl nu,Sum.inr l),q) ∈ actualSecondaryNonzeroRecords (Λ ⊕ Fin r) ∧
    ((Sum.inr l,Sum.inl nu),q) ∈ actualSecondaryNonzeroRecords (Λ ⊕ Fin r) := by
  simp [actualSecondaryNonzeroRecords]

variable {SubSecondary : Type*} [Fintype SubSecondary]

/-- The existing actual secondary solver now acts on the common physical
background/probe coefficient array. Its complete metric error contains the
literal linear residual, all constructed secondary forcing, the actual
cross/self metric term, and the selected mean defect of that same array. -/
theorem round4ParameterProbe_actual_complete_metric_identity
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (u : Fin p → ℝ) (b : OpenPartialHomeomorph (Ep × M) X) :
    let phi := fun l t x => Sum.elim g.phase phase l (b.symm (t,x))
    let R := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false
    let Q := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true
    let cut := fun (_ : Λ ⊕ Fin r) (_ : Ep) (_ : Unit) (_ : D) => (1 : ℝ)
    let PR := fun l t (_ : Unit) x => R l (b.symm (t,x))
    let PQ := fun l t (_ : Unit) x => Q l (b.symm (t,x))
    ∀ (n j length : ℕ) (ell Mg CH : ℝ) (W : Set (Ep × M))
      (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
        ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W),
    (∀ rec : ActualSecondarySignedRecord (Λ ⊕ Fin r),
      let forcing := incrementsSecondaryQuadraticForcing phi tau cut PR PQ
        (fun i _ => EuclideanSpace.single i 1) rec.1.1.1 rec.1.1.2 rec.1.2
      ActualSecondaryForcingBinding F hF (fun s => (data rec s).base) b
        (fun z => actualRealTensorAssembly (forcing z)) (fun z => actualImaginaryTensorAssembly (forcing z))
        (incrementsSecondaryQuadraticPhase phi rec.1.1.1 rec.1.1.2 rec.1.2)) →
    ∀ (H : X → Tensor) (_hW : IsOpen W) (Omega : Set X) (_hOmega : IsOpen Omega),
    Omega ⊆ b.target → ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ b.symm Omega →
    MapsTo b.symm Omega W →
    ∀ z ∈ Omega,
    DifferentiableAt ℝ (fun x => F (b.symm (z.1,x)).1 (b.symm (z.1,x)).2) z.2 →
    (∀ l, DifferentiableAt ℝ (phi l z.1) z.2) →
    (∀ l, DifferentiableAt ℝ (PR l z.1 ()) z.2) →
    (∀ l, DifferentiableAt ℝ (PQ l z.1 ()) z.2) →
    let Fobs := fun y : X => F (b.symm y).1 (b.symm y).2
    let U1 := round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input u ∘ b.symm
    let U2 := actualConstructedSecondarySum F hF (fun rec s => (data rec s).base) tau length ∘ b.symm
    actualFiniteMetricError Fobs (fun y => U1 y+U2 y) H delta z =
      actualJointMetricLinearization Fobs U1 z +
      actualConstructedSecondaryPhysicalSum F hF data b.symm tau length z +
      (actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x)+U2 (z.1,x)) z.2) -
        actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x)) z.2)) +
      (actualPrimaryOppositeMeanTensor phi tau cut PR PQ z-delta^2 • H z) := by
  intro phi R Q cut PR PQ n j length ell Mg CH W data binding H hW Omega hOmega hOmegaB hb hmap
    z hz hFobs hphi hPR hPQ Fobs U1 U2
  have h := actual_constructed_complete_metric_identity F hF data b phi tau length cut PR PQ
    binding H hW Omega hOmega hOmegaB hb hmap z hz hFobs hphi
    (fun _ _ => differentiableAt_const 1) (fun l _ => hPR l) (fun l _ => hPQ l)
  have hw := round4ParameterProbe_observed_primary_wave F hF g label c vf phase tau delta
    backgroundLength probeLength a input u b.symm
  change actualPrimaryJointWave phi tau cut PR PQ = U1 at hw
  change actualFiniteMetricError Fobs (fun y => actualPrimaryJointWave phi tau cut PR PQ y+U2 y) H delta z = _ at h
  rw [hw] at h
  exact h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_observed_primary_wave
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_mixed_secondary_records
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_actual_complete_metric_identity
