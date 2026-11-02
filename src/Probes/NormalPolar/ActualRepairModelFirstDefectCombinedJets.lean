import Probes.ActualSecondaryThreeTermMetricJets
import Probes.Round4ParameterProbeCombinedSecondary

/-!
# The actual combined background/probe three-term metric error

The primary is the literal combined background plus prescribed probe array.
The secondary is built from all signed records of the same disjoint-label
array, including both orders of every mixed background/probe pair. The
secondary and cross/self budgets are derived from actual physical piece
data; no bound for the total metric error or normalized defect is an input.
The separate genuine primary wave and linear-residual profiles remain explicit.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Manifold Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N p r : ℕ} {Ep M Λ Β SubSecondary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

private local instance completeTensorSemi : SeminormedAddCommGroup Tensor :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance completeTensorNormed : NormedAddCommGroup Tensor :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance completeTensorSpace : NormedSpace ℝ Tensor :=
  ContinuousLinearMap.toNormedSpace
private local instance completePartialSemi : SeminormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] Tensor) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance completePartialNormed : NormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] Tensor) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance completePartialSpace : NormedSpace ℝ ((D →L[ℝ] V) →L[ℝ] Tensor) :=
  ContinuousLinearMap.toNormedSpace

theorem actualRepairModelFirstDefect_combined_remainder_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := 𝓙) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ)
    (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (u : Fin p → ℝ)
    (n j q length : ℕ) (ell Mg CH delta tau : ℝ) (W : Set (Ep × M))
    (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n (j+1) ell Mg CH delta W)
    (hbudget : j+2+length ≤ n) (hql : q ≤ length)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau) (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) (hW : IsOpen W)
    (b : OpenPartialHomeomorph (Ep × M) X)
    :
    let phi := fun l t x => Sum.elim g.phase phase l (b.symm (t,x))
    let R0 := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false
    let Q0 := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true
    let chi := fun (_ : Λ ⊕ Fin r) (_ : Ep) (_ : Unit) (_ : D) => (1 : ℝ)
    let P := fun l t (_ : Unit) x => R0 l (b.symm (t,x))
    let Q := fun l t (_ : Unit) x => Q0 l (b.symm (t,x))
    ∀    (binding : ∀ r : ActualSecondarySignedRecord (Λ ⊕ Fin r),
      let H := incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) r.1.1.1 r.1.1.2 r.1.2
      ActualSecondaryForcingBinding F hF (fun a => (data r a).base) b
        (fun z => actualRealTensorAssembly (H z)) (fun z => actualImaginaryTensorAssembly (H z))
        (incrementsSecondaryQuadraticPhase phi r.1.1.1 r.1.1.2 r.1.2))
    (H : X → Tensor) (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (hprimary : ∀ r a, (data r a).base.support ⊆ K r.val.1.1 ∩ K r.val.1.2)
    (Omega S : Set X) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega) (hOmegaB : Omega ⊆ b.target)
    (hb : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ b.symm Omega)
    (hmap : MapsTo b.symm Omega W) (hfirst : ∀ z ∈ Omega, (b.symm z).1 = z.1)
    (O : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary → Set X)
    (hO : ∀ r a, IsOpen (O r a)) (hOOmega : ∀ r a, O r a ⊆ Omega)
    (hactiveO : ∀ r a, S ∩ b.symm ⁻¹' (data r a).base.support ⊆ O r a)
    (hsource : ∀ r a, MapsTo b.symm (O r a) (data r a).base.chart.source)
    (htransition : ∀ r a, ContDiffOn ℝ ∞ ((data r a).base.chart ∘ b.symm) (O r a))
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i)
    (hsample : ∀ r a z, z ∈ S ∩ b.symm ⁻¹' (data r a).base.support →
      (data r a).base.chart (b.symm z) ∈ (data r a).base.sample)
    (htransitionb : ∀ r a z, z ∈ S ∩ b.symm ⁻¹' (data r a).base.support →
      ∀ i, 1 ≤ i → i ≤ j+2 →
        ell^(i-1)*‖iteratedFDeriv ℝ i ((data r a).base.chart ∘ b.symm) z‖ ≤ T i)
    (L R : ℕ)
    (hL : ∀ z ∈ S, (Finset.univ.filter (fun nu => b.symm z ∈ K nu)).card ≤ L)
    (hR : ∀ r : ActualSecondarySignedRecord (Λ ⊕ Fin r), ∀ z ∈ S,
      (Finset.univ.filter (fun a => b.symm z ∈ (data r a).base.support)).card ≤ R)
    (M1 CP : ℝ) (hM1 : 0 ≤ M1) (hCP : 0 ≤ CP),
    let Fobs := fun z : X => F (b.symm z).1 (b.symm z).2
    let U1 := round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input u ∘ b.symm
    let U2 := actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau length ∘ b.symm
    let Mean := fun z => actualPrimaryOppositeMeanTensor phi tau chi P Q z - delta^2 • H z
    ContDiffOn ℝ ∞ Fobs Omega → ContDiffOn ℝ ∞ U1 Omega → ContDiffOn ℝ ∞ H Omega →
    ContDiffOn ℝ ∞ (actualJointMetricLinearization Fobs U1) Omega → ContDiffOn ℝ ∞ Mean Omega →
    (∀ z ∈ Omega, ∀ i, fderiv ℝ (fun x => U1 (z.1,x)) z.2 (EuclideanSpace.single i 1) =
      incrementsGroupedRealDerivative (fun nu => phi nu z.1 z.2 / tau)
        (incrementsSecondaryPhysicalCoefficient phi tau chi P Q
          (fun r _ => EuclideanSpace.single r 1) z) i) →
    (∀ r ≤ j+1, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r U1 z‖ ≤ M1*delta*tau) →
    (∀ r ≤ j, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r (actualJointMetricLinearization Fobs U1) z‖ ≤
      CP*delta*tau*(tau/ell)^length) →
    ContDiffOn ℝ ∞ (fun z => actualFiniteMetricError Fobs (fun w => U1 w+U2 w) H delta z - Mean z) Omega ∧
      ∀ r ≤ j, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r
        (fun z => actualFiniteMetricError Fobs (fun w => U1 w+U2 w) H delta z - Mean z) z‖ ≤
        actualConstructedFiniteErrorCost m N n j length L R Mg CH M1 CP 0 T *
          (delta*(tau/ell)^q+delta^3/tau) := by
  intro phi R0 Q0 chi P Q binding H K hprimary Omega S hOmega hSOmega hOmegaB hb hmap hfirst
    O hO hOOmega hactiveO hsource htransition T hT hsample htransitionb L R hL hR M1 CP hM1 hCP
    Fobs U1 U2 Mean hFobs hU1 hH hlin hMean hgrouped hU1jet hlinjet
  have hw := round4ParameterProbe_observed_primary_wave F hF g label c vf phase tau delta
    backgroundLength probeLength a input u b.symm
  change actualPrimaryJointWave phi tau chi P Q = U1 at hw
  have h := actual_constructed_metric_error_without_mean_jets F hF n j q length ell Mg CH delta tau W
    data hbudget hql hell hell1 htau htaul hdelta hdeltatau hMg hCH hW b phi chi P Q binding H K hprimary
    Omega S hOmega hSOmega hOmegaB hb hmap hfirst O hO hOOmega hactiveO hsource htransition T hT
    hsample htransitionb L R hL hR M1 CP hM1 hCP
  dsimp only at h
  rw [hw] at h
  exact h hFobs hU1 hH hlin hMean hgrouped hU1jet hlinjet

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_combined_remainder_jets
