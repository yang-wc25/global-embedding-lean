import NormalPolar.GlobalWaveResponseAtlas
import NormalPolar.OriginalWaveSeedSupportedValue
import NormalPolar.OriginalProbeScales

/-!
# Original legal-wave Hessian response on the literal paper scales

The actual cutoff gives the carrier and its vanishing complement. The
principal phase and value are those of the very same LocalLegalWave, and
ell=t^(11/10) is used in every primitive weighted-jet hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
  GlobalEmbedding.Continuation
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade
variable {n m N p r : ℕ} {M Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "IM" => 𝓘(ℝ,E)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private noncomputable local instance originalHessianSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance originalHessianNorm :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance originalHessianSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

theorem exists_uniform_globalWave_supported_paper_response
    (theta : Fin r → M → ℝ) (amplitude : Fin r → M → V)
    (carrier : Fin r → Set M) (hclosed : ∀ l, IsClosed (carrier l))
    (hamplitudeZero : ∀ l x, x ∉ carrier l → amplitude l x = 0)
    (atlas : BufferedAtlas M E) (hAtlas : IsSmoothBufferedAtlas atlas)
    (hcompact : ∀ j, IsCompact (atlas.support j))
    (source : Fin r → OpenPartialHomeomorph M D)
    (hsource : ∀ l, ContMDiffOn IM 𝓘(ℝ,D) ∞ (source l) (source l).source)
    (hcarrier : ∀ l, carrier l ⊆ (source l).source) :
    ∃ B1 B2 : ℝ, 0 < B1 ∧ 0 < B2 ∧ ∀
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := IM) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,ℝ) ∞ (phase l) (W ∩ (a l).source))
    (i : Fin r) (b : Ep) (chi : X → ℝ)
    (nu : (t : Ep) → (y : D) → normalSpace (I := IM) (F t) (c i t y))
    (weight : ℝ) (psi : D → ℝ)
    (hphysical : vf i = actualProbeNormalAmplitude F (c i) chi nu (t ^ (10 : ℕ)) (t ^ ((6 : ℝ) / 5)) weight)
    (hinverse : ∀ z ∈ (a i).target, (a i).symm z = (z.1,c i z.1 z.2))
    (hsourceW : (a i).source ⊆ W)
    (hobs : ContMDiffOn 𝓘(ℝ,D) IM ∞ (c i b) ((fun y : D => (b,y)) ⁻¹' (a i).target))
    (hphaseChart : ∀ y, (b,y) ∈ (a i).target → phase i ((a i).symm (b,y)) = weight*psi y)
    (hpsi : ContDiffOn ℝ ∞ psi ((fun y : D => (b,y)) ⁻¹' (a i).target))
    (hchi : ContDiffOn ℝ ∞ chi (a i).target)
    (hnu : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) (a i).target)
    (S : Set D) (hS : ∀ y ∈ S, (b,y) ∈ (a i).target)
    (MB Mg Bchi Bnu Mpsi : ℝ)
    (hweight : 0 < weight)
    (hMB : 0 ≤ MB) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hBRb : ∀ k ≤ 2+length+1, ∀ z ∈ (a i).target, (t ^ ((11 : ℝ) / 10))^k*‖iteratedFDeriv ℝ k
      (fun w : X => fun d : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c i w.1) w.2 0 d : V)) z‖ ≤ MB)
    (hchib : ∀ k ≤ 2+length+1, ∀ z ∈ (a i).target, (t ^ ((11 : ℝ) / 10))^k*‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (hnub : ∀ k ≤ 2+length+1, ∀ z ∈ (a i).target, (t ^ ((11 : ℝ) / 10))^k*‖iteratedFDeriv ℝ k
      (fun w : X => (nu w.1 w.2 : V)) z‖ ≤ Bnu)
    (hAb : ∀ k ≤ 2+length+1, ∀ y ∈ S, (t ^ ((11 : ℝ) / 10))^k*‖iteratedFDeriv ℝ k
      (incrementsModeComplexFirstOrderA (F b) (hF b) (c i b)) y‖ ≤ Mg)
    (hBb : ∀ k ≤ 2+length+1, ∀ y ∈ S, (t ^ ((11 : ℝ) / 10))^k*‖iteratedFDeriv ℝ k
      (incrementsModeComplexFirstOrderB (F b) (hF b) (c i b)) y‖ ≤ Mg)
    (hGb : ∀ k ≤ 2, ∀ y ∈ S, (t ^ ((11 : ℝ) / 10))^k*‖iteratedFDeriv ℝ k
      (fun y => freeGramRightInverse (fderiv ℝ (F b ∘ c i b) y)) y‖ ≤ Mg)
    (hJb : ∀ k ≤ 2, ∀ y ∈ S, (t ^ ((11 : ℝ) / 10))^k*‖iteratedFDeriv ℝ k
      (fun y => (normalSpace (I := IM) (F b) (c i b y)).subtypeL.comp
        (incrementsModeCoordinateJ (F b) (hF b) (c i b) y)) y‖ ≤ Mg)
    (hTb : ∀ k ≤ 2, ∀ y ∈ S, (t ^ ((11 : ℝ) / 10))^k*‖iteratedFDeriv ℝ k
      (incrementsModeTransverseValue (F b) (c i b)) y‖ ≤ Mg)
    (hpsib : ∀ k < 2, ∀ y ∈ S, (t ^ ((11 : ℝ) / 10))^k*‖iteratedFDeriv ℝ (k+1) (fun y => weight*psi y) y‖ ≤ Mpsi)
    (hcoordinate : ∀ y ∈ (source i).target, c i b y = (source i).symm y)
    (hsourceTarget : ∀ y ∈ (source i).target, (b,y) ∈ (a i).target)
    (hpsiOriginal : ∀ y ∈ (source i).target, psi y = (theta i) ((source i).symm y))
    (hamplitudeOriginal : ∀ y ∈ (source i).target,
      chi (b,y) • (nu b y : V) = (amplitude i) ((source i).symm y))
    (hsamples : ∀ j y, y ∈ atlas.support j → y ∈ carrier i → source i y ∈ S)
    (hsliceW : ∀ y, (b,y) ∈ W)
    (hactualCarrier : ∀ q ∈ K i, q.2 ∈ carrier i),
    let CH := round4PrescribedHessianErrorConstant m N length
      (fun _ : Fin 1 => weight) (fun _ => Mpsi) (fun _ => Bchi) (fun _ => Bnu) MB Mg 0
    let C1 := actualPrescribedProbeJetConstant m N p 1 length
      (fun _ : Fin 1 => weight) (fun _ => Mpsi) (fun _ => Bchi) (fun _ => Bnu) MB Mg
    ∀ (j : Fin atlas.count) (x : M), x ∈ atlas.support j →
      ∀ (u : ProbeParameters r) (sine : Bool),
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (fun y =>
          round4PrescribedGlobalWave label F hF c vf phase (t ^ ((6 : ℝ)/5)) length a
            (probeParameterEmbedding label v) (b,(atlas.chart j).symm y))) (atlas.chart j x))
          u (Pi.single (i,sine) 1) -
        (t ^ ((44 : ℝ)/5)*probeTrig sine (weight*(theta i) x/t ^ ((6 : ℝ)/5))) •
          phaseRankOneHessian ((theta i) ∘ (atlas.chart j).symm)
            ((amplitude i) ∘ (atlas.chart j).symm) (atlas.chart j x)‖ ≤
        t ^ ((44 : ℝ)/5) * originalProbeChartModulus |CH| |C1| B1 B2 t := by
  obtain ⟨B1,B2,hB1,hB2,hResponse⟩ := exists_uniform_globalWave_originalAtlas_response
    (N := N) (p := p) (Ep := Ep) atlas hAtlas hcompact source hsource
    carrier hclosed hcarrier
  refine ⟨B1,B2,hB1,hB2,?_⟩
  intro label F hF c vf phase t ht ht1 length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf
    hinput hphase i b chi nu weight psi hphysical hinverse hsourceW hobs hphaseChart
    hpsi hchi hnu S hS MB Mg Bchi Bnu Mpsi hweight hMB hMg hBchi hBnu hBRb hchib hnub
    hAb hBb hGb hJb hTb hpsib hcoordinate hsourceTarget hpsiOriginal hamplitudeOriginal
    hsamples hsliceW hactualCarrier CH C1 j x hx u sine
  have hs := probe_original_scale_conditions t ht ht1
  have hz (y : M) (hy : y ∉ carrier i) : (amplitude i) y = 0 := hamplitudeZero i y hy
  have hh := hResponse label F hF c vf phase (t ^ ((6 : ℝ)/5)) length a W K hW hK hKsource hchart
    hA hB hG hJ hT hBR hvf hinput hphase i b chi nu (t ^ (10 : ℕ)) (t ^ ((11 : ℝ)/10)) weight psi
    hphysical hinverse hsourceW hobs hphaseChart hpsi hchi hnu S hS MB Mg Bchi Bnu Mpsi
    (pow_nonneg ht.le _) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hweight hMB hMg hBchi hBnu
    hBRb hchib hnub hAb hBb hGb hJb hTb hpsib (theta i) (amplitude i) hz
    hcoordinate hsourceTarget hpsiOriginal hamplitudeOriginal hsamples hsliceW hactualCarrier
    j x hx u sine
  rw [probe_delta_div_tau_eq_sigma t ht,probe_tau_div_original_ell t ht] at hh
  convert hh using 1
  unfold originalProbeChartModulus
  rw [abs_of_pos ht]
  ring

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.exists_uniform_globalWave_supported_paper_response
