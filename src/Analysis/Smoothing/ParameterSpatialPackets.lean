import GlobalEmbedding.Offline.PaperWeightedSmoothing
import GlobalEmbedding.Offline.SpatialSmoothingGain

/-!
# Literal spatial jet packets with arbitrary finite parameter dimension

The packet consists of the value and every ordered first/second source-coordinate
partial. Its Cj norm differentiates all source and parameter coordinates. In
particular its base norm has no pure parameter derivatives. Source: main.tex
(6.4) and the product-chart convention in the parameter paragraph of thm:repair.
The packet is a transparent view of actual derivatives of the same map.
-/

open MeasureTheory GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff ENNReal Topology

namespace GlobalEmbedding.Continuation

noncomputable section

/-- Ordered spatial coordinate words of lengths zero, one and two. -/
abbrev ParameterSpatialWord (n : ℕ) := Σ k : Fin 3, Fin k.val → Fin n

/-- Actual spatial derivatives in a full n+d coordinate vector. All direction
vectors have zero parameter coordinates. The empty word is the map value. -/
def parameterSpatialJet {n d q : ℕ} (u : (Fin (n+d) → ℝ) → Fin q → ℝ)
    (w : ParameterSpatialWord n) (z : Fin (n+d) → ℝ) : Fin q → ℝ :=
  iteratedFDeriv ℝ w.1.val u z (fun j => Pi.single (Fin.castAdd d (w.2 j)) 1)

/-- The literal packet indexed by chart and spatial coordinate word. -/
def parameterSpatialPacket {ι : Type*} {n d q : ℕ}
    (u : ι → (Fin (n+d) → ℝ) → Fin q → ℝ) :
    (ι × ParameterSpatialWord n) → (Fin (n+d) → ℝ) → Fin q → ℝ :=
  fun i => parameterSpatialJet (n := n) (d := d) (u i.1) i.2

/-- Base-zero original coordinate norm of the actual spatial packet. -/
def parameterSpatialWeighted {ι : Type*} [Fintype ι] {n d q : ℕ}
    (m : ℕ) (t : ℝ) (u : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ)) : ℝ≥0∞ :=
  paperAtlasWeighted 0 m t (parameterSpatialPacket (n := n) (d := d) u)
    (fun i => O i.1) (fun i => S i.1)

/-- Every packet field is jointly smooth on the original open domain. -/
theorem parameterSpatialJet_contDiffOn {n d q : ℕ}
    {u : (Fin (n+d) → ℝ) → Fin q → ℝ} {O : Set (Fin (n+d) → ℝ)}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O) (w : ParameterSpatialWord n) :
    ContDiffOn ℝ ∞ (parameterSpatialJet (n := n) (d := d) u w) O := by
  have hj : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ w.1.val u) O := by
    intro z hz
    exact ((hu.contDiffAt (hO.mem_nhds hz)).iteratedFDeriv_right (by simp)).contDiffWithinAt
  let L := ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin w.1.val => (Fin (n+d) → ℝ)) (Fin q → ℝ)
    (fun j => Pi.single (Fin.castAdd d (w.2 j)) 1)
  exact L.contDiff.comp_contDiffOn hj

/-- Norms of genuinely identical coordinate germs are identical, also when
infinite. Evaluation domains need only lie in the open differentiation domains. -/
theorem paperAtlasCj_congr_on {ι : Type*} [Fintype ι] {d q : ℕ}
    (j : ℕ) {f g : ι → (Fin d → ℝ) → Fin q → ℝ}
    (O S : ι → Set (Fin d → ℝ)) (hSO : ∀ i, S i ⊆ O i)
    (heq : ∀ i, Set.EqOn (f i) (g i) (O i)) :
    paperAtlasCj j f O S = paperAtlasCj j g O S := by
  unfold paperAtlasCj paperCoordinateCj
  congr 1
  funext i
  congr 1
  funext l
  congr 1
  funext x
  congr 1
  funext c
  rw [paperCoordinatePartial_congr l.val
    (fun y hy => congrFun (heq i hy) c) (hSO i x.property)]

/-- Weighted norms respect the same genuine coordinate germ identities. -/
theorem paperAtlasWeighted_congr_on {ι : Type*} [Fintype ι] {d q : ℕ}
    (base m : ℕ) (t : ℝ) {f g : ι → (Fin d → ℝ) → Fin q → ℝ}
    (O S : ι → Set (Fin d → ℝ)) (hSO : ∀ i, S i ⊆ O i)
    (heq : ∀ i, Set.EqOn (f i) (g i) (O i)) :
    paperAtlasWeighted base m t f O S = paperAtlasWeighted base m t g O S := by
  unfold paperAtlasWeighted
  apply Finset.sum_congr rfl
  intro j hj
  rw [paperAtlasCj_congr_on (j+base) O S hSO heq]

/-- Evaluating any actual source derivative commutes with the same local
joint convolution. All source assumptions are confined to its genuine buffer. -/
theorem parameterSpatialJet_smoothing {n d q : ℕ}
    (mu : Measure (Fin (n+d) → ℝ)) [mu.IsAddHaarMeasure]
    {K : (Fin (n+d) → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K)
    (hcompact : HasCompactSupport K)
    {u : (Fin (n+d) → ℝ) → Fin q → ℝ}
    {U V : Set (Fin (n+d) → ℝ)} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) (ell : ℝ)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    (w : ParameterSpatialWord n) {z : Fin (n+d) → ℝ} (hz : z ∈ U) :
    parameterSpatialJet (n := n) (d := d) (signedSmoothing mu K ell u) w z =
      signedSmoothing mu K ell (parameterSpatialJet (n := n) (d := d) u w) z := by
  unfold parameterSpatialJet
  rw [signedSmoothing_iteratedFDeriv_source_on mu hK hcompact hU hV hu ell hbuffer w.1.val hz]
  have hj : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ w.1.val u) V := by
    intro a ha
    exact ((hu.contDiffAt (hV.mem_nhds ha)).iteratedFDeriv_right (by simp)).contDiffWithinAt
  have hcont : Continuous (fun y => K y • iteratedFDeriv ℝ w.1.val u (z - ell • y)) :=
    (smoothingFamily_contDiffOn hK hV hj ell hbuffer).continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨hz, trivial⟩)
  have hsupp : HasCompactSupport (fun y => K y • iteratedFDeriv ℝ w.1.val u (z - ell • y)) :=
    hcompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _)
  rw [ContinuousMultilinearMap.integral_apply (hcont.integrable_of_hasCompactSupport hsupp)]
  rfl

/-- Every literal packet coordinate is exactly the corresponding spatial
coordinate partial of the same original map, using its original open chart. -/
theorem parameterSpatialJet_eq_paper_partial {n d q : ℕ}
    {u : (Fin (n+d) → ℝ) → Fin q → ℝ} {O : Set (Fin (n+d) → ℝ)}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O) (w : ParameterSpatialWord n)
    {z : Fin (n+d) → ℝ} (hz : z ∈ O) (c : Fin q) :
    parameterSpatialJet (n := n) (d := d) u w z c =
      paperCoordinatePartial (List.ofFn (fun j => Fin.castAdd d (w.2 j)))
        (fun y => u y c) O z := by
  rw [paperCoordinatePartial_ofFn]
  exact (coordinateWordPartialWithin_component u O hO hu w.1.val
    (fun j => Fin.castAdd d (w.2 j)) c z hz).symm

/-- The packet is a linear view of the actual difference on its smooth germ. -/
theorem parameterSpatialJet_sub {n d q : ℕ}
    {f g : (Fin (n+d) → ℝ) → Fin q → ℝ} {z : Fin (n+d) → ℝ}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z)
    (w : ParameterSpatialWord n) :
    parameterSpatialJet (n := n) (d := d) (fun x => f x - g x) w z =
      parameterSpatialJet (n := n) (d := d) f w z - parameterSpatialJet (n := n) (d := d) g w z := by
  unfold parameterSpatialJet
  exact congrArg (fun L => L (fun j => Pi.single (Fin.castAdd d (w.2 j)) 1))
    (iteratedFDeriv_sub_apply (i := w.1.val) (hf.of_le (by simp)) (hg.of_le (by simp)))

/-- Equation (6.4) for the same actual joint local convolution, measured by
all total derivatives of the genuine spatial two-jet. The finite parameter
dimension d is arbitrary, and no chart-count factor appears. Every packet
entry is a literal spatial partial by parameterSpatialJet_eq_paper_partial.
The error packet is taken after smoothing the map, not independently glued.
-/
theorem parameterSpatialWeighted_smoothing_tail {ι : Type*} [Fintype ι] {n d q : ℕ}
    (mu : Measure (Fin (n+d) → ℝ)) [mu.IsAddHaarMeasure]
    {kappa : (Fin (n+d) → ℝ) → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1)
    (m r : ℕ) (u : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (U V : ι → Set (Fin (n+d) → ℝ))
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i)) (hUV : ∀ i, U i ⊆ V i)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (V i))
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (hsegments : ∀ i, ∀ z ∈ U i, ∀ y ∈ tsupport (finiteMomentKernel r kappa),
      ∀ s ∈ Set.Icc (0 : ℝ) 1, z - s • (ell • y) ∈ V i)
    (hNr : parameterSpatialWeighted (n := n) (d := d) r t u V V ≠ ⊤)
    (hNm : parameterSpatialWeighted (n := n) (d := d) m t u V V ≠ ⊤)
    (B : ℝ) (hB : (parameterSpatialWeighted (n := n) (d := d) r t u V V).toReal ≤ B) :
    let S := fun i => signedSmoothing mu (finiteMomentKernel r kappa) ell (u i)
    parameterSpatialWeighted (n := n) (d := d) m tau (fun i z => S i z - u i z) U U ≠ ⊤ ∧
      (parameterSpatialWeighted (n := n) (d := d) m tau (fun i z => S i z - u i z) U U).toReal ≤
        paperSmoothingTailConstant mu kappa m r *
          (B * (ell/t)^r + (parameterSpatialWeighted (n := n) (d := d) m t u V V).toReal * (tau/t)^r) := by
  dsimp only
  let K := finiteMomentKernel r kappa
  have hK := finiteMomentKernel_contDiff hsmooth r
  have hKc := finiteMomentKernel_hasCompactSupport hcompact r
  have hbuffer : ∀ i, ∀ z ∈ U i, ∀ y ∈ tsupport K, z - ell • y ∈ V i := by
    intro i z hz y hy
    simpa only [one_smul] using hsegments i z hz y hy 1 (by simp)
  have hSu (i : ι) := signedSmoothing_contDiffOn mu hK hKc (hU i) (hV i) (hu i) ell (hbuffer i)
  have hpacket (i : ι × ParameterSpatialWord n) :
      ContDiffOn ℝ ∞ (parameterSpatialPacket (n := n) (d := d) u i) (V i.1) :=
    parameterSpatialJet_contDiffOn (hV i.1) (hu i.1) i.2
  have heq (i : ι × ParameterSpatialWord n) :
      Set.EqOn (parameterSpatialPacket (n := n) (d := d) (fun i z => signedSmoothing mu K ell (u i) z - u i z) i)
        (fun z => signedSmoothing mu K ell (parameterSpatialPacket (n := n) (d := d) u i) z -
          parameterSpatialPacket (n := n) (d := d) u i z) (U i.1) := by
    intro z hz
    rw [parameterSpatialPacket, parameterSpatialJet_sub
      ((hSu i.1).contDiffAt ((hU i.1).mem_nhds hz))
      ((hu i.1).contDiffAt ((hV i.1).mem_nhds (hUV i.1 hz))),
      parameterSpatialJet_smoothing mu hK hKc (hU i.1) (hV i.1) (hu i.1) ell (hbuffer i.1) i.2 hz]
    rfl
  have hn := paperAtlasWeighted_congr_on 0 m tau (fun i : ι × ParameterSpatialWord n => U i.1)
    (fun i => U i.1) (fun _ => Set.Subset.rfl) heq
  unfold parameterSpatialWeighted
  rw [hn]
  exact paperAtlasWeighted_smoothing_tail (ι := ι × ParameterSpatialWord n) (q := q)
    mu hsmooth hcompact hmass m r
    (parameterSpatialPacket (n := n) (d := d) u) (fun i => U i.1) (fun i => V i.1)
    (fun i => hU i.1) (fun i => hV i.1) (fun i => hUV i.1) hpacket
    htau htaul helt ht1 (fun i => hsegments i.1) hNr hNm B hB

#print axioms parameterSpatialJet_smoothing
#print axioms parameterSpatialJet_eq_paper_partial
#print axioms parameterSpatialWeighted_smoothing_tail

end
end GlobalEmbedding.Continuation
