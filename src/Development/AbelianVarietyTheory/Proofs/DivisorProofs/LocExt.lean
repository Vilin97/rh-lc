module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothBumpComplexPointsProjective

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BumpPts

theorem exists_finset_closure_eq_top {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k)
    [LocallyOfFiniteType p] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ s : Finset Γ(X, W), Subring.closure (Set.range (constFn p W) ∪ ↑s) = ⊤ := by
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
  letI := (p.appLE ⊤ W (fun _ _ => trivial)).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Sp k, ⊤) Γ(X, W) := h
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := Γ(Sp k, ⊤)) (A := Γ(X, W))
  refine ⟨s, ?_⟩
  have e : Set.range (constFn p W) = Set.range (algebraMap Γ(Sp k, ⊤) Γ(X, W)) := by
    ext f
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨b, rfl⟩
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b, ?_⟩
      have hb : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b) = b := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
      show (p.appLE ⊤ W (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b)) = _
      rw [hb]
      rfl
  rw [e, ← Algebra.adjoin_eq_ring_closure, hs]
  rfl

theorem exists_cInf_bump (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (hp : IsProjOver p) (σ : k →+* ℂ) (y : CxPts p σ) (O : Set (CxPts p σ)) (hO : IsOpen O)
    (hy : y ∈ O) : ∃ χ : CxPts p σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧
      tsupport χ ⊆ O := by
  haveI : IsProper p := CommonModel.isProper_of_isProjOver hp
  haveI : T2Space (CxPts p σ) := t2Space_cxPts_of_isProjOver σ hp
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y.1 (le_preimage_top y.1)
  have hyW' : y ∈ ptsIn p σ W := hyW
  obtain ⟨s, hs⟩ := exists_finset_closure_eq_top p hW
  let φ : CxPts p σ → (s → ℂ) := fun z a => ev p σ W a.1 z

  obtain ⟨S, hS, hSO⟩ : ∃ S ∈ 𝓝 (φ y), ∀ z ∈ ptsIn p σ W, φ z ∈ S → z ∈ O := by
    let l := Filter.comap φ (𝓝 (φ y)) ⊓ 𝓟 (ptsIn p σ W)
    have hφl : Tendsto φ l (𝓝 (φ y)) := tendsto_comap.mono_left inf_le_left
    have ht : Tendsto (fun z => z) l (𝓝 y) := by
      refine (PtsOver.tendsto_iff_of_generators hW hyW hs).2 ⟨?_, fun f hf => ?_⟩
      · exact mem_inf_of_right (mem_principal_self _)
      · exact ((continuous_apply (⟨f, hf⟩ : s)).tendsto _).comp hφl
    have h : O ∈ l := ht (hO.mem_nhds hy)
    rw [mem_inf_principal] at h
    obtain ⟨S, hS, hSO⟩ := mem_comap.1 h
    exact ⟨S, hS, fun z hz hzS => hSO hzS hz⟩
  obtain ⟨F, hFS, hFc, hFd, hFr, hF1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hS
  let K : Set (CxPts p σ) := {z | z ∈ ptsIn p σ W ∧ φ z ∈ tsupport F}

  have hKc : IsCompact K := by
    refine isCompact_iff_ultrafilter_le_nhds.2 fun u hu => ?_
    have hKu : K ∈ u := le_principal_iff.1 hu
    have hWu : ∀ᶠ z in (u : Filter (CxPts p σ)), z ∈ ptsIn p σ W := mem_of_superset hKu fun z hz => hz.1
    obtain ⟨v, -, hv⟩ := hFc.ultrafilter_le_nhds (u.map φ)
      (le_principal_iff.2 (Ultrafilter.mem_map.2
        (mem_of_superset hKu fun z (hz : z ∈ K) => hz.2)))
    have hv' : Tendsto φ u (𝓝 v) := hv
    have hcst : ∀ a : k, ∀ z ∈ ptsIn p σ W, ev p σ W (constFn p W a) z = ev p σ W (constFn p W a) y :=
      fun a z hz => by
        show valR z.1 W _ = valR y.1 W _
        rw [valR_constFn p z.1 W hz, valR_constFn p y.1 W hyW, z.2, y.2]
    have hlim : ∀ f : Γ(X, W), ∃ c, Tendsto (fun z => ev p σ W f z) u (𝓝 c) := by
      intro f
      have hf : f ∈ Subring.closure (Set.range (constFn p W) ∪ ↑s) := hs ▸ Subring.mem_top f
      induction hf using Subring.closure_induction with
      | mem f hf =>
        rcases hf with ⟨a, rfl⟩ | hf
        · exact ⟨_, tendsto_const_nhds.congr' (hWu.mono fun z hz => (hcst a z hz).symm)⟩
        · exact ⟨v ⟨f, hf⟩, ((continuous_apply (⟨f, hf⟩ : s)).tendsto _).comp hv'⟩
      | zero =>
        exact ⟨0, tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 0).trans (map_zero _)).symm)⟩
      | one =>
        exact ⟨1, tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 1).trans (map_one _)).symm)⟩
      | add f g _ _ hf hg =>
        obtain ⟨c, hc⟩ := hf
        obtain ⟨d, hd⟩ := hg
        exact ⟨c + d, (hc.add hd).congr fun z => (ev_add f g z).symm⟩
      | neg f _ hf =>
        obtain ⟨c, hc⟩ := hf
        exact ⟨-c, hc.neg.congr' (hWu.mono fun z hz => by
          show -ev p σ W f z = ev p σ W (-f) z
          rw [ev_eq hz, ev_eq hz, map_neg])⟩
      | mul f g _ _ hf hg =>
        obtain ⟨c, hc⟩ := hf
        obtain ⟨d, hd⟩ := hg
        exact ⟨c * d, (hc.mul hd).congr fun z => (ev_mul f g z).symm⟩
    choose c hc using hlim
    let ψ : Γ(X, W) →+* ℂ :=
      { toFun := c
        map_one' := tendsto_nhds_unique (hc 1)
          (tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 1).trans (map_one _)).symm))
        map_mul' := fun f g => tendsto_nhds_unique (hc (f * g))
          (((hc f).mul (hc g)).congr fun z => (ev_mul f g z).symm)
        map_zero' := tendsto_nhds_unique (hc 0)
          (tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 0).trans (map_zero _)).symm))
        map_add' := fun f g => tendsto_nhds_unique (hc (f + g))
          (((hc f).add (hc g)).congr fun z => (ev_add f g z).symm) }
    have hψ : ∀ a, ψ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W a) = σ a := fun a => tendsto_nhds_unique (hc _)
      (tendsto_const_nhds.congr' (hWu.mono fun z hz => (ev_algX hz a).symm))
    let z' : CxPts p σ := ofHom hW ψ hψ
    have hz'W : z' ∈ ptsIn p σ W := ofHom_mem hW ψ hψ
    have hz'ev : ∀ f, ev p σ W f z' = c f := fun f => ev_ofHom hW ψ hψ f
    have ht : Tendsto (fun z => z) (u : Filter (CxPts p σ)) (𝓝 z') := by
      refine (PtsOver.tendsto_iff_of_generators hW hz'W hs).2 ⟨hWu, fun f _ => ?_⟩
      have := hc f
      rw [← hz'ev f] at this
      exact this
    have hφz' : φ z' = v := funext fun a =>
      (hz'ev a.1).trans (tendsto_nhds_unique (hc a.1) (((continuous_apply a).tendsto _).comp hv'))
    refine ⟨z', ⟨hz'W, ?_⟩, ht⟩
    rw [hφz']
    exact hFc.isClosed.mem_of_tendsto hv' (mem_of_superset hKu fun z hz => hz.2)
  have hKcl : IsClosed K := hKc.isClosed
  let χ : CxPts p σ → ℝ := (ptsIn p σ W).indicator fun z => F (φ z)
  have hsupp : Function.support χ ⊆ K := fun z hz => by
    rw [Function.mem_support, Set.indicator_apply_ne_zero] at hz
    exact ⟨hz.1, subset_tsupport _ hz.2⟩
  refine ⟨χ, fun z => ?_, fun z => Set.indicator_nonneg (fun w _ => (hFr ⟨_, rfl⟩).1) z, ?_, ?_⟩
  · by_cases hz : z ∈ ptsIn p σ W
    · refine ⟨W, s, inferInstance, fun a => a.1, F, Set.univ, hz, isOpen_univ, trivial,
        hFd.contDiffOn, ?_⟩
      filter_upwards [(isOpen_ptsIn W).mem_nhds hz] with w hw
      exact Set.indicator_of_mem hw _
    · have hzK : z ∉ K := fun h => hz h.1
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hKcl.isOpen_compl.mem_nhds hzK] with w hw
      exact Function.notMem_support.1 fun h => hw (hsupp h)
  · show 0 < (ptsIn p σ W).indicator (fun z => F (φ z)) y
    rw [Set.indicator_of_mem hyW', hF1]
    exact one_pos
  · exact (closure_minimal hsupp hKcl).trans fun z hz => hSO z hz.1 (hFS hz.2)

end GlobalTheory.BumpPts
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothBumpComplexPointsProjectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

theorem _root_.GlobalTheory.T.exists_smooth_bump_complexPoints_projective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (y : CxPts p σ) (O : Set (CxPts p σ)), IsOpen O → y ∈ O → ∃ χ : CxPts p σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧ tsupport χ ⊆ O := by
  first | exact @GlobalTheory.BumpPts.exists_cInf_bump | exact GlobalTheory.BumpPts.exists_cInf_bump | (intros; apply GlobalTheory.BumpPts.exists_cInf_bump <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CInfAtSum

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory.CInfGlue

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem cInfAt_inv {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) (h0 : f y ≠ 0) :
    CInfAt (fun z => (f z)⁻¹) y := by
  obtain ⟨W, ι, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨W, ι, inferInstance, g, fun v => (G v)⁻¹, O ∩ G ⁻¹' {0}ᶜ, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_compl_singleton, ⟨h₃, ?_⟩,
    (h₄.mono Set.inter_subset_left).inv fun v hv => hv.2, h₅.mono fun z hz => by simp only [hz]⟩
  have := h₅.self_of_nhds
  simp only at this
  rw [Set.mem_preimage, ← this]
  exact h0

theorem cInfAt_mul {f g : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) (h' : CInfAt g y) :
    CInfAt (fun z => f z * g z) y :=
  h.comp₂ h' (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)

theorem cInfAt_sum {κ : Type} (s : Finset κ) (f : κ → CxPts p σ → ℝ) {y : CxPts p σ}
    (h : ∀ j ∈ s, CInfAt (f j) y) : CInfAt (fun z => ∑ j ∈ s, f j z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const 0 y
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem cInfAt_cut {χ v : CxPts p σ → ℝ} {O : Set (CxPts p σ)} (hχ : ∀ z, CInfAt χ z)
    (hs : tsupport χ ⊆ O) (hv : ∀ z ∈ O, CInfAt v z) (z : CxPts p σ) :
    CInfAt (fun w => χ w * v w) z := by
  by_cases hz : z ∈ O
  · exact cInfAt_mul (hχ z) (hv z hz)
  · have h0 : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hz (hs h)
    refine (cInfAt_const 0 z).congr ?_
    filter_upwards [h0] with w hw
    simp [hw]

theorem glue : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (T : Type) (m : T → CxPts p σ) (u : T → ℝ), (∀ x : CxPts p σ, ∃ (O : Set (CxPts p σ)) (v : CxPts p σ → ℝ), IsOpen O ∧ x ∈ O ∧ (∀ z ∈ O, CInfAt v z) ∧ ∀ t, m t ∈ O → v (m t) = u t) → ∃ v : CxPts p σ → ℝ, (∀ z, CInfAt v z) ∧ ∀ t, v (m t) = u t := by
  intro k _ X p hp σ T m u h
  haveI : CompactSpace (CxPts p σ) := GlobalTheory.CxPts.compactSpace σ hp
  choose O v hO hx hv hu using h
  choose χ hχ hχ0 hχx hχs using fun x => GlobalTheory.T.exists_smooth_bump_complexPoints_projective k X p hp σ x (O x) (hO x) (hx x)
  have hc : ∀ x, Continuous (χ x) := fun x =>
    continuous_iff_continuousAt.2 fun z => (hχ x z).continuousAt
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => {z | 0 < χ x z})
    (fun x => isOpen_lt continuous_const (hc x))
    (fun z _ => Set.mem_iUnion.2 ⟨z, hχx z⟩)
  have hS : ∀ z, 0 < ∑ x ∈ s, χ x z := fun z => by
    obtain ⟨x, hxs, hz⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ z))
    exact Finset.sum_pos' (fun j _ => hχ0 j z) ⟨x, hxs, hz⟩
  refine ⟨fun z => (∑ x ∈ s, χ x z * v x z) * (∑ x ∈ s, χ x z)⁻¹, fun z => ?_, fun t => ?_⟩
  · exact cInfAt_mul
      (cInfAt_sum s (fun x w => χ x w * v x w) fun x _ => cInfAt_cut (hχ x) (hχs x) (hv x) z)
      (cInfAt_inv (cInfAt_sum s χ fun x _ => hχ x z) (hS z).ne')
  · have e : ∀ x ∈ s, χ x (m t) * v x (m t) = χ x (m t) * u t := fun x _ => by
      by_cases h0 : χ x (m t) = 0
      · simp [h0]
      · rw [hu x t (hχs x (subset_tsupport _ h0))]
    simp only
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul, mul_right_comm, mul_inv_cancel₀ (hS _).ne', one_mul]

end GlobalTheory.CInfGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedOfIsProjOver

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocExt

theorem isSeparated_of_isProjOver {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R} (h : IsProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsSeparated (PSpace.str R N) := by unfold PSpace.str; infer_instance
  infer_instance

end GlobalTheory.LocExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocExt

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.ClosedExt

theorem locExt {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (hp : IsProjOver p) (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (u : CxPts q σ → ℝ)
    (hu : ∀ y, CInfAt u y) (x : CxPts p σ) :
    ∃ (O : Set (CxPts p σ)) (v : CxPts p σ → ℝ), IsOpen O ∧ x ∈ O ∧ (∀ z ∈ O, CInfAt v z) ∧
      ∀ y : CxPts q σ, ptMap π hπ σ y ∈ O → v (ptMap π hπ σ y) = u y := by
  have := GlobalTheory.LocExt.isSeparated_of_isProjOver hp
  have hq : IsProjOver q := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    exact ⟨N, π ≫ i, inferInstance, by rw [Category.assoc, hπ]⟩
  have hemb : IsClosedEmbedding (ptMap π hπ σ) := by
    have : CompactSpace (CxPts q σ) := GlobalTheory.CxPts.compactSpace σ hq
    have hc : Continuous (ptMap π hπ σ) := continuous_of_comp (f := π) fun _ => rfl
    refine hc.isClosedEmbedding fun y y' h => Subtype.ext ?_
    exact (cancel_mono π).1 (congrArg Subtype.val h)
  by_cases hx : ∃ y : CxPts q σ, ptMap π hπ σ y = x
  · obtain ⟨y₀, rfl⟩ := hx
    obtain ⟨W, ι, _, g, F, O₀, h₁, h₂, h₃, h₄, h₅⟩ := hu y₀
    obtain ⟨t, ht, htW⟩ := (π.isClosedEmbedding.isInducing.isOpen_iff).1 W.2
    let W₁ : X.Opens := ⟨t, ht⟩
    have hW₁ : π ⁻¹ᵁ W₁ = W := Opens.ext htW
    have hz₀ : π (y₀.1 (IsLocalRing.closedPoint ℂ)) ∈ W₁ := by
      have := mem_ptsIn.1 h₁
      rw [← hW₁] at this
      exact this
    obtain ⟨W', hW'a, hzW', hW'le⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hz₀
    have hle : π ⁻¹ᵁ W' ≤ W := by
      rw [← hW₁]
      exact fun a ha => hW'le ha
    choose g' hg' using fun a => π.app_surjective W' hW'a (resG Y hle (g a))
    have hval (y : CxPts q σ) (hy : y ∈ ptsIn q σ (π ⁻¹ᵁ W')) (a : ι) :
        ev p σ W' (g' a) (ptMap π hπ σ y) = ev q σ W (g a) y := by
      rw [← ev_res hle hy, ← hg' a]
      exact valR_comp y.1 π W' (g' a)
    obtain ⟨s, hs, hsu⟩ := h₅.exists_mem
    obtain ⟨N, hNs, hN, hy₀N⟩ := mem_nhds_iff.1 hs
    obtain ⟨N', hN', hNN'⟩ := (hemb.isInducing.isOpen_iff).1 hN
    have hE : IsOpen (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀) :=
      (continuousOn_pi.2 fun a => continuousOn_ev (g' a)).isOpen_inter_preimage (isOpen_ptsIn W') h₂
    have hy₀W' : y₀ ∈ ptsIn q σ (π ⁻¹ᵁ W') := mem_ptsIn.2 hzW'
    refine ⟨N' ∩ (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀),
      fun z => F fun a => ev p σ W' (g' a) z, hN'.inter hE, ⟨?_, ?_, ?_⟩, fun z hz => ?_, fun y hy => ?_⟩
    · have : y₀ ∈ ptMap π hπ σ ⁻¹' N' := hNN'.symm ▸ hy₀N
      exact this
    · exact mem_ptsIn.2 hzW'
    · simp only [Set.mem_preimage, hval y₀ hy₀W']
      exact h₃
    · exact ⟨W', ι, inferInstance, g', F, O₀, hz.2.1, h₂, hz.2.2, h₄, EventuallyEq.rfl⟩
    · have hyN : y ∈ N := by
        have : y ∈ ptMap π hπ σ ⁻¹' N' := hy.1
        rwa [hNN'] at this
      have hyW' : y ∈ ptsIn q σ (π ⁻¹ᵁ W') := mem_ptsIn.2 (mem_ptsIn.1 hy.2.1)
      simp only [hval y hyW']
      exact (hsu (hNs hyN)).symm
  · exact ⟨(Set.range (ptMap π hπ σ))ᶜ, fun _ => 0, hemb.isClosed_range.isOpen_compl, hx,
      fun z _ => cInfAt_const 0 z, fun y hy => absurd (Set.mem_range_self y) hy⟩

theorem exists_extension : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (u : CxPts q σ → ℝ), (∀ y, CInfAt u y) → ∃ v : CxPts p σ → ℝ, (∀ y, CInfAt v y) ∧ ∀ y, v (ptMap π hπ σ y) = u y := by
  intro k _ X Y p q σ hp π _ hπ u hu
  exact GlobalTheory.CInfGlue.glue k X p hp σ (CxPts q σ) (ptMap π hπ σ) u (locExt hp π hπ u hu)

end GlobalTheory.ClosedExt
end
end
