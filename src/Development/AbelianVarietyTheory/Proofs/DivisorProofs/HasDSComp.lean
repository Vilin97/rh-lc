module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TestFnConstTermVanishX
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.IrredSt
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleRepHasTraceFiniteAdelicPureTensorFunctStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrUnitaryTraceNeZeroCopyFinDSX
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonFieldTypeVanishingX
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspMultiplicityCompletionEqDiscreteSeriesModelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleUnitaryCompletionFiniteTimesDSStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryEquivIffFinitePartEquivDiscreteSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOperatorsVanishingRadicalIntegralsUnitarStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSide
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumEqSumOfMatchingFamilyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryRepEqFiniteSmoothPartTensorDisStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorSplitOneRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceIntegratedOpMulEqZeroOfIsotypicStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwise
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.ExistsIrreducibleSubrepresentationBis
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt

-- Source module: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.AdmissibleRepresentationFactorisation

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace MainStatements.Flath2

open GlobalTheory.PRep (fixed smoothPart smoothRep IsSmooth)
open scoped Topology

theorem finiteDimensional_of_compact_bdd {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsCompactOperator T) (X : Submodule ℂ E) {c : ℝ} (hc : 0 < c)
    (hX : ∀ x ∈ X, c * ‖x‖ ≤ ‖T x‖) : FiniteDimensional ℂ X := by
  set Y := X.topologicalClosure with hYdef
  have hcl : IsClosed {x : E | c * ‖x‖ ≤ ‖T x‖} :=
    isClosed_le (continuous_const.mul continuous_norm) (continuous_norm.comp T.continuous)
  have hY : ∀ y ∈ Y, c * ‖y‖ ≤ ‖T y‖ := by
    intro y hy
    have hy' : y ∈ closure (X : Set E) := by rwa [← Submodule.topologicalClosure_coe]
    exact closure_minimal (fun x hx => hX x hx) hcl hy'
  haveI : CompleteSpace Y := X.isClosed_topologicalClosure.completeSpace_coe
  let f : Y →L[ℂ] E := T ∘L Y.subtypeL
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) f := by
    refine f.antilipschitz_of_bound fun y => ?_
    rw [Real.coe_toNNReal _ (inv_nonneg.2 hc.le)]
    exact (le_inv_mul_iff₀ hc).2 (hY y y.2)
  have hemb : Topology.IsClosedEmbedding f := hanti.isClosedEmbedding f.uniformContinuous
  have hK := hT.isCompact_closure_image_closedBall 1
  have hpre : IsCompact (f ⁻¹' closure (T '' Metric.closedBall 0 1)) := hemb.isCompact_preimage hK
  have hball : IsCompact (Metric.closedBall (0 : Y) 1) :=
    hpre.of_isClosed_subset Metric.isClosed_closedBall fun y hy =>
      subset_closure ⟨(y : E), mem_closedBall_zero_iff.2 (mem_closedBall_zero_iff.1 hy), rfl⟩
  haveI : FiniteDimensional ℂ Y := FiniteDimensional.of_isCompact_closedBall₀ (𝕜 := ℂ) zero_lt_one hball
  exact Submodule.finiteDimensional_of_le X.le_topologicalClosure

theorem mem_fixed_imp {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    {K : Subgroup G} {x : X} (h : x ∈ fixed ρ K) : ∀ g ∈ K, ρ g x = x := fun g hg => by
  simpa using h ⟨g, hg⟩

noncomputable def phiDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GA D V) : ℂ :=
  ∏ τ, ⟪unitVec (H := M.H τ), dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (unitVec (H := M.H τ))⟫_ℂ

theorem continuous_phiDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Continuous (phiDS M) := by
  unfold phiDS
  refine continuous_finsetProd _ fun τ _ => continuous_const.inner ?_
  exact ((isIrrUnitary_dsRep M τ).unitary.continuous_apply (unitVec (H := M.H τ))).comp
    (continuous_projArch D.sp.cm.sig V.gram (placeOf D τ))

theorem phiDS_one {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : phiDS M 1 = 1 := by
  unfold phiDS
  refine Finset.prod_eq_one fun τ _ => ?_
  have : Nontrivial (M.H τ) := (isIrrUnitary_dsRep M τ).irred.1
  have hunit : ‖unitVec (H := M.H τ)‖ = 1 := by
    have h : ∃ x : M.H τ, ‖x‖ = 1 := exists_norm_eq (M.H τ) zero_le_one
    rw [unitVec, dite_eq_left h]
    exact h.choose_spec
  simp only [map_one, ContinuousLinearMap.one_apply]
  rw [inner_self_eq_norm_sq_to_K, hunit]
  simp


theorem inner_apply_homDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)}
    (hπ : IsUnitaryRep π) {K : Subgroup (GfC V)} {Φ : ContinuousMultilinearMap ℂ M.H H} (hΦ : Φ ∈ homDS M π ⊤)
    (hfix : ∀ k ∈ K, ∀ y, π (k : GA D V) (Φ y) = Φ y) (g : GA D V) (hg : toFin V g ∈ K) :
    ⟪Φ (fun τ => unitVec (H := M.H τ)), π g (Φ (fun τ => unitVec (H := M.H τ)))⟫_ℂ =
      ⟪Φ (fun τ => unitVec (H := M.H τ)), Φ (fun τ => unitVec (H := M.H τ))⟫_ℂ * phiDS M g := by
  classical
  have e1 : π g (Φ (fun τ => unitVec (H := M.H τ))) =
      π (toInf V g : GA D V) (π (toFin V g : GA D V) (Φ (fun τ => unitVec (H := M.H τ)))) := by
    conv_lhs => rw [← toInf_mul_toFin g]
    rw [map_mul]; rfl
  rw [e1, hfix _ hg, GlobalTheory.TrAct.toInf_apply_homDS D V S M H π ⊤ Φ hΦ g]
  rw [inner_eq_bePi (fun τ => isIrrUnitary_dsRep M τ) hπ hΦ hΦ]
  rfl


theorem eq_zero_of_apply_unitVec {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)}
    (hπ : IsUnitaryRep π) {Φ : ContinuousMultilinearMap ℂ M.H H} (hΦ : Φ ∈ homDS M π ⊤)
    (h0 : Φ (fun τ => unitVec (H := M.H τ)) = 0) : Φ = 0 := by
  classical
  by_contra hne
  have hpos := bePi_self_pos (fun τ => isIrrUnitary_dsRep M τ) hπ hΦ hne
  simp only [bePi] at hpos
  rw [h0, inner_zero_left] at hpos
  simp at hpos



theorem finiteDimensional_of_bump {G E : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {π : G →* (E →L[ℂ] E)} (hπ : IsUnitaryRep π) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {φ : G → ℂ} (hφc : Continuous φ) (hφ1 : φ 1 = 1) {A : Set G} (hA : IsOpen A) (h1 : (1 : G) ∈ A)
    (hbump : ∀ N ∈ 𝓝 (1 : G), ∃ b : G → ℝ, Continuous b ∧ HasCompactSupport b ∧ 0 ≤ b ∧ b 1 = 1 ∧
      Function.support b ⊆ N ∧ IsCompactOperator (repOp π μ fun g => (b g : ℂ)))
    (X : Submodule ℂ E) (hX : ∀ x ∈ X, ∀ g ∈ A, ⟪x, π g x⟫_ℂ = ⟪x, x⟫_ℂ * φ g) : FiniteDimensional ℂ X := by
  set N : Set G := A ∩ {g | 1 / 2 < (φ g).re} with hNdef
  have hN : N ∈ 𝓝 (1 : G) := by
    refine IsOpen.mem_nhds (hA.inter (isOpen_lt continuous_const (Complex.continuous_re.comp hφc))) ⟨h1, ?_⟩
    show 1 / 2 < (φ 1).re
    rw [hφ1]; norm_num
  obtain ⟨b, hbc, hbcs, hb0, hb1, hbs, hcpt⟩ := hbump N hN
  set f : G → ℂ := fun g => (b g : ℂ) with hfdef
  have hfc : Continuous f := Complex.continuous_ofReal.comp hbc
  have hfcs : HasCompactSupport f := hbcs.comp_left Complex.ofReal_zero
  set J : ℂ := ∫ g, f g * φ g ∂μ with hJdef
  have hint : Integrable (fun g => f g * φ g) μ :=
    (hfc.mul hφc).integrable_of_hasCompactSupport (hfcs.mono (Function.support_mul_subset_left _ _))
  have hsupp : ∀ g, b g ≠ 0 → g ∈ N := fun g hg => hbs (Function.mem_support.2 hg)
  have hJre : J.re = ∫ g, b g * (φ g).re ∂μ := by
    rw [hJdef, ← RCLike.re_to_complex, ← integral_re hint]
    congr 1
    funext g
    simp [hfdef]
  have hJpos : 0 < J.re := by
    rw [hJre]
    refine (hbc.mul (Complex.continuous_re.comp hφc)).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := 1) ?_ ?_ ?_
    · exact hbcs.mono (Function.support_mul_subset_left _ _)
    · intro g
      by_cases hg : b g = 0
      · simp [hg]
      · exact mul_nonneg (hb0 g) ((hsupp g hg).2.le.trans' (by norm_num))
    · simp [hb1, hφ1]
  have hJ0 : J ≠ 0 := fun h => by rw [h] at hJpos; simp at hJpos
  have hbound : ∀ x ∈ X, ‖J‖ * ‖x‖ ≤ ‖repOp π μ f x‖ := by
    intro x hxX
    have hx : ⟪x, repOp π μ f x⟫_ℂ = ⟪x, x⟫_ℂ * J := by
      rw [hπ.inner_repOp hfc hfcs, hJdef, ← integral_const_mul]
      congr 1
      funext g
      by_cases hg : b g = 0
      · simp [hfdef, hg]
      · rw [hX x hxX g (hsupp g hg).1]; ring
    have hn : ‖⟪x, x⟫_ℂ * J‖ = ‖x‖ ^ 2 * ‖J‖ := by
      rw [norm_mul, inner_self_eq_norm_sq_to_K]; simp
    have hcs : ‖x‖ ^ 2 * ‖J‖ ≤ ‖x‖ * ‖repOp π μ f x‖ := by
      rw [← hn, ← hx]; exact norm_inner_le_norm _ _
    rcases (norm_nonneg x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · refine le_of_mul_le_mul_left ?_ hpos
      have : ‖x‖ * (‖J‖ * ‖x‖) = ‖x‖ ^ 2 * ‖J‖ := by ring
      linarith
  exact finiteDimensional_of_compact_bdd _ hcpt X (norm_pos_iff.2 hJ0) hbound


theorem admissible_representation_factorisation : AdmSt := by
  intro D V S M μ _ H _ _ _ π hπ hcpt hU
  classical
  refine ⟨isSmooth_smoothRep _, fun K hKo hKc => ?_⟩
  let ev : fixed (finPartDSSm M hU) K →ₗ[ℂ] H :=
    (ContinuousMultilinearMap.apply ℂ M.H H (fun τ => unitVec (H := M.H τ))).toLinearMap ∘ₗ
      (homDS M π ⊤).subtype ∘ₗ (smoothPart (finPartDS M hU)).subtype ∘ₗ (fixed (finPartDSSm M hU) K).subtype
  have hev : ∀ Φ : fixed (finPartDSSm M hU) K,
      ev Φ = (((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H)
        (fun τ => unitVec (H := M.H τ)) := fun Φ => rfl
  have hfix : ∀ Φ : fixed (finPartDSSm M hU) K, ∀ k ∈ K, ∀ y,
      π (k : GA D V) ((((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y) =
        (((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y :=
    fun Φ k hk y => congrArg (fun Ψ : smoothPart (finPartDS M hU) =>
      ((Ψ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y) (mem_fixed_imp Φ.2 k hk)
  have hX : ∀ x ∈ LinearMap.range ev, ∀ g ∈ {g : GA D V | toFin V g ∈ K},
      ⟪x, π g x⟫_ℂ = ⟪x, x⟫_ℂ * phiDS M g := by
    rintro _ ⟨Φ, rfl⟩ g hg
    rw [hev Φ]
    exact inner_apply_homDS hπ ((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤).2 (hfix Φ) g hg
  have hbump : ∀ N ∈ 𝓝 (1 : GA D V), ∃ b : GA D V → ℝ, Continuous b ∧ HasCompactSupport b ∧ 0 ≤ b ∧ b 1 = 1 ∧
      Function.support b ⊆ N ∧ IsCompactOperator (repOp π μ fun g => (b g : ℂ)) := by
    intro N hN
    obtain ⟨b, hb, hb0, hb1, hbs⟩ := GlobalTheory.CuspSpectrum.exists_bump_ccAd (isCMExt_host D) hN
    have hfc := continuous_of_mem_ccAd hb
    exact ⟨b, Complex.continuous_re.comp hfc.1, hfc.2.comp_left (g := Complex.re) Complex.zero_re, hb0, hb1, hbs,
      hcpt _ hb⟩
  have h1 : (1 : GA D V) ∈ {g : GA D V | toFin V g ∈ K} := by
    show toFin V 1 ∈ K
    rw [map_one]; exact K.one_mem
  have : FiniteDimensional ℂ (LinearMap.range ev) :=
    finiteDimensional_of_bump hπ μ (continuous_phiDS M) (phiDS_one M) (hKo.preimage (continuous_toFin V)) h1
      hbump _ hX
  have hinj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Φ hΦ
    rw [hev Φ] at hΦ
    have h0 := eq_zero_of_apply_unitVec hπ ((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤).2 hΦ
    exact Subtype.ext (Subtype.ext (Subtype.ext h0))
  exact Module.Finite.of_injective ev.rangeRestrict fun a b e => hinj (congrArg Subtype.val e)

end MainStatements.Flath2
end
end

-- Source module: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.CompSt

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace MainStatements.Flath2

theorem compSt : CompSt := by
  intro D V H _ _ _ π hπ w W hW
  set ρ := π.comp (embArch D.sp.cm.sig V.gram w) with hρdef
  have hρ : IsUnitaryRep ρ := isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
  let δ : IrrU (GArch D.sp.cm.sig V.gram w) := ⟨W, hW.1.rep, isIrrUnitary_rep hρ hW⟩
  refine ⟨δ, ?_⟩
  show isoPart δ.π ρ ⊤ = ⊤
  set P := isoPart δ.π ρ ⊤ with hPdef
  have hP : IsSubrep ρ P := isSubrep_isoPart

  have hcomm : ∀ g' : GA D V, projArch D.sp.cm.sig V.gram w g' = 1 → ∀ v ∈ P, π g' v ∈ P := by
    intro g' hg' v hv
    have hle : P ≤ P.comap ((π g' : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine isoPart_le (hP.1.preimage (π g').continuous) fun T hT x => ?_
      show π g' (T x) ∈ P
      have hT' : (π g').comp T ∈ homIn δ.π ρ ⊤ := by
        refine mem_homIn_top.2 fun h y => ?_
        have hc : Commute (embArch D.sp.cm.sig V.gram w h) g' := commute_embArch _ _ h hg'
        have e1 : π g' (π (embArch D.sp.cm.sig V.gram w h) (T y)) = π (embArch D.sp.cm.sig V.gram w h) (π g' (T y)) := by
          rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, hc.eq]
        simp only [ContinuousLinearMap.comp_apply]
        rw [(mem_homIn_top.1 hT) h y]
        exact e1
      exact apply_mem_isoPart hT' x
    exact hle hv
  have hinv : IsSubrep π P := by
    refine ⟨hP.1, fun g v hv => ?_⟩
    set x := projArch D.sp.cm.sig V.gram w g
    set g' : GA D V := (embArch D.sp.cm.sig V.gram w x)⁻¹ * g
    have hg' : projArch D.sp.cm.sig V.gram w g' = 1 := by
      simp [g', x, map_mul, map_inv]
    have hg : g = embArch D.sp.cm.sig V.gram w x * g' := by simp [g']
    rw [hg, map_mul, ContinuousLinearMap.mul_apply]
    exact hP.2 x _ (hcomm g' hg' v hv)
  have hne : P ≠ ⊥ := by
    obtain ⟨y, hyW, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.2.1
    intro hbot
    have hsub : W.subtypeL ∈ homIn δ.π ρ ⊤ := mem_homIn_top.2 fun h z => rfl
    have hm : W.subtypeL ⟨y, hyW⟩ ∈ P := apply_mem_isoPart hsub _
    rw [hbot] at hm
    exact hy0 ((Submodule.mem_bot ℂ).1 hm)
  exact (hπ.irred.2 P hinv).resolve_left hne

end MainStatements.Flath2
end
end

-- Source module: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.CptSt

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace MainStatements.Flath2

theorem cptSt : CptSt := by
  intro hCT D V μ _ _ H _ _ _ π hπ hm f hf
  have c := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  rw [GlobalTheory.AutMult.mCusp_eq_Rcusp, Ne, GlobalTheory.AutMult.multIn_eq_zero_iff] at hm
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hρ := GlobalTheory.Cusp.isUnitaryRep_Rcusp V μ
  have hb0 : GlobalTheory.AutMult.be T T ≠ 0 := fun e => by
    have h := GlobalTheory.AutMult.be_self_pos hπ hρ hT hT0
    rw [e] at h
    simp at h
  have key : ∀ x, T.adjoint (T x) = GlobalTheory.AutMult.be T T • x := fun x =>
    ext_inner_left ℂ fun y => by
      rw [ContinuousLinearMap.adjoint_inner_right, inner_smul_right (𝕜 := ℂ) (E := H)]
      exact GlobalTheory.AutMult.inner_eq_be hπ hρ hT hT x y
  have hcomm : T ∘L repOp π μ f = GlobalTheory.Cusp.RcuspOp V μ f ∘L T :=
    hπ.unitary.comp_repOp hρ c.1 c.2 T hT.2
  have hR : IsCompactOperator (GlobalTheory.Cusp.RcuspOp V μ f) :=
    GlobalTheory.DiscreteSum.isCompactOperator_of_isHilbertSchmidt (hCT D V μ f hf).isHilbertSchmidt
  have hv : ∀ v, T (repOp π μ f v) = GlobalTheory.Cusp.RcuspOp V μ f (T v) := fun v =>
    DFunLike.congr_fun hcomm v
  have e : ⇑(repOp π μ f) =
      (GlobalTheory.AutMult.be T T)⁻¹ • (⇑T.adjoint ∘ (⇑(GlobalTheory.Cusp.RcuspOp V μ f) ∘ ⇑T)) := funext fun v => by
    show repOp π μ f v = (GlobalTheory.AutMult.be T T)⁻¹ • T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v))
    have k : T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v)) = GlobalTheory.AutMult.be T T • repOp π μ f v :=
      (congrArg T.adjoint (hv v)).symm.trans (key (repOp π μ f v))
    calc repOp π μ f v = (GlobalTheory.AutMult.be T T)⁻¹ • (GlobalTheory.AutMult.be T T • repOp π μ f v) :=
          (inv_smul_smul₀ hb0 _).symm
      _ = (GlobalTheory.AutMult.be T T)⁻¹ • T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v)) := congrArg _ k.symm
  rw [e]
  exact ((hR.comp_clm T).clm_comp T.adjoint).smul (GlobalTheory.AutMult.be T T)⁻¹

end MainStatements.Flath2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDSComp

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.PsCo.SpecX

open GlobalTheory GlobalTheory.SpecTraceProof MainStatements.Flath2

theorem hasDSComp (h1 : IrredSt) (h2 : CompSt) : GlobalTheory.Published.DiscreteSeriesClassification →  True → True → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestDataX V lam M T U μa μf μ fa ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → HasDSComp M π := by
  intro hDS hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD H _ _ _ π hπ c hc hc0 τ
  have hRP : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ := hTD.2.2.2.2.1
  have hmem : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w := hTD.2.2.2.2.2.1.mem
  have hfin : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
  obtain ⟨Q, hQ, hrep⟩ := GlobalTheory.T.pureTensorOperator_split_oneRealPlace D V μa μf μ hRP fa ff hmem hfin H π hπ.unitary (placeOf D τ)
  haveI : (μa (placeOf D τ)).IsHaarMeasure := hRP.1 _
  have hcont := continuous_of_mem_ccSmooth (continuous_archCoord _ _ _) (hmem (placeOf D τ))
  have hint : Integrable (fa (placeOf D τ)) (μa (placeOf D τ)) := hcont.integrable_of_hasCompactSupport (hmem _).1
  have hπw : IsUnitaryRep (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) :=
    isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
  have htc : IsTraceClass (repOp (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) (μa (placeOf D τ)) (fa (placeOf D τ)) * Q) := hrep ▸ hc.1
  obtain ⟨W, hW⟩ := h1 _ H _ hπw (repOp (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) (μa (placeOf D τ)) (fa (placeOf D τ))) Q
    (fun S hS => hπw.comp_repOp hπw hcont (hmem _).1 S fun g v => DFunLike.congr_fun (hS g) v) hQ
    (GlobalTheory.DiscreteSum.isCompactOperator_of_isHilbertSchmidt htc.isHilbertSchmidt)
    (fun h0 => hc0 (by rw [← hc.2, hrep, h0]; exact trace_zero))
  obtain ⟨δ, hδ'⟩ := h2 D V H π hπ (placeOf D τ) W hW
  obtain ⟨c', hc', himp⟩ := GlobalTheory.PsCo.Plug.archTrace hDS hHC hPC D V lam S M T U μa μf μ fa ff hTD τ δ.H δ.π δ.isIrr
  by_cases hc'0 : c' = 0
  · exfalso
    haveI := δ.isIrr.complete
    have hc'w : HasTrace (repOp δ.π (μa (placeOf D τ)) (fa (placeOf D τ))) 0 := hc'0 ▸ hc'
    have h0 := GlobalTheory.T.trace_integratedOp_mul_eq_zero_of_isotypic (GArch D.sp.cm.sig V.gram (placeOf D τ)) _ _ hint δ.H H δ.π _ δ.isIrr hπw hδ' Q hQ hc'w htc
    exact hc0 (hc.2.symm.trans (hrep ▸ h0))
  · show IsIsotypic (dsRep M τ) (π.comp (embW V (placeOf D τ)))
    exact GlobalTheory.isIsotypic_of_uEquiv_left (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) (himp hc'0) hδ'

theorem copyFinDS (h1 : IrredSt) (h2 : CompSt) (h4 : AdmSt) : GlobalTheory.Published.DiscreteSeriesClassification →  True → True → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestDataX V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → (∀ f ∈ CcGA V, IsCompactOperator (repOp π μ f)) → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ (GfC V) W), σ.IsIrreducible ∧ IsAdmissible σ ∧ IsCopyFinDS σ M π ⊤ ∧ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c := by
  intro hDS hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD ν hν H _ _ _ π hπ hcp c hc hc0
  have hcomp : HasDSComp M π := hasDSComp h1 h2 hDS hHC hPC D V lam S M T U μa μf μ fa ff hTD H π hπ c hc hc0
  have hU : GlobalTheory.AutomorphicL2Unitary.IsSubrep π ⊤ := GlobalTheory.AutomorphicL2Unitary.isSubrep_top
  have hcopy := GlobalTheory.T.irreducibleUnitaryRep_eq_finiteSmoothPart_tensor_discreteSeries D V S M H π hπ hcomp hU
  have hadm := h4 D V S M μ H π hπ.unitary hcp hU
  have hirr := GlobalTheory.FinPartIrrAdm.irreducible hπ hcomp hU hadm
  haveI : ν.IsHaarMeasure := hν.1
  have hfam : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V ν ff hfam _ (finPartDSSm M hU) hadm
  have hπc' := GlobalTheory.PsCo.Plug.copyTraceT D V lam S M T U μa μf μ fa ff hTD ν hν H π hπ _ (finPartDSSm M hU) hirr hadm hcopy c' hc'
  have hcc : c' = c := hπc'.2.symm.trans hc.2
  subst hcc
  exact ⟨_, _, _, finPartDSSm M hU, hirr, hadm, hcopy, hc'⟩

theorem specTrace (h1 : IrredSt) (h2 : CompSt) (h3 : CptSt) (h4 : AdmSt) : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → True → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTermX → True → SpecTraceX := by
  intro hDSC tc hChar hCO hPCT hPCS
  intro D V lam S M T U μa μf μ _ _ fa ff hTD ν hν n Ws _ _ σs hIrr hcover c hc
  have hcusp := GlobalTheory.PsCo.Plug.cuspOpT hCO hPCT D V lam S M T U μa μf μ fa ff hTD
  have hpone := copyFinDS h1 h2 h4 hDSC hChar hPCS D V lam S M T U μa μf μ fa ff hTD ν hν
  refine ⟨hcusp.traceClass, ?_⟩
  refine GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching (UDual (GA D V)) n (fun x => (mCusp V μ x.rep.π).toNat)
    (fun x => repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) (fun i => (mCuspDS μ (σs i) M).toNat) c
    (fun x i => IsCopyFinDS (σs i) M x.rep.π ⊤) _ hcusp.hasSum_trace ?_ ?_ ?_ ?_ ?_
  ·
    intro x hm ht
    have hm' : mCusp V μ x.rep.π ≠ 0 := fun h => hm (by rw [h]; simp)
    have htr : HasTrace (repOp x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff))
        (repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) := ⟨hcusp.traceClass_rep x hm', rfl⟩
    obtain ⟨W, _, _, σ, hσi, hσa, hcopy, hσt⟩ := hpone x.rep.H x.rep.π x.rep.isIrr
      (h3 tc D V μ x.rep.H x.rep.π x.rep.isIrr hm') _ htr ht
    have hmσ : mCuspDS μ σ M ≠ 0 := by
      rwa [← GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel D V S M μ x.rep.H x.rep.π x.rep.isIrr W σ hσi hσa hcopy]
    obtain ⟨i, ⟨f⟩⟩ := hcover W σ hσi hσa hmσ (not_isIntegralOp_zero hσt ht)
    exact ⟨i, isCopyFinDS_of_equiv f hcopy⟩
  ·
    intro i hi
    have hi' : mCuspDS μ (σs i) M ≠ 0 := fun h => hi (by rw [h]; simp)
    obtain ⟨H, _, _, π, hπ, hcopy⟩ := GlobalTheory.T.exists_irreducibleUnitary_completion_finiteTimesDS D V S M μ (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi'
    let R : IrrU (GA D V) := ⟨H, π, hπ⟩
    refine ⟨R.cl, isCopyFinDS_of_uEquiv ?_ hcopy⟩
    exact (IrrU.cl_eq_iff.1 (UDual.cl_rep R.cl)).symm
  ·
    intro x i hR
    refine ⟨?_, ?_⟩
    · rw [GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel D V S M μ x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hR]
    · exact (GlobalTheory.PsCo.Plug.copyTraceT D V lam S M T U μa μf μ fa ff hTD ν hν x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i)
        (hIrr.1 i) (hIrr.2.1 i) hR (c i) (hc i)).2
  ·
    intro x i j hi hj
    by_contra hne
    have e := (GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi
      x.rep.H x.rep.π x.rep.isIrr (Ws j) (σs j) (hIrr.1 j) (hIrr.2.1 j) hj).1 (UEquiv.refl _)
    exact (hIrr.2.2 i j hne).false e.some
  ·
    intro x y i hx hy
    have e := (GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hx
      y.rep.H y.rep.π y.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hy).2 ⟨Representation.Equiv.refl _⟩
    rw [← UDual.cl_rep x, ← UDual.cl_rep y]
    exact IrrU.cl_eq_iff.2 e

theorem main : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.TrMult.SpecTraceX :=
  fun ds tc => specTrace irredSt compSt cptSt admissible_representation_factorisation ds tc trivial (GlobalTheory.T.cuspidalOperators_vanishingRadicalIntegrals_unitaryGroup tc) GlobalTheory.PsCo.Plug.parabolicT trivial

end GlobalTheory.PsCo.SpecX

end
end
end
