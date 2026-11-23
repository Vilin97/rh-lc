module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharacterTrivialOnPrincipalLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvalAtNeZero
public import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGroupOfCongruent
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDominantWeightCuspSectionsNoCommonZeroStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemHolSubIff
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanLeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestriction
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlueIntegralDecompositionsOverRationalPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsOnePlaceStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionFamilyNoCommonZeroLargeWeight

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanFamily



theorem holSub0_le_span_cuspA_of_lastPos : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos (T.Q.Dw j) a →
    4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n →
    Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤
      Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j a n : Set (T.R j))) := by
  intro D T h j hj σ hσ a n hdom hlast hn
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  obtain ⟨hrk, hM⟩ := h.modelW j hj σ hσ
  have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (T.U j s)) hr h.pins.2.1.2
    (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj s hs)) σ hσ
    (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
    (fun k => GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore h.toLawsM j hj σ hσ k)
    a n hdom hlast hn
    (fun k => h.chiTriv j hj σ hσ a n hdom k)
  intro P hP
  exact key ⟨hP.1, hP.2⟩

theorem exists_complex_point {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) (I : Ideal A) (hI : I ≠ ⊤) : ∃ ψ : A →ₐ[K] CAt σ, ∀ x ∈ I, ψ x = 0 := by
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hI
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let _ : Algebra K ℂ := σ.toAlgebra
  let κ : (A ⧸ M) →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨κ.comp (Ideal.Quotient.mkₐ K M), fun x hx => ?_⟩
  show κ (Ideal.Quotient.mk M x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]

theorem evR_of_frMap {D : D7} (T : CoreJ D) (h : LawsJ T) {j : ℕ} (hj : Formalism.L2.Pj.InR D j) (f : T.R j)
    (hf : IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra T.Q.c.F S] (p : TRing T.Q.c.F) (ψ : p.R →ₐ[T.Q.c.F] S)
    (y : FrPt (T.Q.Xo j) T.Q.c p.R) (z : FrPt (T.Q.Xo j) T.Q.c S) (hz : FrMap ψ y z) :
    evR (T.Q.Xo j) T.Q.c f z = ψ (f p y) := by
  have hT : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) z :=
    ⟨p, ψ, y, hz⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact h.evalWD j hj f hf S _ p _ ψ _ y z hT.choose_spec.choose_spec.choose_spec hz


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem exists_family : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c), Dom b m ∧ (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) ∧ (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) ∧ ∀ P ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n), ∀ i, P * rdU (T.U j σ) (t i) ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (a + b) (n + m) : Set (Rul (T.Q.Xo j) T.Q.c))) := by
  intro D T h j hj σ hσ a n hdom
  obtain ⟨b, m, hbm, hlast, hm, hnz⟩ := GlobalTheory.T.exists_dominantWeight_cuspSections_noCommonZero D T h j hj σ hσ
  haveI : FiniteDimensional T.Q.c.F (T.cuspA j b m) := h.cuspFD j hj b m hbm
  haveI : Module.Free T.Q.c.F (T.cuspA j b m) := Module.Free.of_divisionRing _ _
  let B := Module.finBasis T.Q.c.F (T.cuspA j b m)
  have hsec : ∀ i, (B i : T.R j) ∈ sec (T.Q.Xo j) T.Q.c b m := fun i => cusp_le_sec _ _ _ _ _ (B i).2
  refine ⟨b, m, _, fun i => (B i : T.R j), hbm, hsec, ?_, ?_⟩
  · intro p y
    by_contra hne
    have hL := (GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c).1
    obtain ⟨ψ, hψ⟩ := exists_complex_point σ _ hne
    obtain ⟨z, hz⟩ := hL.bc p.R (CAt σ) ψ y
    have hz0 : ∀ i, evR (T.Q.Xo j) T.Q.c (B i : T.R j) z = 0 := fun i => by
      rw [evR_of_frMap T h hj _ (hsec i).1 p ψ y z hz]
      exact hψ _ (Ideal.subset_span ⟨i, rfl⟩)
    haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
    obtain ⟨k, x, t, ht⟩ := (h.unf j hj σ hσ).2.2.1 z
    have hx0 : ∀ i, rdU (T.U j σ) (B i : T.R j) k x.1 = 0 := fun i => by
      have hw := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hsec i) t _ z ht
      rw [hz0 i] at hw
      have hu : wchar (ex (T.Q.Dw j) b m) t ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun c _ => pow_ne_zero _ (t c).ne_zero
      have h0 := (mul_eq_zero.1 hw.symm).resolve_left hu
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2]
      exact congrArg toC h0
    let ev : FDSec (T.U j σ).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k x.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hall : ∀ f ∈ T.cuspA j b m, rdU (T.U j σ) f k x.1 = 0 := by
      intro f hf
      have key : ∀ g : T.cuspA j b m, g ∈ Submodule.span T.Q.c.F (Set.range B) →
          rdU (T.U j σ) (g : T.R j) k x.1 = 0 := by
        intro g0 hg0
        induction hg0 using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨i, rfl⟩ := hg
          exact hx0 i
        | zero => rw [Submodule.coe_zero, map_zero]; rfl
        | add g g' _ _ hg hg' =>
          rw [Submodule.coe_add, map_add (f := _), Pi.add_apply, Pi.add_apply, hg, hg', add_zero]
        | smul c g _ hg =>
          rw [Submodule.coe_smul, map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hg, smul_zero]
      exact key ⟨f, hf⟩ (B.mem_span _)
    have hle : Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j b m : Set (T.R j))) ≤ LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hall f hf
    obtain ⟨P, hP, hPx⟩ := hnz k x.1 x.2
    exact hPx (hle (holSub0_le_span_cuspA_of_lastPos D T h j hj σ hσ b m hbm hlast hm hP))
  · intro P hP i
    have hrd : rdU (T.U j σ) (B i : T.R j) ∈ holSub (T.U j σ).X (laU (T.U j σ) b m) :=
      ((mem_cusp _ _ _ _ _ _).1 (B i).2).2 σ hσ
    have hdab : Dom (a + b) (n + m) := ⟨fun τ => (hdom.1 τ).add (hbm.1 τ), hdom.2.add hbm.2⟩
    have hprod : P * rdU (T.U j σ) (B i : T.R j) ∈
        Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) (a + b) (n + m)) := by
      refine ⟨?_, fun k x hx => by simp [hP.2 k x hx]⟩
      have hP1 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 hP.1
      have hr1 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 hrd
      refine (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).2 fun k => ?_
      rw [show laU (T.U j σ) (a + b) (n + m) k = laU (T.U j σ) a n k + laU (T.U j σ) b m k from
        GlobalTheory.CuspProduct.laU_add (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) a b n m hdom.2 hbm.2 k]
      exact (siegelSpaceAlgebra_holds (E := D.host.E) D.R.r _ _ _ 0).2.1 _ (hP1 k) _ (hr1 k).1
    have hlast' : LastPos (T.Q.Dw j) (a + b) := fun τ hτ hm0 =>
      lt_of_lt_of_le (hlast τ hτ hm0) (by simp)
    have hs := holSub0_le_span_cuspA_of_lastPos D T h j hj σ hσ (a + b) (n + m) hdab hlast' (by omega) hprod
    exact Submodule.span_mono (Set.image_mono (cusp_le_sec _ _ _ _ _)) hs

end GlobalTheory.SpanFamily
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionFamilyNoCommonZeroLargeWeightStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_section_family_no_common_zero_large_weight : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c), Dom b m ∧ (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) ∧ (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) ∧ ∀ P ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n), ∀ i, P * rdU (T.U j σ) (t i) ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (a + b) (n + m) : Set (Rul (T.Q.Xo j) T.Q.c))) := by
  first | exact @GlobalTheory.SpanFamily.exists_family | exact GlobalTheory.SpanFamily.exists_family | (intros; apply GlobalTheory.SpanFamily.exists_family <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedCuspidalHolomorphicLeSpanAlgebraicCuspSec

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.SmallWtSpan

theorem holSub0_le_span_cuspSec : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ w : WeightFamilies.Wt D j, w.LastPos → 0 < w.n → holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n)}) := by
  intro D T hT j hj σ hσ w hw hn P hP
  have hdom := dom_wtA w
  obtain ⟨b, m, N, t, hbm, ht, hunit, hprod⟩ := GlobalTheory.T.exists_section_family_no_common_zero_large_weight D T hT j hj σ hσ _ _ hdom
  have hP' := Submodule.mem_inf.mp hP
  have h2 := GlobalTheory.GlueSpan.span_of_products D T hT j hj σ hσ _ b _ m N t hdom hbm ht hunit P hP'.2
    (fun i => hprod P hP i)
  exact GlobalTheory.T.holomorphic_sections_span_le D T hT j hj σ hσ w hw hn (Submodule.mem_inf.mpr ⟨hP, h2⟩)

end GlobalTheory.SmallWtSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedCuspidalHolomorphicLeSpanAlgebraicCuspSecStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.boundedCuspidalHolomorphic_le_span_algebraicCuspSections : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ w : WeightFamilies.Wt D j, w.LastPos → 0 < w.n → holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n)}) := by
  first | exact @GlobalTheory.SmallWtSpan.holSub0_le_span_cuspSec | exact GlobalTheory.SmallWtSpan.holSub0_le_span_cuspSec | (intros; apply GlobalTheory.SmallWtSpan.holSub0_le_span_cuspSec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormRationalDescentToBase

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.CoverDescRat



theorem mu_mul_level_of_tie (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (hJ : LawsJ T) (hlev : R.toLevCh.Is A.μ0) (hT : TieIn T R κ v₀) (j : Fin D.R.m) :
    ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, T.mu ((j : ℕ) + 1) T.σ₀ (g * k) = T.mu ((j : ℕ) + 1) T.σ₀ g := by
  intro k hk g
  have hj := inR j
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨τ, hτ⟩ := GlobalTheory.MuLevel.exists_ext (L := D.what₂.LL) T.σ₀
  obtain ⟨hf, hk'⟩ := (hJ.levelK _ hj _ hσ k).1 hk
  have hodd : Odd (D.host.g 0 * D.host.g 1) := hJ.pins.2.1.1 ▸ T.Q.l.odd
  obtain ⟨y, hy, hu, hc⟩ := GlobalTheory.MuLevel.exists_root_of_level _ _ hodd k hf hk'
  have hm := R.C.isMu0 j
  have h1 : R.mu0 ((j : ℕ) + 1) y = 1 := by
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ _ (hlev.mu0 j) hm.tame _
      (fun P hP => hm.unr P fun a ha => hP ?_) y hu hc
    rw [Nat.cast_mul]
    fin_cases a
    · exact Ideal.mul_mem_right _ _ ha
    · exact Ideal.mul_mem_left _ _ ha
  have hg : GoodEmb T.Q.c (τ.comp (algebraMap T.Q.c.F D.what₂.LL)) := hτ ▸ hσ
  obtain ⟨z, hz1, hz2⟩ := (hT.chiR j τ hg).2.2.2.1 y hu.1
  have h2 : algebraMap T.Q.c.F D.what₂.LL z = 1 :=
    D.what₂.embLL.injective (by rw [← hz1, h1, map_one, Circle.coe_one])
  have hχ : T.chiW ((j : ℕ) + 1) T.σ₀ y = 1 := by
    rw [hτ] at hz2
    apply Subtype.ext
    rw [hz2, h2, map_one, Circle.coe_one]
  have hMV := hJ.muVal _ hj _ hσ
  obtain ⟨x, hx⟩ := hMV.1 g
  have hxy : IsDetRoot _ (g * k) (x * y) := (GlobalTheory.Member.isDetRoot_laws D _).2.2.2 g k x y hx hy
  rw [hMV.2 _ _ hxy, hMV.2 g x hx, map_mul, hχ, mul_one]



theorem cover_desc_rat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ φ ∈ C.ratForms (wtA (κ i)) (κ i).n, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) ∧ φ = ∑ a, C.σ₂ (x a) • ψ a := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hJ hlev _ _ _ _ hT i _ hV _ l _ C hC hP φ hφ hinv
  have hn : 0 < (κ i).n := by
    obtain ⟨t⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
    rw [(hT.kap i t).2.2]
    unfold Ranks.nV
    have := D.R.t_odd.pos
    omega
  exact GlobalTheory.CoverFormDesc.cover_form_desc D T hJ ((i : ℕ) + 1) (inR i) T.σ₀ T.toCore.good_σ₀ C hC.1 (wtA (κ i)) (κ i).n (dom_wtA (κ i)) hP
    (GlobalTheory.T.boundedCuspidalHolomorphic_le_span_algebraicCuspSections D T hJ ((i : ℕ) + 1) (inR i) T.σ₀ T.toCore.good_σ₀ (κ i) (GlobalTheory.AdTh.lastPos_of_kapIs hT.kap i) hn)
    (mu_mul_level_of_tie D G Pl0 T0 A T R κ v₀ hJ hlev hT i) φ hφ hinv

end GlobalTheory.CoverDescRat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormRationalDescentToBaseStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coverForm_rational_descent_to_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ φ ∈ C.ratForms (wtA (κ i)) (κ i).n, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) ∧ φ = ∑ a, C.σ₂ (x a) • ψ a := by
  first | exact @GlobalTheory.CoverDescRat.cover_desc_rat | exact GlobalTheory.CoverDescRat.cover_desc_rat | (intros; apply GlobalTheory.CoverDescRat.cover_desc_rat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsTowerCover

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DescIntRoad

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
  Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem descIntAt_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.DescIntAt T i (κ i) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin S hO hU φ hφ hk
  obtain ⟨m, x, ψ, hψ, e⟩ := GlobalTheory.T.coverForm_rational_descent_to_base D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin φ
    (C.intForms_subset _ _ S hφ) hk
  refine GlobalTheory.T.glue_integral_decompositions_over_rationalPrime D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin S hO hU φ hφ hk m x ψ hψ e
    fun la hla => ?_
  have hsub : C.intForms (wtA (κ i)) (κ i).n S ⊆ C.intForms (wtA (κ i)) (κ i).n {la} :=
    Set.image_mono fun _ hf => ⟨hf.1, fun la' h => hf.2 la' (by rw [Set.mem_singleton_iff.1 h]; exact hla)⟩
  exact GlobalTheory.T.unramified_descent_integral_forms_one_place D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin la (hO la hla)
    (fun la' h => hU la' (by rw [Set.mem_singleton_iff.1 h]; exact hla)) φ (hsub hφ) hk m x ψ hψ e

end GlobalTheory.DescIntRoad
end
end
end
