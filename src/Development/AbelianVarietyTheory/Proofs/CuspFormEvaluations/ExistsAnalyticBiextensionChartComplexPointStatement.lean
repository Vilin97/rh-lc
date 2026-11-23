module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameExponentialJetsIsChartStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameAdjointnessSeriesTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameFirstPartialLawTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSecondPartialLawTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSymmetryTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticLineBundleFrameEqAppellHumbertStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJetsStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorJetReadingStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorJetReadingStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNormalisedIsoReadingOneAnalyticFrameStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsValueAtJetPointCmFrameSection
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameExponentialImmersionAtOrigin

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameImm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

section Group

variable {g : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}

theorem deriv_one (h0 : e 0 = (1 : Over.mk y ⟶ G).left) : IsDerivAt0 e 0 (1 : epsPt y ⟶ G).left := by
  let φ : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have h1 : (1 : epsPt y ⟶ G).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 := by
    rw [h0, ← MonObj.comp_one φ]
    rfl
  have h2 : spMap GlobalTheory.TangentOrigin.fstC ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 = e 0 := by
    rw [← Category.assoc, GlobalTheory.FrameTangent.spMap_comp']
    have : GlobalTheory.TangentOrigin.fstC.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ :=
      RingHom.ext fun r => by simp
    rw [this]
    simp [spMap]
  rw [h1, GlobalTheory.PointUnif.isDerivAt0_iff]
  refine ⟨h2, fun U hU f => ?_⟩
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := h2 ▸ (GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hU
  rw [GlobalTheory.TangentOrigin.evalPt_spMap_comp _ _ U hU0 hU, map_zero]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem deriv_list (h0 : e 0 = (1 : Over.mk y ⟶ G).left) :
    ∀ (m : ℕ) (w : Fin m → Fin g → ℂ) (v : Fin m → (epsPt y ⟶ G)), (∀ i, IsDerivAt0 e (w i) (v i).left) →
      IsDerivAt0 e (∑ i, w i) (List.ofFn v).prod.left
  | 0, w, v, _ => by simpa using deriv_one h0
  | m + 1, w, v, h => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
    exact GlobalTheory.PointUnif.deriv_mul h0 (h 0) (deriv_list h0 m _ _ fun i => h i.succ)

end Group

theorem anPt_imm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm := by
  classical
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ w hw
  by_contra hcon
  push Not at hcon
  apply hw
  have he0 : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)
  have h0 : (fun z => (Φ.e z).left) 0 = (1 : Over.mk y.x ⟶ Xo.univ.t.G).left := congrArg (·.left) he0
  have d0 := deriv_one (e := fun z => (Φ.e z).left) h0
  have dw : IsDerivAt0 (fun z => (Φ.e z).left) w (1 : epsPt y.x ⟶ Xo.univ.t.G).left := by
    refine ⟨d0.1, fun U hU f => (d0.2 U hU f).trans ?_⟩
    rw [map_zero]
    refine (hcon U f ?_).symm
    have h3 := (GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hU
    exact (congrArg (fun p : Sp ℂ ⟶ Xo.univ.t.G.left => ⊤ ≤ p ⁻¹ᵁ U) d0.1).mp h3
  let q := (Fintype.equivFin (Lt1 Dw)).symm
  have key : ∀ w' : Fin g → ℂ, IsDerivAt0 (fun z => (Φ.e z).left) w' (1 : epsPt y.x ⟶ Xo.univ.t.G).left →
      IsCombAt y.x (m := Fintype.card (Lt1 Dw)) (fun i => y.u (q i).1 (q i).2) (fun i => w' (el.symm (q i)))
        (1 : epsPt y.x ⟶ Xo.univ.t.G).left := by
    intro w' hw'
    let v : Fin (Fintype.card (Lt1 Dw)) → (epsPt y.x ⟶ Xo.univ.t.G) := fun i =>
      GlobalTheory.FrameTangent.smT y.x (w' (el.symm (q i)))
        (GlobalTheory.FrameTangent.ovT (t := Xo.univ.t) (y.tan (q i).1 (q i).2))
    refine ⟨v, fun i => rfl, GlobalTheory.PointUnif.deriv_unique ?_ hw'⟩
    have hs : w' = ∑ i, w' (el.symm (q i)) • (Pi.single (el.symm (q i)) 1 : Fin g → ℂ) := by
      exact (pi_eq_sum_univ' w').trans
        (Equiv.sum_comp (q.trans el.symm) (fun j => w' j • (Pi.single j 1 : Fin g → ℂ))).symm
    have := deriv_list (e := fun z => (Φ.e z).left) h0 _
      (fun i => w' (el.symm (q i)) • (Pi.single (el.symm (q i)) 1 : Fin g → ℂ)) v
      fun i => GlobalTheory.PointUnif.deriv_smul (Φ.der (q i)) _
    rwa [← hs] at this
  have ht : IsTanAt y.x (1 : epsPt y.x ⟶ Xo.univ.t.G).left := ⟨Over.w _, d0.1.trans h0⟩
  have hu := (GlobalTheory.FrameTangent.frame_tangent_basis E H Dw l Xo c ℂ y _ ht).unique
    (y₁ := fun ℓ => w (el.symm ℓ)) (y₂ := fun ℓ => (0 : Fin g → ℂ) (el.symm ℓ)) (key w dw) (key 0 d0)
  funext j
  simpa using congrFun hu (el j)

end GlobalTheory.FrameImm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameExponentialImmersionAtOriginStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.analyticFrame_exponential_immersion_at_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm := by
  first | exact @GlobalTheory.FrameImm.anPt_imm | exact GlobalTheory.FrameImm.anPt_imm | (intros; apply GlobalTheory.FrameImm.anPt_imm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticFrameJetPairIsAnE

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem jetMap_psum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el) (n m : ℕ) (xs : Fin n → (jO y g m n ⟶ Xo.univ.t.G))
    (Λ : Fin n → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hx : ∀ i, Φ.toAnFr.JetMap m (xs i).left (Λ i))
    (I : Finset (Fin n)) :
    Φ.toAnFr.JetMap m (psum Xo.univ.t.G xs I).left (∑ i ∈ I, Λ i) := by
  obtain ⟨-, h1, hmul, -⟩ := GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ n m
  have key : ∀ L : List (Fin n), Φ.toAnFr.JetMap m
      (L.foldr (fun k acc => padd Xo.univ.t.G (xs k) acc) (pzero Xo.univ.t.G (jO y g m n))).left
      (L.map Λ).sum := by
    intro L
    induction L with
    | nil => exact h1
    | cons k L ih => exact (hmul _ _ _ _ (hx k) ih).1
  have hs : (((List.finRange n).filter (fun x => decide (x ∈ I))).map Λ).sum = ∑ i ∈ I, Λ i := by
    rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
    congr 1
    ext i
    simp
  rw [← hs]
  exact key _

theorem exists_isAnE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∃ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ
  have h : ∀ m, ∃ τ : FrTy y g Φ.jx m, τ.IsGen ∧ Φ.toAnFr.JetRd m
      (cφ ![jpt y g Φ.jx m (0 : Fin 2), jpt y g Φ.jx m (1 : Fin 2)]) (cε 2) τ (psumL 2 g) := by
    intro m
    refine GlobalTheory.T.exists_generator_jet_reading _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr 2 m _
      (cφ ![jpt y g Φ.jx m (0 : Fin 2), jpt y g Φ.jx m (1 : Fin 2)]) (cε 2) (psumL 2 g) ?_
    intro I
    refine jetMap_psum Φ 2 m _ (fun i => LinearMap.proj i) ?_ I.down
    have h0 := (GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ 2 m).1
    intro i
    fin_cases i
    · exact h0 0
    · exact h0 1
  choose e he using h
  exact ⟨e, he⟩

end GlobalTheory.AnVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticFrameJetPairIsAnEStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_analyticFrame_jetPair_isAnE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∃ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e := by
  first | exact @GlobalTheory.AnVal.exists_isAnE | exact GlobalTheory.AnVal.exists_isAnE | (intros; apply GlobalTheory.AnVal.exists_isAnE <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsValueAtJetPointCmFrameSectionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isValueAt_jetPoint_cmFrame_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (m k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.Rd k F θ → Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → ∃ F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y g m 1)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y g m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧ IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (Φ.jx m) τ (toΓ _ (jetOf m θ)) := by
  first | exact @GlobalTheory.JetVal.isValueAt_jetPt | exact GlobalTheory.JetVal.isValueAt_jetPt | (intros; apply GlobalTheory.JetVal.isValueAt_jetPt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticBiextensionChartComplexPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] [StarRing (𝓞 E)] {y : FrPt Xo c ℂ} {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem isFrame_of_isAnE (hst : ∀ a : 𝓞 E, star a = H.bar a) (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) :
    IsFrame y g Φ.jx (anFB ty).G.F (anFB ty).A.act (anFB ty).ph1 (anFB ty).ph2 (anFB ty).sy (anFB ty).ad e := by
  have hI := GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ
  exact ⟨fun m => (he m).1, GlobalTheory.T.analyticFrame_first_partial_law_trivial E H Dw l Xo c y g ty el Φ hI e he,
    GlobalTheory.T.analyticFrame_second_partial_law_trivial E H Dw l Xo c y g ty el Φ hI e he, GlobalTheory.T.analyticFrame_symmetry_trivial E H Dw l Xo c y g ty el Φ hI e he,
    GlobalTheory.T.analyticFrame_adjointness_series_trivial E H Dw l Xo c y g ty el Φ hI hst e he⟩

theorem isGerm_tay_of_rd (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (wP : PrimTy H Xo) (hw : IsPrim wP) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ)
    (hF : Φ.toAnFr.Rd k F θ) : IsGerm y g Φ.jx (anFB ty).A.act e wP k F (tay θ 0) := by
  simp only [IsGerm]
  intro m
  have hJ : Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) :=
    (GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ 1 m).2.2.2.2
  obtain ⟨τ, -, hτ⟩ := GlobalTheory.T.exists_generator_jet_reading _ _ _ _ _ Φ.toAnFr 1 m (Fin 1) (fun _ => (Φ.jx m).left) (fun _ => (k : ℤ))
    (fun _ => LinearMap.proj 0) (fun _ => hJ)
  obtain ⟨F', hpull, hval⟩ := GlobalTheory.T.isValueAt_jetPoint_cmFrame_section E H Dw l Xo c y g ty el Φ m k F θ τ hF hτ
  have hc := (GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert E H Dw l Xo c y g ty el Φ (GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ) e wP he hw).1 m k τ hτ
  exact ⟨F', τ, hpull, hc, hval⟩

noncomputable def AnPt.chartOf (hst : ∀ a : 𝓞 E, star a = H.bar a) (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e)
    (wP : PrimTy H Xo) (hw : IsPrim wP) : ChartAt Xo c y where
  d := g
  B := anFB ty
  uvec := anUvec el
  x := Φ.jx
  e := e
  wP := wP
  h := 0
  chart := GlobalTheory.T.cmFrame_exponential_jets_isChart E H Dw l Xo c y g ty el Φ
  frame := isFrame_of_isAnE Φ hst e he
  prim := hw
  gauge := anFB_canon ty
  rig0 := (GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert E H Dw l Xo c y g ty el Φ (GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ) e wP he hw).2

end

theorem rename_cast_refl {g : ℕ} (f : MvPowerSeries (Fin 1 × Fin g) ℂ) :
    MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) f = f := by
  have h : (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) = id := funext fun p => rfl
  rw [h]
  exact MvPowerSeries.rename_id_apply f

theorem exists_analytic_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∀ a : 𝓞 E, star a = H.bar a) → ∃ (C : ChartAt Xo c y) (hd : C.d = g), C.h = 0 ∧ (∀ i, C.B.G.F i = (MvPowerSeries.X (R := ℂ) ((0 : Fin 2), i) + MvPowerSeries.X (R := ℂ) ((1 : Fin 2), i))) ∧ (∀ (ℓ : Lt1 Dw) (i' : Fin C.d), C.uvec ℓ i' = if Fin.cast hd i' = el.symm ℓ then 1 else 0) ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ), Φ.toAnFr.Rd k F θ → IsGerm y C.d C.x C.B.A.act C.e C.wP k F (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast hd.symm p.2)) (tay θ 0)) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hst
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_analyticFrame_jetPair_isAnE E H Dw l Xo c y g ty el Φ
  obtain ⟨wP, hw⟩ := (GlobalTheory.T.exists_normalisedIso_reading_one_analyticFrame E H Dw l Xo c y g ty el Φ).1
  refine ⟨AnPt.chartOf Φ hst e he wP hw, rfl, rfl, ?_, ?_, ?_⟩
  · intro i
    first
      | rfl
      | simp [AnPt.chartOf, anFB, Germ.FB.triv, addFGLaw]
  · intro ℓ i'
    first
      | rfl
      | simp [AnPt.chartOf, anUvec, Pi.single_apply, eq_comm]
      | (simp only [AnPt.chartOf, anUvec]; done)
  · intro k F θ hF
    show IsGerm y g Φ.jx (anFB ty).A.act e wP k F
      (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) (tay θ 0))
    rw [rename_cast_refl]
    exact isGerm_tay_of_rd Φ e he wP hw k F θ hF

end GlobalTheory.AnVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticBiextensionChartComplexPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_analytic_biextension_chart_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∀ a : 𝓞 E, star a = H.bar a) → ∃ (C : ChartAt Xo c y) (hd : C.d = g), C.h = 0 ∧ (∀ i, C.B.G.F i = (MvPowerSeries.X (R := ℂ) ((0 : Fin 2), i) + MvPowerSeries.X (R := ℂ) ((1 : Fin 2), i))) ∧ (∀ (ℓ : Lt1 Dw) (i' : Fin C.d), C.uvec ℓ i' = if Fin.cast hd i' = el.symm ℓ then 1 else 0) ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ), Φ.toAnFr.Rd k F θ → IsGerm y C.d C.x C.B.A.act C.e C.wP k F (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast hd.symm p.2)) (tay θ 0)) := by
  first | exact @GlobalTheory.AnVal.exists_analytic_chart | exact GlobalTheory.AnVal.exists_analytic_chart | (intros; apply GlobalTheory.AnVal.exists_analytic_chart <;> assumption)
end
end
