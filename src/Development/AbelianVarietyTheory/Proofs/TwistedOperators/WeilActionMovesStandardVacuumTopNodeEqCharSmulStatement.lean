module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitEmbeddingValuedEqIntValuationInteger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceChartFiniteAdeleTensorLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTupleHeckeCharacterDetIdeleEqProdLocalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacePartFixesStandardVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusConjLevelDetEqOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.DetIdeleUnit

open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem val_eq_one_of_le {a b : WithZero (Multiplicative ℤ)} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 :=
  le_antisymm ha (by
    calc (1 : WithZero (Multiplicative ℤ)) = a * b := h.symm
      _ ≤ a := mul_le_of_le_one_right' hb)

theorem valued_isInt {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Fv D.host.F v}
    (h : GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) x) : Valued.v x ≤ 1 := by
  obtain ⟨o, rfl⟩ := h
  exact o.2

theorem chart_val_eq_one {es : AE D} {PP : Pl D.host.E} (he : IsIdemAt es PP) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart es v π) {c c' : AE D} (hcc : c * c' = 1)
    (hc : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : Valued.v (π c) = 1 := by
  obtain ⟨φ, hφ, hint, -⟩ := GlobalTheory.ChartLevels.chart_levels D es PP v π he hπ
  have hc' : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c')) = 1 := by
    have h1 : GlobalTheory.StdFrames.cpt PP (toEAf D c) * GlobalTheory.StdFrames.cpt PP (toEAf D c') = 1 := by
      rw [← map_mul, ← map_mul, hcc, map_one, map_one]
    have h2 := congrArg Valued.v h1
    rw [map_mul, hc, one_mul, map_one] at h2
    exact h2
  have key : ∀ y : AE D, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D y)) = 1 → Valued.v (π y) ≤ 1 := by
    intro y hy
    rw [← hφ]
    refine valued_isInt ((hint _).1 ((GlobalTheory.AdIsom.mem_OA _).2 fun Q => ?_))
    rw [map_mul]
    by_cases hQ : Q = PP
    · subst hQ; rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).1, one_mul, hy]
    · rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 Q hQ, zero_mul, map_zero]; exact zero_le'
  refine val_eq_one_of_le (key c hc) (key c' hc') ?_
  rw [← map_mul, ← map_mul, hcc, map_one, map_one]

theorem absFin_single {es : AE D} {PP : Pl D.host.E} (he : IsIdemAt es PP) (u : (AE D)ˣ) (c : AE D)
    (hu : (u : AE D) = es * c + (1 - es)) (c' : AE D) (hcc : c * c' = 1)
    (hc : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D u = 1 := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart es he.1
  have hee : es * es = es := he.1.1
  have hu1 : (1 - es) * (u : AE D) = 1 - es := by rw [hu]; linear_combination (1 - c) * hee
  rw [GlobalTheory.SplitLinear.absFin_split D es v π he.1 hπ u hu1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  have hπu : π (u : AE D) = π c := by
    rw [hu, map_add (f := _), map_mul, map_sub, map_one, hπ.map_e hee, one_mul, sub_self, add_zero]
  change ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v (π (u : AE D)))) = 1
  rw [hπu, chart_val_eq_one he hπ hcc hc, WithZero.log_one, zpow_zero]

theorem absFin_idemSum_eq_one {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (x : (AE D)ˣ) (c c' : AE D)
    (hcc : c * c' = 1) (hx : (x : AE D) = e * c + (1 - e))
    (hc : ∀ PP ∈ P, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = 1 := by
  obtain ⟨⟨es, hes, hae⟩, -⟩ := he
  let u : {PP // PP ∈ P} → (AE D)ˣ := fun PP =>
    { val := es PP.1 * c + (1 - es PP.1)
      inv := es PP.1 * c' + (1 - es PP.1)
      val_inv := GlobalTheory.SplitIdeleModulus.unit_aux (hes PP.1 PP.2).1.1 hcc
      inv_val := GlobalTheory.SplitIdeleModulus.unit_aux (hes PP.1 PP.2).1.1 (by rw [mul_comm]; exact hcc) }
  have hx' : x = ∏ PP ∈ P.attach, u PP := by
    apply Units.ext
    rw [hx, Units.coe_prod]
    change _ = ∏ PP ∈ P.attach, (fun PP => es PP * c + (1 - es PP)) PP.1
    rw [Finset.prod_attach P (fun PP => es PP * c + (1 - es PP)),
      GlobalTheory.SplitIdeleModulus.prod_idem hes _ P subset_rfl, hae]
  let A : (AE D)ˣ →* ℝ := ⟨⟨GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D, GlobalTheory.SplitIdeleModulus.absFin_one'⟩, GlobalTheory.SplitLinear.absFin_mul⟩
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = A x := rfl
  rw [hA, hx', map_prod]
  exact Finset.prod_eq_one fun PP _ => absFin_single (hes PP.1 PP.2) (u PP) c rfl c' hcc (hc PP.1 PP.2)

end GlobalTheory.DetIdeleUnit

open GlobalTheory.FunObj in
theorem GlobalTheory.DetIdeleUnit.cpt_gdet_kapAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
  ((gdet (GlobalTheory.TopLevelInv.kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) = GlobalTheory.StdFrames.cpt w ((finG (G.V (.top (j + 1))) k).val.det) := by
  have hu : IsUnit ((S.βp (j + 1)).val.det) := (Matrix.GeneralLinearGroup.det (S.βp (j + 1))).isUnit
  have ha : ((S.βp (j + 1)).val.map (GlobalTheory.StdFrames.cpt w)).det ≠ 0 := by
    intro h0; apply (hu.map (GlobalTheory.StdFrames.cpt w)).ne_zero; rw [RingHom.map_det]; exact h0
  unfold GlobalTheory.TopLevelInv.kapAt inBasis
  simp [gdet, GlobalTheory.StepData.reGL, Matrix.GeneralLinearGroup.det, GlobalTheory.StdFrames.loc, RingHom.map_det]
  rw [mul_right_comm, inv_mul_cancel₀ ha, one_mul]

theorem GlobalTheory.DetIdeleUnit.valued_eq_one_of_valuation {D : D7} {w : Pl D.host.E} (y : Kw w) (h : ValuativeRel.valuation (Kw w) y = 1) : Valued.v y = 1 := by
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  first
  | exact e.eq_one_iff_eq_one.1 h
  | exact le_antisymm (e.le_one_iff_le_one.1 h.le) (e.one_le_iff_one_le.1 h.ge)

namespace GlobalTheory.DetIdeleUnit

open Formalism.L2.NTheta (IsIdemAt)
open GlobalTheory.ExpansionInvariance

variable {D : D7}

theorem det_mt_conj (V : HSp D) (h k : GA D V) :
    (Formalism.L2.Theta.mt V (h⁻¹ * k * h)).det = (Formalism.L2.Theta.mt V k).det := by
  rw [GlobalTheory.IdemSupport.mt_mul, GlobalTheory.IdemSupport.mt_mul, Matrix.det_mul, Matrix.det_mul,
    mul_comm (Formalism.L2.Theta.mt V h⁻¹).det, mul_assoc, ← Matrix.det_mul, ← GlobalTheory.IdemSupport.mt_mul, inv_mul_cancel,
    GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one, mul_one]

theorem cpt_det_cutPart {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P)
    (V : HSp D) (g : GA D V) :
    GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det) =
      GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V g).det) := by
  have hee : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have hc0 : e * cA D e = 0 := he.2
  obtain ⟨hf1, hf2⟩ := idem_conj_sum hee hc0
  obtain ⟨⟨es, hes, hae⟩, -⟩ := id he
  let ψ : AE D →+* Kw PP := (GlobalTheory.StdFrames.cpt PP).comp (toEAf D)
  have hψe : ψ e = 1 := by

    rw [hae, map_sum, Finset.sum_eq_single PP]
    · exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).1
    · intro Q hQ hne
      exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).2 PP (Ne.symm hne)
    · intro h; exact absurd hPP h
  have hψc : ψ (cA D e) = 0 := by
    have := congrArg ψ hc0
    rwa [map_mul, hψe, one_mul, map_zero] at this
  have hψa : ψ (e + cA D e) = 1 := by rw [map_add (f := _), hψe, hψc, add_zero]
  show ψ _ = ψ _
  rw [RingHom.map_det, RingHom.map_det, mt_cutPart hf1 hf2]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
    map_mul, map_sub, map_one, hψa, hψe, hψc, one_mul, sub_self, zero_mul, add_zero]

theorem absFin_detAt_cutPart {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (hee : e * e = e) (V : HSp D)
    (g : GA D V) (hg : ∀ PP ∈ P, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V g).det)) = 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e hee V (cutPart (e + cA D e) V g)) = 1 :=
  absFin_idemSum_eq_one he _ (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det
    (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)⁻¹).det
    (by rw [← Matrix.det_mul, ← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]) rfl
    (fun PP hPP => by rw [cpt_det_cutPart he hPP]; exact hg PP hPP)

end GlobalTheory.DetIdeleUnit


open GlobalTheory.DetIdeleUnit in
theorem GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) = 1 := by
  intro D T L sc G W U S t μ₀ hμ ht Φ β j hj k hk e he
  refine absFin_detAt_cutPart he _ _ _ fun PP hPP => ?_
  have h1 := GlobalTheory.TopLevelInv.valuation_gdet_kapAt S hj hk ⟨PP, hPP⟩
  rw [cpt_gdet_kapAt] at h1
  have h2 := valued_eq_one_of_valuation _ h1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, det_mt_conj]
  rw [RingHom.map_det]
  exact h2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusConjLevelDetEqOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.finiteIdeleModulus_conjLevelDet_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) = 1 := by
  first | exact @GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one | exact GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one | (intros; apply GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacePartFixesStandardVacuumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.offPlacePart_fixes_standardVacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))), 1) (S.Z.vac (.top t (j + 1))) = S.Z.vac (.top t (j + 1)) := by
  first | exact @GlobalTheory.OffPartVac.offPart_fixes_vac | exact GlobalTheory.OffPartVac.offPart_fixes_vac | (intros; apply GlobalTheory.OffPartVac.offPart_fixes_vac <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionMovesStandardVacuumTopNodeEqCharSmul

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.TopLevelInv


open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove in
theorem vac_high_law (hA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))), 1) (S.Z.vac (.top t (j + 1))) = S.Z.vac (.top t (j + 1))) (hC1 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) = 1) (hC2 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ)) : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hce : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hce
  have hW := W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hvac := S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hS := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m by omega))
  have hT := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
  set g : GA D (G.V (.top (j + 1))) := ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) with hgdef
  have key := GlobalTheory.SplitLinear.splitLinearModel D W.ψ _ _ _ _ _ hW _ _ hS hT (locPl G t) e he _ hvac.2.theta hvac.2.lat 1
    one_ne_zero Tm hTm (cutPart (e + cA D e) _ g) 1 (suppAt_cutPart hee hce _ g) (GlobalTheory.SplitLinear.suppAt_one e _) _ _
    (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) _ (GlobalTheory.isSBHalf_halfInd e _)
  have hvacTm : Tm (halfInd e (stdLatO S (.top t (j + 1)))) = S.Z.vac (.top t (j + 1)) := by
    have := hTm.vac
    rwa [one_smul] at this
  have hr1 : Even (G.V (.top (j + 1 + 1))).rank := by
    rw [GlobalTheory.FunObj.rank_top G (j := j + 1 + 1) (by omega)]; exact GlobalTheory.FunObj.rankX_even D (j + 1 + 1)
  have hr0 : Even (G.V (.top (j + 1))).rank := by
    rw [GlobalTheory.FunObj.rank_top G (j := j + 1) (by omega)]; exact GlobalTheory.FunObj.rankX_even D (j + 1)
  have hTc : G.chrT (.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, if_false]
  have hc : ((splitFacO (G.chrS (.top t (j + 1) : Pair T)) (G.chrT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ)) =
      ∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ) := by
    have h1 : GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1 = 1 := map_one _
    have h2 := hC1 S hL ht j hj k hk e he
    have h3 := hC2 S hL ht j hj k hk e he
    rw [h1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac, h2, hTc]
    simp only [splitFacO, map_one, mul_one, Real.one_rpow, Complex.ofReal_one, Circle.coe_inv]
    have h4 : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    simp only [h4, Real.one_rpow, mul_one, Complex.ofReal_one]
    have h5 : ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g)) : Circle) : ℂ) =
        ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ) := h3
    rw [h5, ← Finset.prod_inv_distrib]
    simp only [Units.val_inv_eq_inv_val]
  calc W.om (.top t (j + 1)) (g, 1) (S.Z.vac (.top t (j + 1)))
      = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1)
          (W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) _ g, 1) (S.Z.vac (.top t (j + 1)))) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, ← cutPart_mul hf]
    _ = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1) (S.Z.vac (.top t (j + 1))) := by
        rw [hA S hL ht j hj k hk e he]
    _ = _ := by
        rw [← hvacTm]
        erw [key]
        rw [← hc]
        conv_rhs => rw [← map_smul]
        congr 1
        funext x
        rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitLinear.subst_eq, halfInd_cutPart hee hce]
        rfl

theorem vac_move_high_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) :=
  vac_high_law (by intros; apply GlobalTheory.T.offPlacePart_fixes_standardVacuum <;> assumption) (by intros; apply GlobalTheory.T.finiteIdeleModulus_conjLevelDet_eq_one <;> assumption)
    (by intros; apply GlobalTheory.T.gridTupleHeckeCharacter_detIdele_eq_prod_local <;> assumption)

end GlobalTheory.TopLevelInv

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionMovesStandardVacuumTopNodeEqCharSmulStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.weilAction_moves_standardVacuum_topNode_eq_char_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  first | exact @GlobalTheory.TopLevelInv.vac_move_high_eq | exact GlobalTheory.TopLevelInv.vac_move_high_eq | (intros; apply GlobalTheory.TopLevelInv.vac_move_high_eq <;> assumption)
end
end
