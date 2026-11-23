module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUni
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroChartOfMemberLevelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesReferenceTupleEqEmpty
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRowFrame
public import Formalism.LocalToGlobal.Columns.Adelic
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.RecLevelStep

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFramesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.memberRepresentative_moved_at_twist_eq_tupleFrames : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∀ (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => F.to0.cls0.lev.Lb) (fun _ => F.to0.cls0.lev.U) (fun _ => F.to0.cls0.lev.chi) (fun c => (F.to0.cls0.y c).1) (fun c s => (F.to0.cls0.stabI c s).1) (fun _ => k) → ∀ c, ∃ κ : F.to0.cls0.lev.U, (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) ∧ F.to0.cls0.lev.chi κ = 1 ∧ PtOf (B := B) ((show GA B (B.R.N 0) from (F.to0.cls0.y c).1 * κ.1) * k) (extTo I.SQ ((I.stp u a 0).rep (I.eCls0 l u a c)).1.1) := by
  first | exact @GlobalTheory.Mem.Col2.ZeroMove.main | exact GlobalTheory.Mem.Col2.ZeroMove.main | (intros; apply GlobalTheory.Mem.Col2.ZeroMove.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelCharacterEqReferenceTuple

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.StepZeroChr

theorem isPtOf_of_deco {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {p' : DecoF E n ST SG Q'} (e : p'.deco = p.deco)
    (h : IsPtOf hc g p) : IsPtOf hc g p' :=
  ⟨h.uni, e ▸ h.lat, e ▸ h.f, e ▸ h.be, fun P => (Finset.eq_empty_iff_forall_notMem.1 hQ P.1 P.2).elim⟩



theorem chr_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → chi κ0 = 1 → ∀ (x : U) (κ : (I.stp u a 0).G c'.1), (I.stp u a 0).gam c'.1 κ = 1 → PtOf (y c * κ0.1 * x.1 * k) ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 → ((chi x : ℂˣ) : ℂ) = B.embLL (((I.stp u a 0).chr c'.1 κ : B.LLˣ) : B.LL) := by
  intro B X I hI hP l Z u a Lb U chi y st k hR c κ0 c' hc' _ hchi x κ hκ hpt
  have hd : ((I.stp u a 0).rep c').1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
    subst hc'
    exact ClsZero.stepZero_corresponding_representatives_same_deco hI u a _ c
  have hΛ := ClsZero.levelTypePrimes_stepZero_eq_colLev hI a c'.1
  have hΛ0 := ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 c.1
  have hm : κ.2.1.1 ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).grp := by
    rw [hΛ0, ← hΛ]
    exact κ.2.1.2
  let κ' : (I.stp u I.mu0 0).G c.1 := (κ.1, ⟨κ.2.1.1, hm⟩, 1)
  have e1 : ((I.stp u I.mu0 0).act c.1 κ' ((I.stp u I.mu0 0).rep c)).1.1.deco =
      ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1.deco := by
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u I.mu0 0).rep c).1.1.deco = ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u a 0).rep c').1.1.deco
    rw [hd]
  have h1 : PtOf (y c * (κ0 * x).1 * k) ((I.stp u I.mu0 0).act c.1 κ' ((I.stp u I.mu0 0).rep c)).1.1 := by
    rw [Subgroup.coe_mul, ← mul_assoc]
    exact isPtOf_of_deco (RefTup.twistPrimes_reference_tuple_eq_empty B X I) e1 hpt
  have h2 := hR.chr c (κ0 * x) κ' hκ h1
  rw [map_mul, hchi, one_mul] at h2
  refine h2.trans ?_
  congr 2
  show (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr ⟨κ.2.1.1, hm⟩ *
      (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr 1 =
    (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 c'.1).chr κ.2.1 * (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 c'.1).chr κ.2.2
  rw [map_one, StepZero.chr_eq_one (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a c'.1), StepZero.chr_congr hΛ, StepZero.chr_congr hΛ0]

end GlobalTheory.TwU.StepZeroChr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelCharacterEqReferenceTupleStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZero_levelCharacter_eq_referenceTuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → chi κ0 = 1 → ∀ (x : U) (κ : (I.stp u a 0).G c'.1), (I.stp u a 0).gam c'.1 κ = 1 → PtOf (y c * κ0.1 * x.1 * k) ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 → ((chi x : ℂˣ) : ℂ) = B.embLL (((I.stp u a 0).chr c'.1 κ : B.LLˣ) : B.LL) := by
  first | exact @GlobalTheory.TwU.StepZeroChr.chr_zero | exact GlobalTheory.TwU.StepZeroChr.chr_zero | (intros; apply GlobalTheory.TwU.StepZeroChr.chr_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelReadAsReference

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.LevZero

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem moves_iff (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl)
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) :
    (∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c)) ↔
      ∃ g : FormG (colLev I.Ch 0), ufGL B.fields.E (B.R.N 0) g.1 = 1 ∧ g • ((I.stp u a 0).rep c).1.1.deco = q.deco := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  constructor
  · rintro ⟨κ, h1, h2, -⟩
    refine ⟨StepZero.down (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) ((I.Tp a).pref u 0) hΛ c.1 κ, h1, ?_⟩
    exact (StepZero.deco_smul (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) _ hΛ c.1 κ _).symm.trans
      (congrArg (fun q => q.deco) h2)
  · rintro ⟨g₀, h0, hg⟩
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p g₀ (by rw [hp]; exact hg)
    refine ⟨g, ?_, ?_, Chart0.cos0 I _ _⟩
    · exact (congrArg (fun g => ufGL B.fields.E (B.R.N 0) g.1) h2).trans h0
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp

theorem lev_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → ∀ (x : GA B (B.R.N 0)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0), PtOf (y c * κ0.1 * x * k) q → (x ∈ U ↔ ∃ κ : (I.stp u a 0).G c'.1, (I.stp u a 0).gam c'.1 κ = 1 ∧ ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 = q ∧ cosetIn ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')) = cosetIn ((I.stp u a 0).rep c')) := by
  intro B X I hI _ l _ u a Lb U chi y st k hR c κ0 c' hc' _ x q hq
  have hQ : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  have hq0 : PtOf (y c * (κ0.1 * x) * k) (extTo (I.Q I.mu0) q) := by
    rw [← mul_assoc]
    exact IsPtOf.extTo (hQ ▸ Finset.empty_subset _) (hQ ▸ Finset.disjoint_empty_right _) hq
  have h1 := hR.lev c (κ0.1 * x) (extTo (I.Q I.mu0) q) hq0
  have e : ((I.stp u a 0).rep c').1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
    rw [hc']
    exact ClsZero.stepZero_corresponding_representatives_same_deco hI u a _ c
  refine (Subgroup.mul_mem_cancel_left U κ0.2).symm.trans (h1.trans ((moves_iff I hI u I.mu0 c _).trans ?_))
  refine Iff.trans ?_ (moves_iff I hI u a c' q).symm
  rw [e]
  rfl

end GlobalTheory.Mem.Col2.TC.LevZero

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelReadAsReferenceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZero_level_readAsReference : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → ∀ (x : GA B (B.R.N 0)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0), PtOf (y c * κ0.1 * x * k) q → (x ∈ U ↔ ∃ κ : (I.stp u a 0).G c'.1, (I.stp u a 0).gam c'.1 κ = 1 ∧ ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 = q ∧ cosetIn ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')) = cosetIn ((I.stp u a 0).rep c')) := by
  exact @GlobalTheory.Mem.Col2.TC.LevZero.lev_zero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnTupleStepZeroReadByMemberLevel

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.AtTrue.StepZeroRead



theorem reads : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) K0 ∧ (∀ β, (K0 β).lev.Lb = F.to0.cls0.lev.Lb ∧ (K0 β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (K0 β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (K0 β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (K0 β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((K0 ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hF
  obtain ⟨k, hk⟩ := hF.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hk' : I.Reads u I.mu0 0 (fun _ => ()) (fun _ => F.to0.cls0.lev.Lb) (fun _ => F.to0.cls0.lev.U)
      (fun _ => F.to0.cls0.lev.chi) (fun c => (F.to0.cls0.y c).1) (fun c s => (F.to0.cls0.stabI c s).1) (fun _ => k ()) := hk
  choose κ hκ using GlobalTheory.T.memberRepresentative_moved_at_twist_eq_tupleFrames I hI hP l Z u F a Q hQ hF (k ()) hk'
  obtain ⟨K0, hLb, hUloc, hU, hchi, hy, hst⟩ :=
    GlobalTheory.T.stepZeroChart_of_memberLevel I hI hP l Z u a Q F.to0.cls0 κ (fun c s => hk'.stab c s)
  have nQ : ∀ v, ¬ I.UnderQ I.mu0 v := fun v ⟨P, hP', _⟩ => by
    rw [I.twistPrimes_reference_tuple_eq_empty] at hP'
    simp at hP'
  letI := StepZero.idxUnique (hI.idx_ok a)
  refine ⟨K0, ⟨fun _ => k (), ⟨?key, ?onto, ?lb, ?kstd, ?koff, ?kT, ?pt, ?lev, ?chr, ?stab⟩, ?off⟩, ?levs, ?ys⟩
  case key =>
    intro c c'
    exact ⟨fun _ => ⟨Subsingleton.elim _ _, Chart0.cos0 I _ _⟩, fun _ => rfl⟩
  case onto =>
    intro β
    obtain ⟨c0, -⟩ := hk'.onto ()
    exact ⟨I.eCls0 l u a c0, Subsingleton.elim _ _⟩
  case lb =>
    intro β x
    cases β
    rw [hLb]
    exact hk'.lb () x
  case kstd => exact fun _ => hk'.k_std ()
  case koff => exact fun _ v hT _ _ => hk'.k_off () v hT (nQ v) (Or.inl rfl)
  case kT => exact fun _ => hk'.k_T ()
  case pt =>
    intro c
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    show PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * k ()) _
    rw [hy c0]
    exact (hκ c0).2.2
  case lev =>
    intro c x q hq
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    change PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * x * k ()) q at hq
    rw [hy c0] at hq
    show x ∈ (K0 ()).lev.U ↔ _
    rw [hU]
    exact GlobalTheory.T.stepZero_level_readAsReference I hI hP l Z u a _ _ _ _ _ (k ()) hk' c0 (κ c0) _ rfl (hκ c0).2.2 x q hq
  case chr =>
    intro c x κ' hg hq
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    change PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * x.1 * k ()) _ at hq
    rw [hy c0] at hq
    let x' : F.to0.cls0.lev.U := ⟨x.1, hU ▸ x.2⟩
    show (((K0 ()).lev.chi x : ℂˣ) : ℂ) = _
    rw [hchi x x' rfl]
    exact GlobalTheory.T.stepZero_levelCharacter_eq_referenceTuple I hI hP l Z u a _ _ _ _ _ (k ()) hk' c0 (κ c0) _ rfl (hκ c0).2.2 (hκ c0).2.1 x' κ' hg hq
  case stab => exact fun c s => hst ⟨c, rfl⟩ s
  case off => exact fun _ v hT => hk'.k_off () v hT (nQ v) (Or.inl rfl)
  case levs => exact fun β => by cases β; exact ⟨hLb, hUloc, hU, hchi⟩
  case ys => exact fun c => ⟨κ c, hy c, (hκ c).2.1, (hκ c).1⟩

end GlobalTheory.TwU.AtTrue.StepZeroRead

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnTupleStepZeroReadByMemberLevelStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnTuple_stepZero_read_by_memberLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) K0 ∧ (∀ β, (K0 β).lev.Lb = F.to0.cls0.lev.Lb ∧ (K0 β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (K0 β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (K0 β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (K0 β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((K0 ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  exact @GlobalTheory.TwU.AtTrue.StepZeroRead.reads
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoiceStepZeroChartsGood

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwU.AtTrue.charts_zero_good : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ Kc : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), (ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1) ∧ (∀ β, (Kc β).lev.Lb = F.to0.cls0.lev.Lb ∧ (Kc β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (Kc β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (Kc β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (Kc β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((Kc ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hStd
  obtain ⟨K0, hR, hEq, hy⟩ := GlobalTheory.T.columnTuple_stepZero_read_by_memberLevel I hI hP l Z u F a Q hQ hStd
  obtain ⟨N, hN, hNc⟩ := GlobalTheory.unipotent_type_character_finite_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F.to0.glev0 ℂ (RingHom.id ℂ)
    (fun i => (I.rec7 l Z).host.g_prime i) (fun i => ⟨_, Complex.isPrimitiveRoot_exp _ ((I.rec7 l Z).host.g_prime i).ne_zero⟩)
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  haveI : NeZero (B.R.N 0) := ⟨(B.R.N_pos 0).ne'⟩
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hgr, -, -⟩ := hc 0 (Nat.zero_le _)
  have hB := basePi_of_ok hX hPr u
  have hLb : ∀ β, (K0 β).lev.Lb = baseLb B.fields.E (B.R.N 0) ((B.primes X).vT u) := fun β => by
    obtain ⟨k, hk⟩ := hR.readsK
    ext x
    exact (hk.lb β x).trans (GlobalTheory.Mem.Col2.Reside.mem_baseLb hPr u _ x).symm
  have hlaws := fun β => GlobalTheory.Mem.Col2.Reside.swapLaws B.sp.cm hB (hPr.T_prime u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => by simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hPr.vT_norm u P hP) hgr (K0 β).lev (hLb β)
  choose hl hk using hlaws
  refine ⟨fun β => { K0 β with lev := GlobalTheory.Mem.Col2.Reside.swap (K0 β).lev _ (hl β) }, ⟨hR, fun β => ⟨hk β, N, hN, fun κ => ?_⟩⟩, fun β => hEq β, hy⟩
  have hm : κ.1 ∈ F.to0.cls0.lev.U := (hEq β).2.2.1 ▸ κ.2
  have e := (hEq β).2.2.2 κ ⟨κ.1, hm⟩ rfl
  show (K0 β).lev.chi κ ^ N = 1
  rw [e]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact (hNc _).1)
end
end
