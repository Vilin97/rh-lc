module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeEqualityOfEvaluationVectorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesBaseDatumAdelicFormMultipleStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistTrivialOnRational
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeTransferRankOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDetOfMemSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
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
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortTranslate

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.LevelMoveShort

open GlobalTheory.TraceLattice




theorem isShortRule_mv {D : D7} (T : Full D) (hT : LawsFull T) {j : ℕ} (hj : InR D j) (hxi : TwistTrivialOnRational T j)
    {w : WeightFamilies.Wt D j} {n : ℕ} (hn : w.n = n) (hnV : n = D.R.nV)
    {γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l} (hγ : DetOne γ)
    {Λ : GenLat D.host.E n} {N : ℕ} {P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F} {x x' : Fin n → (T.Q.Dw j).La} {f : T.R j}
    (h1 : Λ.Unimod) (h2 : Λ.TrivAt (badN D)) (h3 : Λ.TrivAt (T.dδ j n).l₂.M) (h4 : Λ.LevOK N (T.dδ j n).l₂.M)
    (hP : P ∈ harmL (Dw := T.Q.Dw j) T.Q.c Λ (wtA w)) (hx : IsRightMul γ x' x) (ha : AdmX (l := T.Q.l) true x)
    (ha' : AdmX (l := T.Q.l) true x') (hs : f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n)
    (hf : IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x P f) :
    IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x' P (mv T.toTop j γ f) := by
  subst hn
  have hd : decide (w.n = D.R.nV) = true := decide_eq_true hnV
  have hG : GoodDatum T.toTop j w Λ N P := ⟨h1, h2, h3, h4, hP⟩
  obtain ⟨f', hf'⟩ := exists_isSeries hT.sh hj hG (x := x') (hd ▸ ha')
  have e := mv_series T hT hj hxi (hnV ▸ Nat.le_add_right _ _) hγ hG hx ⟨hd ▸ ha, hs, hf⟩ hf'
  rw [e]
  exact hf'.2.2

end GlobalTheory.LevelMoveShort

theorem GlobalTheory.LevelMoveShort.short_translate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), R.LUnif → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ), RunPin (T := T) R i (κ i).n v p → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → ∀ u : U, ∃ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P (F₀.1 : T.R ((i : ℕ) + 1)) ∧ cuspTo hT.p fw i (f u) = (R.FW i).ρ ((u : G)⁻¹) (cuspTo hT.p fw i F₀) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw hT _ i _ ℓ hℓ hAP v p hR hPg U hU Λ N x₀ P x f h1 h2 h3 h4 ha₀ hP hx u
  obtain ⟨act, hact, hρ⟩ := hAP
  have hnV : (κ i).n = D.R.nV := (fw.kap i (D.eTau.symm 1)).2.2
  have hnV' : (Vc D i).rank = D.R.nV := (GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne.rank_Vc i).1
  have hxi := GlobalTheory.TraceLattice.twistTrivial_of_runPin hT hR
  have hdet : GlobalTheory.TraceLattice.DetOne (ℓ (u : G)) := GlobalTheory.TraceLattice.detOne_of_levelPin hT hℓ hPg (hU u)
  refine ⟨act (u : G) (f u), ?_, ?_⟩
  · rw [hact]
    exact GlobalTheory.LevelMoveShort.isShortRule_mv T hT (inR_succ i) hxi (hnV.trans hnV'.symm) hnV' hdet h1 h2 h3 h4 hP
      (hx u).1 (hx u).2.1 ha₀ (cutR_le T.C _ _ (f u).2).1 (hx u).2.2
  · rw [hρ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesTraceTermAtEvaluationVector

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.OneTermEval



theorem series_term_at_eval : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ u : U, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hOM hβ hU hIo hRow hPh hCS v hv hmu hQG hFO hVal hdel hMb hRun ℓ hLev hAct U hdet χ ξR ω φ hK Λ h hSp hLa N x₀ P x f y h1 h2 h3 h4 h5 h6 h7 h8
  have base := GlobalTheory.T.shortSeries_baseDatum_adelicForm_multiple D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOM hβ hU hIo hRow hPh hCS v hv hmu hQG hFO hVal hdel hMb hRun ℓ hLev hAct χ ξR ω φ hK Λ h hSp hLa N x₀ P y h1 h2 h3 h4 h5 h6 h8
  rcases base with ⟨y₀, c, hr, hc, hmain⟩
  refine ⟨y₀, c, hr, hc, fun φ' hφ' w hw u => ?_⟩
  obtain ⟨F₀, hF₀, he⟩ := GlobalTheory.LevelMoveShort.short_translate D G Pl0 T0 A T R F κ v₀ fw hT hC i hU ℓ hLev hAct v (ownAt D v) hRun hMb U hdet Λ N x₀ P x f h1 h2 h3 h4 h5 h6 h7 u
  have e := (hU i (sg0 D A)).2.2 ((u : G)⁻¹) (cuspTo hT.p fw i F₀)
  have hc1 : (R.FW i).chi ((u : G)⁻¹) = 1 := by
    apply Units.ext
    apply D.what₂.embLL.injective
    rw [hC.grp.chiW, Units.val_one, map_one]
    refine Finset.prod_eq_one fun PP _ => ?_
    have hd : Matrix.GeneralLinearGroup.det (R.eG ((u : G)⁻¹) PP) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact hdet u⁻¹ PP
    rw [hd, map_one, Units.val_one]
  rw [hc1, Units.val_one, map_one, one_smul] at e
  have e2 : adForm R i ((R.FW i).ρ ((u : G)⁻¹) (cuspTo hT.p fw i F₀)) (fun ρ => w ρ) =
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (adForm R i (cuspTo hT.p fw i F₀) (fun ρ => w ρ)) :=
    congrArg (fun T => T (fun ρ => w ρ)) e
  rw [he, e2, hmain φ' hφ' w hw F₀ hF₀, map_smul]

end GlobalTheory.OneTermEval
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesTraceTermAtEvaluationVectorStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.shortSeries_trace_term_at_evaluationVector : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ u : U, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  first | exact @GlobalTheory.OneTermEval.series_term_at_eval | exact GlobalTheory.OneTermEval.series_term_at_eval | (intros; apply GlobalTheory.OneTermEval.series_term_at_eval <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceShortSeriesEqMulAdelicSeries

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.OneMapExact.splitOff_of_dvd {D : D7} {V : HSp D} {b b' : ℕ} (hd : b ∣ b') {g : GA D V} (H : SplitOffBad V b' g) :
    SplitOffBad V b g := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := H
  refine ⟨h1, e, P, h2, fun PP hP hb => h3 PP hP ?_, h4⟩
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hb

theorem GlobalTheory.OneMapExact.trace_of_terms {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (S : GA D (Wc D i) → ℂ) (c : D.what₂.LL) (X : U → Fin (R.nW i) → D.what₂.LL)
    (w : ∀ τ, (R.MW i (sg0 D A)).sm τ)
    (H : ∀ u : U, adForm R i (X u) w =
      D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) S) :
    adForm R i (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • X u) w = D.what₂.embLL c • levelTrace R i U ψ S := by
  classical
  have h0 : adForm R i 0 = 0 := by
    have := adForm_smul (R := R) (i := i) 0 0
    rw [zero_smul, map_zero, zero_smul] at this
    exact this
  have hadd : ∀ (s : Finset U) (Y : U → Fin (R.nW i) → D.what₂.LL),
      adForm R i (∑ u ∈ s, Y u) = ∑ u ∈ s, adForm R i (Y u) := by
    intro s Y
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adForm_add, ih]
  rw [finsum_eq_sum_of_fintype, hadd]
  simp only [adForm_smul]
  unfold levelTrace gaL
  rw [LinearMap.sum_apply]
  ext1 g
  simp only [MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, LinearMap.smul_apply,
    H, smul_eq_mul]
  set Fn : G → ℂ := fun d => (if hg : d ∈ U then D.what₂.embLL ((ψ ⟨d, hg⟩)⁻¹ : D.what₂.LLˣ) else 0) *
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG d) S g with hFn
  have e1 : ∑ d : G, Fn d = ∑ u : U, D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g := by
    calc ∑ d : G, Fn d = ∑ d ∈ Finset.univ.filter (· ∈ U), Fn d :=
          (Finset.sum_filter_of_ne fun d _ h => by
            by_contra hd
            exact h (by simp only [hFn, dif_neg hd, zero_mul])).symm
      _ = ∑ u : U, Fn u := Finset.sum_subtype _ (by simp) Fn
      _ = _ := Finset.sum_congr rfl fun u _ => by simp only [hFn, dif_pos u.2]
  have e2 : ∑ u : U, D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g =
      ∑ u : U, D.what₂.embLL ((ψ u⁻¹)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u⁻¹ : U) : G)) S g :=
    (Equiv.sum_comp (Equiv.inv U) (fun u : U => D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g)).symm
  rw [e2] at e1
  calc _ = D.what₂.embLL c * ∑ d : G, Fn d := by
        rw [e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [map_inv, inv_inv, Subgroup.coe_inv]
        ring
    _ = _ := by
        congr 1



theorem GlobalTheory.OneMapExact.one_term : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, ∀ u : U, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16
    U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  have hterm := GlobalTheory.T.shortSeries_trace_term_at_evaluationVector D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  obtain ⟨y₀, c, hr, hc, H⟩ := hterm
  exact ⟨y₀, c, hr, hc, fun φ' hφ' w u =>
    GlobalTheory.T.lowestTypeEquality_of_evaluationVector D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U χ ξR ω φ h17 Λ h (GlobalTheory.OneMapExact.splitOff_of_dvd (dvd_mul_right _ _) h18) h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27 y₀ c hr φ' hφ' u (fun w₀ hw₀ => H φ' hφ' w₀ hw₀ u) w⟩



theorem GlobalTheory.OneMapExact.trace_short_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • levelTrace R i U ψ (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16
    U hU ψ χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  obtain ⟨y₀, c, hr, hc, H⟩ := GlobalTheory.OneMapExact.one_term D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  exact ⟨y₀, c, hr, hc, fun φ' hφ' w => GlobalTheory.OneMapExact.trace_of_terms R i U ψ _ c _ _ (H φ' hφ' w)⟩

end
end
end
