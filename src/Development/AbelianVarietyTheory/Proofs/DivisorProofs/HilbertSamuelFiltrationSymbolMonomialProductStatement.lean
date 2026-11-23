module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelSectionShiftCommSingleMonomialStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopRankPowers
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
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLiftSymbol

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore.IntLift

variable {K : Type} [Field K] [NumberField K]

theorem mulPow_mem_global (G : Geo K) (s : Fin G.D → Fin G.N → K) {a j l : ℕ} (h : j + a = l)
    (α : MonoDeg (Fin G.D) a) {m : G.Sec j} (hm : m ∈ G.global j) : mulPow G s h α m ∈ G.global l := by
  obtain ⟨F, rfl⟩ := hm
  refine ⟨(Vanishing.powChart (isLB_tens G.K.isLB G.isLBA) G.isLB ((Nat.cast_add j a).symm.trans (congrArg _ h))).mul
    (H0.ofSec G.str ⊤ (monoSec (G.sec s) α)) F, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec]
  rfl

end GlobalTheory.HSCore.IntLift

namespace GlobalTheory.HSCore

end GlobalTheory.HSCore
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDataOfPositivity

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory

namespace GlobalTheory.HilbertSamuel.Model

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem mulW_mem_global (j : ℕ) (u : Fin G.N → F) {f : G.Sec j} (hf : f ∈ G.global j) :
    G.mulW j u f ∈ G.global (j + 1) := by
  obtain ⟨f, rfl⟩ := hf
  refine ⟨(oneChart (isLB_tens G.K.isLB G.isLBA) G.isLB (Nat.cast_succ j).symm).mul
    (H0.ofSec G.str ⊤ (G.comb u)) f, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec, G.ofSec_comb]
  simp [Geo.mulW, Fintype.linearCombination_apply]

variable {T : ℕ} (hT : G.D + 1 ≤ T) (β J : ℝ) (hβ : 1 ≤ β)





end GlobalTheory.HilbertSamuel.Model
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsGlobalResidues

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

namespace GlobalTheory.HSShort.GlobWord

theorem shift_single {K : Type} [Field K] [NumberField K] (G : Geo K) (j : ℕ) (u : Fin G.N → K) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext i
  cases i with
  | zero => rw [Pi.single_eq_of_ne (Nat.succ_ne_zero j).symm]; rfl
  | succ i =>
    show G.mulW i u ((Pi.single j m : Tot G) i) = _
    by_cases h : i = j
    · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun h' => h (Nat.succ_injective h')), map_zero]

theorem word_global : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (t j : ℕ) (u : Fin t → Fin G.N → K), ∀ x ∈ G.global j, ∃ x' ∈ G.global (j + t), word (shift G) u (Pi.single j x) = Pi.single (j + t) x' ∧ ∀ (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s) (δ : ℕ) (Co : Coord G hs δ) (p : Fin δ), Co.ev (j + t) (hs.res (j + t) x') p = (∏ q, ∑ k, u q k * Co.y p k) * Co.ev j (hs.res j x) p := by
  intro K _ _ G t j
  induction t with
  | zero =>
    intro u x hx
    exact ⟨x, hx, by simp [word], fun s hs δ Co p => by simp⟩
  | succ t ih =>
    intro u x hx
    obtain ⟨x', hx', hw, hr⟩ := ih (fun q => u q.succ) x hx
    refine ⟨G.mulW (j + t) (u 0) x', GlobalTheory.HilbertSamuel.Model.mulW_mem_global G (j + t) _ hx', ?_, fun s hs δ Co p => ?_⟩
    · unfold word at hw ⊢
      rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, hw]
      exact shift_single G (j + t) (u 0) x'
    · show Co.ev (j + t + 1) (hs.res (j + t + 1) (G.mulW (j + t) (u 0) x')) p = _
      rw [hs.res_mulW, Co.mul]
      beta_reduce
      rw [hr, Fin.prod_univ_succ, mul_assoc]

end GlobalTheory.HSShort.GlobWord
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsGlobalResiduesStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.productOfVectorMultiplications_global_residues : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (t j : ℕ) (u : Fin t → Fin G.N → K), ∀ x ∈ G.global j, ∃ x' ∈ G.global (j + t), word (shift G) u (Pi.single j x) = Pi.single (j + t) x' ∧ ∀ (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s) (δ : ℕ) (Co : Coord G hs δ) (p : Fin δ), Co.ev (j + t) (hs.res (j + t) x') p = (∏ q, ∑ k, u q k * Co.y p k) * Co.ev j (hs.res j x) p := by
  first | exact @GlobalTheory.HSShort.GlobWord.word_global | exact GlobalTheory.HSShort.GlobWord.word_global | (intros; apply GlobalTheory.HSShort.GlobWord.word_global <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelFiltrationSymbolMonomialProduct

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

namespace GlobalTheory.HSShort

theorem exists_filV_mulPow {K : Type} [Field K] [NumberField K] (X : Data K) {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s}
    {δ : ℕ} (Co : Coord X.toGeo hs δ) {a : ℕ} (haT : a ≤ X.T) (α : MonoDeg (Fin X.D) a)
    (m : X.Sec (X.T - a)) (hg : m ∈ X.global (X.T - a)) :
    ∃ f : filV X s a, (f.1 : X.Sec X.T) = mulPow X.toGeo s (Nat.sub_add_cancel haT) α m ∧
      ∀ α' p, symV Co a f (α', p) = if α'.1 = α.1 then Co.ev (X.T - a) (hs.res (X.T - a) m) p else 0 := by
  have hh : X.T - a + a = X.T := Nat.sub_add_cancel haT
  have hgl := GlobalTheory.HSCore.IntLift.mulPow_mem_global X.toGeo s hh α hg
  obtain ⟨f, hfeq⟩ : ∃ f : X.V X.T, (f : X.Sec X.T) = mulPow X.toGeo s hh α m := ⟨⟨_, X.global_le _ le_rfl hgl⟩, rfl⟩
  have hfF : (f : X.Sec X.T) ∈ Fil (X.ideal s) a (spaceV X s) := by
    refine (mem_Fil).2 ⟨Submodule.mem_sup_left ?_, ?_⟩
    · rw [hfeq]; exact hgl
    · rw [hfeq]; exact vanishesTo_mulMono _ _ _ _ _ _
  refine ⟨⟨f, hfF⟩, hfeq, fun α' p => ?_⟩
  have key : hs.sym hh (spaceV X s) ((X.V X.T).subtype.restrict (p := filV X s a) (q := Fil (X.ideal s) a (spaceV X s))
      (fun _ hx => hx) ⟨f, hfF⟩) = Pi.single α (hs.res (X.T - a) m) :=
    Vanishing.sym_mulMono _ _ _ _ _ _ _ _ _ _ α (m : X.Sec (X.T - a)) _ hfeq
  unfold symV
  rw [dite_eq_left haT]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, LinearEquiv.coe_coe, LinearMap.coe_proj,
    Function.eval]
  rw [key]
  by_cases hα : α' = α
  · subst hα; simp
  · rw [if_neg (fun h => hα (Subtype.ext h)), Pi.single_eq_of_ne hα, map_zero]; rfl

theorem totSym_incl {K : Type} [Field K] [NumberField K] {X : Data K} {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s}
    {δ : ℕ} (Co : Coord X.toGeo hs δ) (a : ℕ) (f : filV X s a) (y : totFil X s a) (h : y.1 = incl X X.T f.1) :
    totSym Co a y = symV Co a f := by
  have : y = Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a) f := Subtype.ext h
  rw [this]
  exact congrArg (symV Co a) (LinearEquiv.symm_apply_apply _ f)

theorem totSym_mono : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), X.MulStable → ∀ a < X.T - X.D, ∀ (α : MonoDeg (Fin X.D) a) (l : Fin (X.T - a) → Fin X.N → K), ∀ m ∈ LinearMap.range (incl X 0), ∃ h : pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l m) ∈ totFil X s a, ∀ α' p, totSym Co a ⟨_, h⟩ (α', p) = if α'.1 = α.1 then (∏ q, ∑ k, l q k * Co.y p k) * totRes Co m p else 0 := by
  intro K _ _ X s hs δ Co _ a ha α l m hm
  obtain ⟨m₀, rfl⟩ := hm
  have haT : a ≤ X.T := by omega
  have hm₀ : (m₀ : X.Sec 0) ∈ X.global 0 := (SetLike.ext_iff.1 X.V_zero _).1 m₀.2
  have H : ∀ (t k : ℕ) (_ : 0 + t = k) (u : Fin t → Fin X.N → K), ∃ x' ∈ X.global k,
      word (shift X.toGeo) u (Pi.single 0 (m₀ : X.Sec 0)) = Pi.single k x' ∧ ∀ p,
        Co.ev k (hs.res k x') p = (∏ q, ∑ j, u q j * Co.y p j) * Co.ev 0 (hs.res 0 m₀) p := by
    intro t k h u
    subst h
    obtain ⟨x', h1, h2, h3⟩ := GlobalTheory.T.productOfVectorMultiplications_global_residues K X.toGeo t 0 u _ hm₀
    exact ⟨x', h1, h2, h3 s hs δ Co⟩
  obtain ⟨x', h1, h2, h3⟩ := H _ _ (Nat.zero_add _) l
  obtain ⟨f, hf, hsym⟩ := exists_filV_mulPow X Co haT α x' h1
  have e : pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l (incl X 0 m₀)) = incl X X.T f.1 := by
    change pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l (Pi.single 0 (m₀ : X.Sec 0))) =
      Pi.single X.T (f.1 : X.Sec X.T)
    rw [h2, hf]
    exact (GlobalTheory.T.hilbertSamuelSectionShift_comm_single_monomial K X.toGeo).2.2 s a _ _ _ α x'
  refine ⟨⟨f.1, f.2, e.symm⟩, fun α' p => ?_⟩
  rw [totSym_incl Co a f _ e, hsym, h3]
  have : totRes Co (incl X 0 m₀) = Co.ev 0 (hs.res 0 m₀) := by simp [totRes, incl]
  rw [this]

end GlobalTheory.HSShort
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelFiltrationSymbolMonomialProductStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.hilbertSamuelFiltrationSymbol_monomial_product : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), X.MulStable → ∀ a < X.T - X.D, ∀ (α : MonoDeg (Fin X.D) a) (l : Fin (X.T - a) → Fin X.N → K), ∀ m ∈ LinearMap.range (incl X 0), ∃ h : pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l m) ∈ totFil X s a, ∀ α' p, totSym Co a ⟨_, h⟩ (α', p) = if α'.1 = α.1 then (∏ q, ∑ k, l q k * Co.y p k) * totRes Co m p else 0 := by
  first | exact @GlobalTheory.HSShort.totSym_mono | exact GlobalTheory.HSShort.totSym_mono | (intros; apply GlobalTheory.HSShort.totSym_mono <;> assumption)
end
end
