module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenInterEqSingletonOfNoGenerisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffQDivAddOfIsQCart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalMultipleAddQWeil
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LcCutTwoClosedPointsOneCentreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionStepLogCanonical

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingSectionOfIsolatedNonKltPoint

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sec_sep_of_lcCut : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (ρ d : ℚ) (x x' : X), M.IsLB → IsEffQDiv Δ → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → QNum p N d D → d < ρ → IsClosed ({x} : Set X) → x ≠ x' → LcCut p n (Δ + D) x 0 → ¬ KltAt p n (Δ + D) x' → ∃ s : M.Sec, x ∈ nonzeroLocus s ∧ x' ∉ nonzeroLocus s := by
  intro hNadel X _ _ _ p n hp hn
  letI := algebraΓOfHom p
  intro M Δ m G N D ρ d x x' hM hΔ hm hG hN hdeg hD hdρ hx hxx' hlc hx'
  haveI hNoeth : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨m', D₀, hm', hD₀, rfl, hDn⟩ := hD

  have hq0 : 0 < ρ - d := sub_pos.2 hdρ
  set a : ℕ := (ρ - d).num.toNat with ha_def
  set b : ℕ := (ρ - d).den with hb_def
  have hb : 0 < b := (ρ - d).den_pos
  have hnum : 0 < (ρ - d).num := Rat.num_pos.2 hq0
  have ha : ((a : ℤ) : ℚ) = (ρ - d).num := by
    rw [ha_def, Int.toNat_of_nonneg hnum.le]
  have ha1 : 1 ≤ a := by omega
  have hab : ρ - d = (a : ℚ) / b := by
    have e := Rat.num_div_den (ρ - d)
    rw [← ha, Int.cast_natCast] at e
    exact e.symm
  have hpS : IsProjOver (strHom ℂ (X := X)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have hNa : IsAmpleLB (lbPow N a) := (isAmpleLB_pow_iff hN.isLB ha1).2 hN
  have hdeg' : ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) =
      interNumRed ℂ C ![toLB (m' • G + m • D₀)] / ((m * m' : ℕ) : ℚ) +
        interNumRed ℂ C ![lbPow N a] / (b : ℚ) := by
    intro C hC
    have e := hC.interNumRed_of_cls_eq_add hH (isLB_toLB (m' • G + m • D₀))
      (isLB_lbPow (isLB_toLB G) m') (isLB_lbPow (isLB_toLB D₀) m)
      (by rw [cls_lbPow (isLB_toLB G), cls_lbPow (isLB_toLB D₀), ← toPic_apply, ← toPic_apply,
        ← toPic_apply, map_add, map_nsmul, map_nsmul])
    rw [hC.interNumRed_lbPow hH (isLB_toLB G), hC.interNumRed_lbPow hH (isLB_toLB D₀)] at e
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    have h3 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
    have hD' := hDn C hC
    rw [div_eq_iff h2] at hD'
    rw [hdeg C hC, e, hC.interNumRed_lbPow hH hN.isLB a, show ρ = d + a / b by linarith]
    push_cast
    rw [hD']
    field_simp
    ring
  obtain ⟨J, hJ, hvan⟩ := hNadel X p n hp hn M (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) b
    (lbPow N a) hM (isEffQDiv_add_of_isQCart X p hp Δ _ hΔ ⟨m', D₀, hm', hD₀, rfl⟩)
    (Nat.mul_pos hm hm') (isLogCanonicalMultiple_add_qWeil X p n Δ m m' G D₀ hm hm' hG) hb
    hNa.isNef (IsAmpleLB.isBig ℂ X hpS _ hNa) hdeg'
  have hxJ : x ∈ J.support := (hJ x).2 hlc.2.1
  have hx'J : x' ∈ J.support := (hJ x').2 hx'
  obtain ⟨U, hxU, hU⟩ := exists_open_inter_eq_singleton_of_no_generisation X (J.support : Set X) x
    J.support.isClosed hx hxJ fun z hz hzx => by
      by_contra hne
      obtain ⟨e, -, he, h1⟩ := closure_point_topologicalKrullDim X n z hn
      have h0 := hlc.2.2 z hzx ((hJ z).1 hz)
      have he1 := h1 x hzx (Ne.symm hne)
      rw [he] at h0
      have : e ≤ 0 := by exact_mod_cast h0
      omega
  obtain ⟨s, hs1, hs2⟩ := exists_sec_mem_nonzeroLocus_of_isolated_zero_else ℂ X p hp M hM J x U hx
    hxU hU (hvan 1 one_pos)
  exact ⟨s, hs1, hs2 x' hx'J (Ne.symm hxx')⟩

end GlobalTheory.PairStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingSectionOfIsolatedNonKltPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (ρ d : ℚ) (x x' : X), M.IsLB → IsEffQDiv Δ → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → QNum p N d D → d < ρ → IsClosed ({x} : Set X) → x ≠ x' → LcCut p n (Δ + D) x 0 → ¬ KltAt p n (Δ + D) x' → ∃ s : M.Sec, x ∈ nonzeroLocus s ∧ x' ∉ nonzeroLocus s := by
  first | exact @GlobalTheory.PairStep.exists_sec_sep_of_lcCut | exact GlobalTheory.PairStep.exists_sec_sep_of_lcCut | (intros; apply GlobalTheory.PairStep.exists_sec_sep_of_lcCut <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QWeilZeroCartier

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PairStep

theorem qWeil_zero_cartier {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (m : ℕ) :
    qWeil (0 : CartierDiv X) m = 0 := by
  funext z
  have : (0 : CartierDiv X).mult z = 0 := by
    rw [(CartierDiv.isEqn_zero z).mult_eq]
    by_cases hz : Order.coheight z = 1
    · exact (Scheme.ord_eq_iff hz one_ne_zero).2 (by simp)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _
  simp [qWeil, this]

theorem qNum_zero_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ),
    IsProjOver p → ∀ N : LB X, QNum p N 0 0 := by
  intro X _ _ p _ N
  letI := algebraΓOfHom p
  refine ⟨1, 0, one_pos, CartierDiv.eff_zero, (qWeil_zero_cartier 1).symm, fun C _ => ?_⟩
  rw [interNumRed_one_eq_zero (isLB_toLB 0) (by rw [← toPic_apply, map_zero])]
  simp

end GlobalTheory.PairStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionStepLogCanonicalStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.twoPoint_induction_step_logCanonical : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (d ε : ℚ) (h : ℕ → ℚ) (x x' : X) (j : ℕ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x} : Set X) → IsClosed ({x'} : Set X) → x ≠ x' → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x ∨ z ⤳ x' → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → 0 < ε → QNum p N d D → 0 ≤ d → LcCut p n (Δ + D) x j → ¬ KltAt p n (Δ + D) x' → LcCut p n (Δ + D) x 0 ∨ ∃ (i : ℕ) (D' : X → ℚ) (d' : ℚ), i < j ∧ 0 ≤ d' ∧ d' ≤ d + (h (i + 1) + ε) ∧ QNum p N d' D' ∧ ((LcCut p n (Δ + D') x i ∧ ¬ KltAt p n (Δ + D') x') ∨ (LcCut p n (Δ + D') x' i ∧ ¬ KltAt p n (Δ + D') x)) := by
  first | exact @GlobalTheory.PairStep.twoPoint_step | exact GlobalTheory.PairStep.twoPoint_step | (intros; apply GlobalTheory.PairStep.twoPoint_step <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionKltPairSeparation

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem add_le_sum_Icc_of_lt (h : ℕ → ℚ) (ε : ℚ) (hpos : ∀ e, 0 < h e + ε) {n i j : ℕ}
    (hij : i < j) (hjn : j ≤ n) {d : ℚ} (hd : d ≤ ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε)) :
    d + (h (i + 1) + ε) ≤ ∑ e ∈ Finset.Icc (i + 1) n, (h e + ε) := by
  rw [Finset.Icc_eq_cons_Ioc (by omega : i + 1 ≤ n), Finset.sum_cons]
  have : ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε) ≤ ∑ e ∈ Finset.Ioc (i + 1) n, (h e + ε) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun e he => by simp only [Finset.mem_Icc, Finset.mem_Ioc] at he ⊢; omega)
      fun e _ _ => (hpos e).le
  linarith

theorem sum_Icc_le_sum_Icc_one (h : ℕ → ℚ) (ε : ℚ) (hpos : ∀ e, 0 < h e + ε) (n j : ℕ) :
    ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε) ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
    fun e _ _ => (hpos e).le

end GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem two_point_induction : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair →
    GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ε : ℚ)
    (h : ℕ → ℚ) (x₁ x₂ : X), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m →
    IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x₁} : Set X) →
    IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) →
    (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e →
      topologicalKrullDim (closure ({z} : Set X)) = e →
      2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X))
        fun _ : Fin e => N : ℤ)) → 0 < ε →
    ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) ∧ QNum p N d D ∧
      ((LcCut p n (Δ + D) x₁ 0 ∧ ¬ KltAt p n (Δ + D) x₂) ∨
        (LcCut p n (Δ + D) x₂ 0 ∧ ¬ KltAt p n (Δ + D) x₁)) := by
  intro hP hNV hNef X _ _ _ p n hproj hdim
  letI := algebraΓOfHom p
  intro Δ m G N ε h x₁ x₂ hΔ hklt hm hG hNa hc₁ hc₂ hne hh hint hε
  have hpos : ∀ e, 0 < h e + ε := fun e => add_pos (hh e) hε

  have hξ : ∀ x : X, genericPoint X ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hdimξ : topologicalKrullDim (closure ({genericPoint X} : Set X)) = n := by
    rw [genericPoint_closure,
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph, hdim]

  have hn : 1 ≤ n := by
    obtain ⟨e, -, he, he1⟩ := GlobalTheory.T.exists_topologicalKrullDim_closure_point_le X n (genericPoint X) hdim
    have hen : e = n := by
      rw [hdimξ] at he; exact_mod_cast he.symm
    subst hen
    by_cases h₁ : x₁ = genericPoint X
    · exact he1 x₂ (hξ x₂) fun h₂ => hne (h₁.trans h₂.symm)
    · exact he1 x₁ (hξ x₁) h₁
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  have key : ∀ j, j ≤ k → ∀ (D : X → ℚ) (d : ℚ), 0 ≤ d →
      d ≤ ∑ e ∈ Finset.Icc (j + 1) (k + 1), (h e + ε) → QNum p N d D →
      ((LcCut p (k + 1) (Δ + D) x₁ j ∧ ¬ KltAt p (k + 1) (Δ + D) x₂) ∨
        (LcCut p (k + 1) (Δ + D) x₂ j ∧ ¬ KltAt p (k + 1) (Δ + D) x₁)) →
      ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 (k + 1), (h e + ε) ∧ QNum p N d D ∧
        ((LcCut p (k + 1) (Δ + D) x₁ 0 ∧ ¬ KltAt p (k + 1) (Δ + D) x₂) ∨
          (LcCut p (k + 1) (Δ + D) x₂ 0 ∧ ¬ KltAt p (k + 1) (Δ + D) x₁)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hjk D d hd0 hd hQ hcut
    have hd1 := hd.trans (sum_Icc_le_sum_Icc_one h ε hpos (k + 1) j)
    rcases hcut with ⟨hc, hnk⟩ | ⟨hc, hnk⟩
    · rcases GlobalTheory.T.twoPoint_induction_step_logCanonical hP hNV hNef X p (k + 1) hproj hdim Δ m G N D d ε h x₁ x₂ j hΔ hklt hm
          hG hNa hc₁ hc₂ hne hh hint hε hQ hd0 hc hnk with h0 | ⟨i, D', d', hij, hd'0, hd', hQ', hc'⟩
      · exact ⟨D, d, hd1, hQ, Or.inl ⟨h0, hnk⟩⟩
      · exact ih i hij (by omega) D' d' hd'0
          (hd'.trans (add_le_sum_Icc_of_lt h ε hpos hij (by omega) hd)) hQ' hc'
    · rcases GlobalTheory.T.twoPoint_induction_step_logCanonical hP hNV hNef X p (k + 1) hproj hdim Δ m G N D d ε h x₂ x₁ j hΔ hklt hm
          hG hNa hc₂ hc₁ hne.symm hh (fun z e hz => hint z e hz.symm) hε hQ hd0 hc hnk with
        h0 | ⟨i, D', d', hij, hd'0, hd', hQ', hc'⟩
      · exact ⟨D, d, hd1, hQ, Or.inr ⟨h0, hnk⟩⟩
      · exact ih i hij (by omega) D' d' hd'0
          (hd'.trans (add_le_sum_Icc_of_lt h ε hpos hij (by omega) hd)) hQ' hc'.symm

  have hlc : ∀ x, LcAt p (k + 1) (Δ + 0) x := fun x => by rw [add_zero]; exact (hklt x).lcAt
  have hdimξ' : topologicalKrullDim (closure ({genericPoint X} : Set X)) = ((k + 1 : ℕ) : WithBot ℕ∞) :=
    hdimξ
  obtain ⟨D', d', hd'0, hd', hQ', hc'⟩ := GlobalTheory.T.lc_cut_two_closed_points_one_centre hP hNV hNef X p (k + 1) hproj hdim Δ m G N 0
    0 (h (k + 1)) x₁ x₂ (genericPoint X) k hΔ hklt hm hG hNa (qNum_zero_zero X p hproj N) le_rfl
    hc₁ hc₂ (hlc x₁) (hlc x₂) (hξ x₁) (hξ x₂) (Or.inl rfl) hdimξ' (hh _)
    (hint (genericPoint X) (k + 1) (Or.inl (hξ x₁)) (by omega) hdimξ')
  refine key k le_rfl D' d' hd'0 ?_ hQ' hc'
  rw [Finset.Icc_self, Finset.sum_singleton]
  linarith [hε]

end GlobalTheory.PairStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionKltPairSeparationStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.twoPoint_induction_kltPair_separation : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ε : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → 0 < ε → ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) ∧ QNum p N d D ∧ ((LcCut p n (Δ + D) x₁ 0 ∧ ¬ KltAt p n (Δ + D) x₂) ∨ (LcCut p n (Δ + D) x₂ 0 ∧ ¬ KltAt p n (Δ + D) x₁)) := by
  first | exact @GlobalTheory.PairStep.two_point_induction | exact GlobalTheory.PairStep.two_point_induction | (intros; apply GlobalTheory.PairStep.two_point_induction <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingTwoPointsAmple

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.exists_sec_separating_two_points_of_ample : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  intro hP hNV hNef X _ _ _ p n hproj hdim M Δ m G N ρ h x₁ x₂ hM hΔ hklt hm hlc hNamp hnum
    hx₁ hx₂ hne hh hvol hsum
  set S : ℚ := ∑ e ∈ Finset.Icc 1 n, h e with hS
  set ε : ℚ := (ρ - S) / (n + 1) with hε
  have hn1 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hεpos : 0 < ε := div_pos (by linarith) hn1
  have h1 : ((n : ℚ) + 1) * ε = ρ - S := by rw [hε]; field_simp
  have hsplit : ∑ e ∈ Finset.Icc 1 n, (h e + ε) = S + n * ε := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp [hS]
  obtain ⟨D, d, hd, hQ, hcase⟩ := GlobalTheory.T.twoPoint_induction_kltPair_separation hP hNV hNef X p n hproj hdim Δ m G N ε h x₁ x₂
    hΔ hklt hm hlc hNamp hx₁ hx₂ hne hh hvol hεpos
  have hdρ : d < ρ := by
    have h2 : (n : ℚ) * ε + ε = ρ - S := by rw [← h1]; ring
    linarith
  rcases hcase with ⟨hlc1, hnk2⟩ | ⟨hlc2, hnk1⟩
  · obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint hNV X p n hproj hdim M Δ m G N D ρ d x₁ x₂ hM hΔ hm hlc
      hNamp hnum hQ hdρ hx₁ hne hlc1 hnk2
    exact ⟨s, Or.inl ⟨hs1, hs2⟩⟩
  · obtain ⟨s, hs2, hs1⟩ := GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint hNV X p n hproj hdim M Δ m G N D ρ d x₂ x₁ hM hΔ hm hlc
      hNamp hnum hQ hdρ hx₂ (Ne.symm hne) hlc2 hnk1
    exact ⟨s, Or.inr ⟨hs2, hs1⟩⟩
end
end
