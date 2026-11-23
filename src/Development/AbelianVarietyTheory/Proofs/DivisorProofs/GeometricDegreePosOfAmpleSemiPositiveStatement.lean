module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxMonomialFamilyProdMemNormBallOfExponentLtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBallFamMonoNegAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarieStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ManyIndependentProductsInFunctionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCardLeDegreeAmpleSemiPositive

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → P.L.SemiPos D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  intro hAr hHS k _ X _ p D hX P hamp hsp J _ e x he hx hbox
  have hxb := (GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX).2 x hx
  have hmono := (GlobalTheory.VolBr.isBallFam_mono_neg_add _ _ _ (GlobalTheory.VolBr.Pair.isBallFam k X p P 1 0)).1
  have hb : ∀ c, ∃ u : ℝ, 0 ≤ u ∧ boxFam e x c ∈ P.Bl 1 0 (Real.exp u) := fun c =>
    GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX P 1 0 _ (hbox c)
  choose u hu0 hu using hb
  have hall : ∀ c, boxFam e x c ∈ P.Bl 1 0 (Real.exp (∑ c, u c)) := fun c =>
    hmono _ _ (Real.exp_le_exp.2 (Finset.single_le_sum (fun c _ => hu0 c) (Finset.mem_univ c))) (hu c)
  apply GlobalTheory.T.factorial_mul_rank_le_degree_of_indep_small_sections hAr hHS k X p D hX P 1 0 P.L (GlobalTheory.VolBr.Pair.rep_base k X p P).1 hamp hsp
    (Fintype.card J) (∑ c, u c)
  intro m hm
  rcases isEmpty_or_nonempty J with hJ | ⟨⟨j⟩⟩
  · have h0 : Fintype.card J = 0 := Fintype.card_eq_zero
    haveI : IsEmpty (Fin (Fintype.card J * m ^ D)) := by rw [h0, zero_mul]; exact Fin.isEmpty'
    exact ⟨isEmptyElim, linearIndependent_empty_type, isEmptyElim⟩
  · haveI : CharZero X.functionField := charZero_of_inj_zero fun n hn => by
      have h := he.smul_left_injective j (a₁ := (n : ℤ)) (a₂ := 0) (by simp [hn])
      exact_mod_cast h
    obtain ⟨v, hv, hvs⟩ := GlobalTheory.T.exists_linearIndependent_products_function_field X.functionField D x hxb J e he m hm
    refine ⟨v, hv, fun s => ?_⟩
    obtain ⟨w, n, hn, hvs'⟩ := hvs s
    rw [hvs']
    have h := GlobalTheory.T.boxMonomialFamily_prod_mem_normBall_of_exponent_lt k X p P D J e x 1 0 (Real.exp (∑ c, u c)) (Real.exp_pos _).le hall m w n hn
    rw [← Real.exp_nat_mul, mul_comm (m : ℝ)] at h
    exact h
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCardLeDegreeAmpleSemiPositiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.factorial_mul_card_le_degree_ample_semiPositive : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → P.L.SemiPos D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  first | exact @GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam | exact GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam | (intros; apply GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreePow

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GdegPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem isometric_comb_unit (L : HermLB p) (n : ℕ) :
    (comb (fun _ : Unit => L) fun _ => (n : ℤ)).Isometric (L.pow n) :=
  HermLB.icls_eq_iff.1 (by rw [icls_comb, HermLB.icls_pow, Fintype.sum_unique, natCast_zsmul])

theorem lin_unit (c : ℝ) : (lin fun _ : Unit => c) = c • (MvPolynomial.X () : MvPolynomial Unit ℝ) := by
  rw [lin, Fintype.sum_unique, MvPolynomial.C_mul']

theorem gdeg_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (n : ℕ), gdeg (L.pow n) D = (n : ℝ) ^ D * gdeg L D := by
  intro hC k _ X _ p D hX L n
  obtain ⟨Ψ, hΨ, -⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).2
  have key (m : ℕ) : gdeg (L.pow m) D = (m : ℝ) ^ D * Ψ ((MvPolynomial.X () : MvPolynomial Unit ℝ) ^ D) := by
    rw [← (isometric_comb_unit L m).gdeg_eq, ← hΨ fun _ => (m : ℤ)]
    simp only [Int.cast_natCast]
    rw [lin_unit, smul_pow, map_smul, smul_eq_mul]
  have h1 : gdeg L D = Ψ ((MvPolynomial.X () : MvPolynomial Unit ℝ) ^ D) := by
    rw [← (HermLB.icls_eq_iff.1 (by rw [HermLB.icls_pow, one_smul]) : (L.pow 1).Isometric L).gdeg_eq, key 1]
    simp
  rw [key n, h1]

end GlobalTheory.GdegPow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreePowStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.hermLineBundleGeometricDegree_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (n : ℕ), gdeg (L.pow n) D = (n : ℝ) ^ D * gdeg L D := by
  first | exact @GlobalTheory.GdegPow.gdeg_pow | exact GlobalTheory.GdegPow.gdeg_pow | (intros; apply GlobalTheory.GdegPow.gdeg_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreePosOfAmpleSemiPositive

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_pair_mem_H_of_rep {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {a b : ℤ} {M : HermLB p} (h : P.Rep a b M) : ∃ Q : Pair p, Q.L = M ∧ ∀ f ∈ P.H a b, f ∈ Q.H 1 0 := by
  obtain ⟨ρ, hρ, hu, -⟩ := h
  refine ⟨⟨M, P.A, ρ, P.r', hρ, P.hr'⟩, rfl, fun f hf x c j hc hj => ?_⟩
  have hx : x ∈ (⨆ i, P.L.B.U i) := by rw [P.L.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  have h1 := (hu x c i j hc hi hj).regAt.mul (hf x i j hi hj)
  have hi0 : (P.r i : X.functionField) ^ a ≠ 0 := zpow_ne_zero _ (P.r i).ne_zero
  have hj0 : (P.r' j : X.functionField) ^ b ≠ 0 := zpow_ne_zero _ (P.r' j).ne_zero
  convert h1 using 1
  simp only [Pair.loc, zpow_one, zpow_zero]
  field_simp

theorem gdeg_pos_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, IsAmpleLB L.B → L.SemiPos D → 0 < gdeg L D := by
  intro hA hS k _ X _ p D hX L hL hs
  obtain ⟨P, rfl, hPA⟩ := exists_pair L L
  obtain ⟨x, hx⟩ := (GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX).1
  obtain ⟨c, g, hc, hg, -, hm⟩ := GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle k X p D hX P (hPA ▸ hL) 0 (Finset (Fin D)) fun S => ∏ i ∈ S, x i
  have hr := Pair.rep_pow k X p P 0 1 P.A c (Pair.rep_base k X p P).2.1
  rw [mul_zero, mul_one, hPA] at hr
  obtain ⟨Q, hQ, hH⟩ := exists_pair_mem_H_of_rep P hr
  have hQa : IsAmpleLB Q.L.B := by
    rw [hQ]
    exact (isAmpleLB_pow_iff hL.isLB hc).2 hL
  have hQs : Q.L.SemiPos D := by rw [hQ]; exact hs.pow c
  haveI : CharZero X.functionField :=
    have := hX.charZero
    ((fnOf (X := X) ⊤ trivial).charZero_iff (fnOf_injective _ _)).1 this
  have hli : LinearIndependent ℤ (fun _ : Unit => g) := linearIndependent_unique_iff.2 hg
  have h := GlobalTheory.T.factorial_mul_card_le_degree_ample_semiPositive hA hS k X p D hX Q hQa hQs Unit (fun _ => g) x hli hx.1 fun c' => hH _ (hm c'.2)
  rw [hQ, GlobalTheory.T.hermLineBundleGeometricDegree_pow hA k X p D hX] at h
  have h0 : (0 : ℝ) < (c : ℝ) ^ D := by positivity
  have h1 : (0 : ℝ) < (D.factorial : ℝ) * Fintype.card Unit := by
    simp [Nat.factorial_pos]
  exact (mul_pos_iff_of_pos_left h0).1 (h1.trans_le h)

end GlobalTheory.HSNef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreePosOfAmpleSemiPositiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.geometricDegree_pos_of_ample_semiPositive : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, IsAmpleLB L.B → L.SemiPos D → 0 < gdeg L D := by
  first | exact @GlobalTheory.HSNef.gdeg_pos_of_ample | exact GlobalTheory.HSNef.gdeg_pos_of_ample | (intros; apply GlobalTheory.HSNef.gdeg_pos_of_ample <;> assumption)
end
end
