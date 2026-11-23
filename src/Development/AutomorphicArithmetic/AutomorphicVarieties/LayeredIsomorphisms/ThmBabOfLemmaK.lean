module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfDescends
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ExistsDescends
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycMemPrincIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.PrincGen
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Kmono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.PartA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.PartB
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
import Formalism.GaloisCohomology.Statement
import Mathlib.Data.Finset.Functor
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IsAlgClosureRat

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Descends

section

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.PropA.descends :
    ∀ (l : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] [NumberField L₀], HasMuQ l L₀ →
      ∀ γ : G L₀ (AlgebraicClosure L₀), IsGen l ⊤ γ → Descends l L₀ γ := by
  intro l _ L₀ _ _ hmu γ hγ e he m L₁ _ _ _ hL
  have hne : (e : ℤ) ≠ 0 := by
    have : 0 < e := he
    exact_mod_cast this.ne'
  exact step0 hmu hγ hne m L₁ hL
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.GenLevel

section

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.PropA.genLevel :
    ∀ (l : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] [NumberField L₀], HasMuQ l L₀ →
      ∃ γ : G L₀ (AlgebraicClosure L₀), IsGen l ⊤ γ ∧ IsLevel l (cycZ L₀ _ l γ : ℤ_[l]) (cZero l L₀) ∧
        ∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ cZero l L₀) := by
  intro l _ L₀ _ _ hmu
  have hM := muQ L₀ (AlgebraicClosure L₀) l
  have hq : qExp l ≤ cZero l L₀ := hM.2.2.1.mp hmu
  have hP := princGen l (cZero l L₀) hq
  obtain ⟨u, hu, hu'⟩ : ∃ u ∈ KStar.TotallyRealRoots.princ l (cZero l L₀), u ∉ KStar.TotallyRealRoots.princ l (cZero l L₀ + 1) := by
    by_contra hne
    push_neg at hne
    have h1 := hP.2.2 1
    rw [Subgroup.relIndex_eq_one.mpr hne, pow_one] at h1
    exact (Fact.out : l.Prime).one_lt.ne h1
  have hr := cycRange L₀ (AlgebraicClosure L₀) l hmu
  obtain ⟨γ, hγ⟩ : u ∈ (cycZ L₀ (AlgebraicClosure L₀) l).range := hr ▸ hu
  refine ⟨γ, ⟨Subgroup.mem_top _, ?_⟩, ?_, (hM.1 _).mpr le_rfl⟩
  · rw [← MonoidHom.range_eq_map, hr, hγ]
    exact (hP.1 u hu).mpr hu'
  · rw [hγ]
    exact (hP.2.1 u hu hu').1
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfIsTower

section

@[expose] public section

open NumberField Formalism.GaloisCohomology

theorem UpperTheory.V.PropA.aBound_of_isTower (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (l : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] [NumberField L₀] (R : ℕ) (ht : UpperTheory.V.Tower.IsTower l L₀ R) :
    UpperTheory.V.Win.ABound l R L₀ := by
  obtain ⟨γ, h₁, h₂, h₃⟩ := UpperTheory.V.PropA.genLevel l L₀ ht.mu
  exact UpperTheory.V.PropA.aBound_of_descends hP hF hT ht h₂ h₃ (UpperTheory.V.PropA.descends l L₀ ht.mu γ h₁)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Window1

section

@[expose] public section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.window1 :
    ∀ (R : ℕ) (B U : ℝ) (T : Finset ℝ), 1 ≤ B → 0 < U → T.card ≤ R →
      ∃ y : ℝ, U / (2 ^ (R + 2) * B ^ R) ≤ y ∧ 2 * y ≤ U ∧ ∀ a ∈ T, ∀ u : ℝ, y ≤ u → u ≤ 2 * y → a ≤ u → B * a ≤ u := by
  intro R
  induction R with
  | zero =>
    intro B U T hB hU hT
    have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT0
    refine ⟨U / 2, ?_, by linarith, ?_⟩
    · apply div_le_div_of_nonneg_left hU.le (by norm_num)
      norm_num
    · intro a ha
      simp at ha
  | succ n ih =>
    intro B U T hB hU hT
    have hB0 : 0 < B := by linarith
    by_cases h : ∃ a ∈ T, U / (2 * B) < a ∧ a ≤ U
    · obtain ⟨a0, ha0, h1, h2⟩ := h
      obtain ⟨y, hy1, hy2, hy3⟩ := ih B (U / (2 * B)) (T.erase a0) hB (by positivity)
        (by rw [Finset.card_erase_of_mem ha0]; omega)
      refine ⟨y, ?_, ?_, ?_⟩
      · calc U / (2 ^ (n + 1 + 2) * B ^ (n + 1))
            = U / (2 * B) / (2 ^ (n + 2) * B ^ n) := by
              rw [div_div]
              congr 1
              ring
          _ ≤ y := hy1
      · have : U / (2 * B) ≤ U := div_le_self hU.le (by linarith)
        linarith
      · intro a ha u hu1 hu2 hau
        by_cases hae : a = a0
        · subst hae
          exfalso
          have : U / (2 * B) < u := lt_of_lt_of_le h1 hau
          linarith
        · exact hy3 a (Finset.mem_erase.mpr ⟨hae, ha⟩) u hu1 hu2 hau
    · push_neg at h
      refine ⟨U / 2, ?_, by linarith, ?_⟩
      · apply div_le_div_of_nonneg_left hU.le (by norm_num)
        have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        have h3 : (1 : ℝ) ≤ B ^ (n + 1) := one_le_pow₀ hB
        have h4 : (2 : ℝ) ^ (n + 1 + 2) = 8 * 2 ^ n := by ring
        rw [h4]
        nlinarith
      · intro a ha u hu1 hu2 hau
        by_contra hc
        push_neg at hc
        have ha1 : U / (2 * B) < a := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        have := h a ha ha1
        linarith
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Window

section

@[expose] public section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.window :
    ∀ (R : ℕ) (eta Ct X : ℝ) (Exc : Finset ℕ), 0 < eta → eta ≤ Ct → 1 < X → Exc.card ≤ R →
      ∃ Y : ℝ, InRange (2 ^ (R + 2) * (Ct / eta) ^ R) X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → Good eta Ct Exc x := by
  intro R eta Ct X Exc heta hle hX hcard
  classical
  have hCt : 0 < Ct := lt_of_lt_of_le heta hle
  have hX0 : 0 < X := by linarith
  have hB : 1 ≤ Ct / eta := (one_le_div heta).mpr hle
  obtain ⟨y, hy1, hy2, hy3⟩ := UpperTheory.V.Win.window1 R (Ct / eta) (Real.log X)
    (Exc.image fun e : ℕ => Real.log (e : ℝ) / Ct) hB (Real.log_pos hX)
    (le_trans Finset.card_image_le hcard)
  have hsq : Real.exp y ^ (2 : ℝ) = Real.exp (2 * y) := by
    rw [← Real.exp_mul, mul_comm]
  refine ⟨Real.exp y, ⟨?_, ?_⟩, ?_⟩
  · rw [Real.rpow_def_of_pos hX0, Real.exp_le_exp, mul_one_div]
    exact hy1
  · rw [hsq, ← Real.le_log_iff_exp_le hX0]
    exact hy2
  · intro x hx1 hx2 e he hex
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos y) hx1
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · subst h0
      simpa using (Real.rpow_pos_of_pos hx0 eta).le
    have he0 : (0 : ℝ) < e := by exact_mod_cast hpos
    have hu1 : y ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx1
    have hu2 : Real.log x ≤ 2 * y := by
      rw [Real.log_le_iff_le_exp hx0, ← hsq]
      exact hx2
    have hu3 : Real.log (e : ℝ) / Ct ≤ Real.log x := by
      rw [div_le_iff₀ hCt, mul_comm, ← Real.log_rpow hx0]
      exact Real.log_le_log he0 hex
    have h := hy3 _ (Finset.mem_image_of_mem _ he) (Real.log x) hu1 hu2 hu3
    have h' : Ct / eta * (Real.log (e : ℝ) / Ct) = Real.log (e : ℝ) / eta := by
      field_simp
    rw [h', div_le_iff₀ heta] at h
    rw [Real.rpow_def_of_pos hx0, ← Real.log_le_iff_le_exp he0]
    exact h
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOf

section

@[expose] public section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.thmBab_of :
    (∃ CK : ℝ, LemmaK CK) → FixedIn → TwoIn → ∃ K : BConst, ∀ Ct : ℝ, 1 ≤ Ct → ThmBab K Ct := by
  rintro ⟨CK0, hK0⟩ hF hT
  classical
  have hCK1 : (1 : ℝ) ≤ max CK0 1 := le_max_right _ _
  have hCKpos : (0 : ℝ) < max CK0 1 := lt_of_lt_of_le one_pos hCK1
  have hK : LemmaK (max CK0 1) := kmono CK0 _ (le_max_left _ _) hK0
  let P : ℕ → AbF → ℕ → Prop := fun l A R =>
    ∃ (_ : Fact l.Prime) (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀), IsAbField A L₀ ∧ ABound l R L₀
  let R0 : AbF → ℕ := fun M => Classical.choose (hT M)
  let Rl : ℕ → AbF → ℕ := fun l A => if h : ∃ R, P l A R then Classical.choose h else 0
  refine ⟨BConst.mk R0 Rl (max CK0 1) hCKpos, fun Ct hCt => ?_⟩
  unfold ThmBab BShape IsBWindow
  intro M B' L hAux eps A1 heps heps'
  unfold OddPrimesWithRootsOfUnity at hAux
  have hCt0 : 0 < Ct := lt_of_lt_of_le one_pos hCt
  set CK : ℝ := max CK0 1 with hCKdef
  set R : ℕ := R0 M + ∑ l ∈ B', Rl l (L l) with hRdef
  set J : ℝ := 2 ^ (R + 2) * (2 * CK * Ct / eps) ^ R with hJdef
  have hJpos : 0 < J := by
    have : 0 < 2 * CK * Ct / eps := by positivity
    positivity
  obtain ⟨x0A, hA⟩ := partA CK hCKpos hK M (R0 M) J Ct eps A1 hJpos hCt0.le heps
  have hB : ∀ l ∈ B', ∃ x0 : ℝ, ∀ e t, admitted A1 Ct e t → ∀ X : ℝ, ∃ Exc : Finset ℕ,
      Exc.card ≤ Rl l (L l) ∧ ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct Exc x →
        ∀ (_ : Fact l.Prime) (L₀' : Type) [Field L₀'] [NumberField L₀'], IsAbField (L l) L₀' →
          ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀' L₁],
            IsLayer l (Nat.log l (Rl l (L l)) + 3) L₀' L₁ → VVat l L₁ (t x) (Real.exp (x ^ (4 * eps / 5))) := by
    intro l hl
    obtain ⟨hp, hl2, hmu⟩ := hAux l hl
    haveI : Fact l.Prime := ⟨hp⟩
    by_cases hex : ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀), IsAbField (L l) L₀
    · obtain ⟨L₀, _, _, hab⟩ := hex
      have hP : ∃ R, P l (L l) R := by
        obtain ⟨R', hR'⟩ := hF l hl2 (L l) hmu L₀ hab
        exact ⟨R', ⟨_, L₀, _, _, hab, hR'⟩⟩
      have hRl : Rl l (L l) = Classical.choose hP := by
        show (if h : ∃ R, P l (L l) R then Classical.choose h else 0) = _
        rw [dite_eq_left hP]
      obtain ⟨_, L₀₀, _, _, hab0, hR0⟩ := Classical.choose_spec hP
      obtain ⟨x0, hx0⟩ := partB CK hCKpos hK l (Classical.choose hP) hl2 (L l) hmu L₀₀ hab0 hR0
        J Ct eps A1 hJpos hCt0.le heps
      refine ⟨x0, fun e t hAdm X => ?_⟩
      obtain ⟨Exc, hcard, hx⟩ := hx0 e t hAdm X
      refine ⟨Exc, hRl ▸ hcard, fun x hxx hlo hhi hg _ L₀' _ _ hab' L₁ _ _ _ hlay => ?_⟩
      rw [hRl] at hlay
      exact hx x hxx hlo hhi hg L₀' hab' L₁ hlay
    · refine ⟨0, fun e t _ X => ⟨∅, by simp, ?_⟩⟩
      intro x _ _ _ _ _ L₀' _ _ hab' _ _ _ _ _
      exact absurd ⟨L₀', _, _, hab'⟩ hex
  choose! f hf using hB
  set x1 : ℝ := max 1 (max x0A (∑ l ∈ B', |f l|)) with hx1def
  have hfle : ∀ l ∈ B', f l ≤ x1 := fun l hl =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (f i)) hl).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hx0A : x0A ≤ x1 := (le_max_left _ _).trans (le_max_right _ _)
  have hx1pos : 0 ≤ x1 := zero_le_one.trans (le_max_left _ _)
  refine ⟨max 2 (x1 ^ J), fun e t hAdm X hX q d hqd hlog => ?_⟩
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXJ : x1 ^ J ≤ X := (le_max_right _ _).trans hX
  have hlow : x1 ≤ X ^ (1 / J) := by
    calc x1 = (x1 ^ J) ^ (1 / J) := by
          rw [← Real.rpow_mul hx1pos, mul_one_div_cancel hJpos.ne', Real.rpow_one]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hx1pos _) hXJ (by positivity)
  obtain ⟨L₀, _, _, hTB, hAB⟩ := Classical.choose_spec (hT M) q d hqd
  obtain ⟨ExcA, hcardA, hxA⟩ := hA e t hAdm X q d hqd hlog L₀ hTB hAB
  have hB2 := fun l hl => hf l hl e t hAdm X
  choose! g hg using hB2
  have hcard : (ExcA ∪ B'.biUnion g).card ≤ R :=
    (Finset.card_union_le _ _).trans (add_le_add hcardA
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun l hl => (hg l hl).1)))
  have heta : 0 < eps / (2 * CK) := by positivity
  have hetaCt : eps / (2 * CK) ≤ Ct := by
    have h1 : eps / (2 * CK) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  obtain ⟨Y, hY, hgood⟩ := window R (eps / (2 * CK)) Ct X (ExcA ∪ B'.biUnion g) heta hetaCt
    (by linarith) hcard
  have hJeq : (2 : ℝ) ^ (R + 2) * (Ct / (eps / (2 * CK))) ^ R = J := by
    rw [hJdef, show Ct / (eps / (2 * CK)) = 2 * CK * Ct / eps by rw [div_div_eq_mul_div]; ring]
  rw [hJeq] at hY
  refine ⟨Y, hY, fun x hYx hxY => ?_⟩
  have hG := hgood x hYx hxY
  have hXlo : X ^ (1 / J) ≤ x := hY.1.trans hYx
  have hXhi : x ≤ X := hxY.trans hY.2
  have hGsub : ∀ S ⊆ ExcA ∪ B'.biUnion g, Good (eps / (2 * CK)) Ct S x :=
    fun S hS n hn => hG n (hS hn)
  refine ⟨hxA x (hx0A.trans (hlow.trans hXlo)) hXlo hXhi (hGsub _ Finset.subset_union_left), ?_⟩
  unfold BbAt
  intro l hl _ L₀' _ _ hab L₁ _ _ _ hlay
  exact (hg l hl).2 x ((hfle l hl).trans (hlow.trans hXlo)) hXlo hXhi
    (hGsub _ ((Finset.subset_biUnion_of_mem g hl).trans Finset.subset_union_right)) _ L₀' hab L₁ hlay
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOfLemmaK

section

@[expose] public section

open Formalism.GaloisCohomology

namespace UpperTheory.V.Win

theorem thmBab_of_lemmaK (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hFW : Published.FerreroWashington) (hK : ∃ CK : ℝ, LemmaK CK) : ∃ K : BConst, ∀ Ct : ℝ, 1 ≤ Ct → ThmBab K Ct :=
  have hA : Two.TowerBound := fun l _ L _ _ R h => PropA.aBound_of_isTower hP hF hT l L R h
  thmBab_of hK (Two.fixedIn hFW hA) (Two.twoIn hFW hA)

end UpperTheory.V.Win
end
end
