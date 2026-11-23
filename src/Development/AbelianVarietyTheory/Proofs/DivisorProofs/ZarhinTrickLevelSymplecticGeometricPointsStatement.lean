module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Mathlib.Data.Nat.Totient
public import Mathlib.FieldTheory.Finite.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalZarhinBundleEqZetaPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductLevelStructureEqMkPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductMkPointBasicFacts
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBijectiveOnTorsionCoprimeDegree

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory

theorem isogeny_torsion_bij {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A]
    [IsCommMonObj B] (la : A ⟶ B) (mu : B ⟶ A) (d M : ℕ) (T : Over S) :
    IsMonHom la → IsMonHom mu → la ≫ mu = 𝟙 A ^ d → mu ≫ la = 𝟙 B ^ d → M.Coprime d →
      (∀ y : T ⟶ A, y ^ M = 1 → y ≫ la = 1 → y = 1) ∧
        (∀ g : T ⟶ B, g ^ M = 1 → ∃ y : T ⟶ A, y ^ M = 1 ∧ y ≫ la = g) := by
  intro hla hmu hlm hml hMd
  refine ⟨fun y hyM hyl => ?_, fun g hgM => ?_⟩
  · have hyd : y ^ d = 1 := by
      have h1 : y ≫ (la ≫ mu) = y ^ d := by
        rw [hlm, MonObj.comp_pow, Category.comp_id]
      rw [← h1, ← Category.assoc, hyl, MonObj.one_comp]
    have h := (pow_gcd_eq_one (a := y) (m := M) (n := d)).2 ⟨hyM, hyd⟩
    rwa [Nat.Coprime.gcd_eq_one hMd, pow_one] at h
  ·
    set e := d ^ (Nat.totient M - 1) with he
    have hde : d * e % M = 1 % M := by
      rcases Nat.eq_zero_or_pos M with h0 | hpos
      · subst h0
        have hd1 : d = 1 := (Nat.coprime_zero_left d).1 hMd
        subst hd1
        simp [he]
      · have ht : 0 < Nat.totient M := Nat.totient_pos.2 hpos
        have hpow : d * e = d ^ Nat.totient M := by
          rw [he, ← pow_succ']
          congr 1
          omega
        rw [hpow]
        exact Nat.ModEq.pow_totient (Nat.Coprime.symm hMd)
    refine ⟨(g ≫ mu) ^ e, ?_, ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, ← MonObj.pow_comp, hgM, MonObj.one_comp, one_pow]
    · have h1 : (g ≫ mu) ≫ la = g ^ d := by
        rw [Category.assoc, hml, MonObj.comp_pow, Category.comp_id]
      rw [MonObj.pow_comp, h1, ← pow_mul, pow_eq_pow_mod (d * e) hgM, hde,
        ← pow_eq_pow_mod 1 hgM, pow_one]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBijectiveOnTorsionCoprimeDegreeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.isogeny_bijective_on_torsion_coprime_degree : ∀ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (la : A ⟶ B) (mu : B ⟶ A) (d M : ℕ) (T : Over S), IsMonHom la → IsMonHom mu → la ≫ mu = 𝟙 A ^ d → mu ≫ la = 𝟙 B ^ d → M.Coprime d → (∀ y : T ⟶ A, y ^ M = 1 → y ≫ la = 1 → y = 1) ∧ (∀ g : T ⟶ B, g ^ M = 1 → ∃ y : T ⟶ A, y ^ M = 1 ∧ y ≫ la = g) := by
  first | (exact @GlobalTheory.isogeny_torsion_bij) | (exact GlobalTheory.isogeny_torsion_bij) | (intros; apply GlobalTheory.isogeny_torsion_bij <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductMkPointBasicFactsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhinProductMkPoint_basic_facts : ∀ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T T' : Over S} (f : T' ⟶ T) (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (g : T ⟶ GlobalTheory.ZarhinFam.Zob A B) (n : ℕ), f ≫ GlobalTheory.ZarhinFam.mkZ A B u v = GlobalTheory.ZarhinFam.mkZ A B (fun i => f ≫ u i) (fun j => f ≫ v j) ∧ GlobalTheory.ZarhinFam.mkZ A B u v ^ n = GlobalTheory.ZarhinFam.mkZ A B (fun i => u i ^ n) (fun j => v j ^ n) ∧ (GlobalTheory.ZarhinFam.mkZ A B u v = 1 ↔ (∀ i, u i = 1) ∧ ∀ j, v j = 1) ∧ g = GlobalTheory.ZarhinFam.mkZ A B (fun i => g ≫ GlobalTheory.ZarhinFam.pa A B i) (fun j => g ≫ GlobalTheory.ZarhinFam.pb A B j) := by
  first | (exact @GlobalTheory.ZarhinFam.PtFacts.mkZ_facts) | (exact GlobalTheory.ZarhinFam.PtFacts.mkZ_facts) | (intros; apply GlobalTheory.ZarhinFam.PtFacts.mkZ_facts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinSymplecticTransferBijectiveMod

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem omegaStd_nsmul_left' {h : ℕ} (M : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    omegaStd (M • a) b = (M : ℤ) * omegaStd a b := by
  unfold omegaStd
  simp only [Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem omegaStd_single_inr {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (Sum.inr i) 1) = a (Sum.inl i) := by
  simp [omegaStd, Pi.single_apply]

theorem omegaStd_single_inl {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (Sum.inl i) 1) = -a (Sum.inr i) := by
  simp [omegaStd, Pi.single_apply]

theorem kappaOK_dvd_iff {h M d : ℕ} {κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)}
    (hκ : KappaOK h M d κ) (a : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    (∀ k, ∃ b, κ k a = M • b) ↔ ∃ b, a = M • b := by
  constructor
  · intro hk
    choose c hc using hk
    have hdiv : ∀ b, (M : ℤ) ∣ omegaStd a b := by
      intro b
      have h2 : (M : ℤ) ∣ formZ d h (fun k => κ k a) (fun k => κ k b) := by
        unfold formZ
        refine Finset.dvd_sum fun k _ => Finset.dvd_sum fun l _ => ?_
        dsimp only
        rw [hc k, omegaStd_nsmul_left']
        exact Dvd.intro (form d (sig k) (sig l) * omegaStd (c k) (κ l b)) (by ring)
      have := dvd_add (hκ.1 a b).dvd h2
      simpa using this
    have hx : ∀ x, (M : ℤ) ∣ a x := by
      rintro (i | i)
      · simpa [omegaStd_single_inr] using hdiv (Pi.single (Sum.inr i) 1)
      · simpa [omegaStd_single_inl] using hdiv (Pi.single (Sum.inl i) 1)
    exact ⟨fun x => a x / M, funext fun x => by simp [Int.mul_ediv_cancel' (hx x)]⟩
  · rintro ⟨b, rfl⟩ k
    exact ⟨κ k b, map_nsmul _ _ _⟩

theorem kappaOK_mod (h M d : ℕ) (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ))
    (hM : 1 ≤ M) (hκ : KappaOK h M d κ) :
    (∀ a, (∀ k, ∃ b, κ k a = M • b) ↔ ∃ b, a = M • b) ∧
      ∀ cc : Fin 8 → (Fin h ⊕ Fin h → ℤ), ∃ a, ∀ k, ∃ b, κ k a = cc k + M • b := by
  refine ⟨kappaOK_dvd_iff hκ, ?_⟩
  haveI : NeZero M := ⟨by omega⟩
  let f : (Fin (8 * h) ⊕ Fin (8 * h) → ZMod M) → (Fin 8 → Fin h ⊕ Fin h → ZMod M) :=
    fun x k j => ((κ k (fun i => ((x i).val : ℤ)) j : ℤ) : ZMod M)
  have hinj : Function.Injective f := by
    intro x y hxy
    let a : Fin (8 * h) ⊕ Fin (8 * h) → ℤ := fun i => ((x i).val : ℤ) - ((y i).val : ℤ)
    have hk : ∀ k, ∃ b, κ k a = M • b := by
      intro k
      have hj : ∀ j, (M : ℤ) ∣ κ k a j := by
        intro j
        have e := congrFun (congrFun hxy k) j
        simp only [f] at e
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have ha : a = (fun i => ((x i).val : ℤ)) - (fun i => ((y i).val : ℤ)) := rfl
        rw [ha, map_sub, Pi.sub_apply, Int.cast_sub, e, sub_self]
      exact ⟨fun j => κ k a j / M, funext fun j => by simp [Int.mul_ediv_cancel' (hj j)]⟩
    obtain ⟨b, hb⟩ := (kappaOK_dvd_iff hκ a).1 hk
    funext i
    have e := congrFun hb i
    have h2 : ((a i : ℤ) : ZMod M) = 0 := by rw [e]; simp
    simp [a] at h2
    exact sub_eq_zero.mp h2
  have hcard : Fintype.card (Fin (8 * h) ⊕ Fin (8 * h) → ZMod M) =
      Fintype.card (Fin 8 → Fin h ⊕ Fin h → ZMod M) := by
    simp only [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, ZMod.card]
    rw [← pow_mul]
    congr 1
    ring
  have hbij := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  intro cc
  obtain ⟨x, hx⟩ := hbij.2 (fun k j => (cc k j : ZMod M))
  refine ⟨fun i => ((x i).val : ℤ), fun k => ?_⟩
  have hj : ∀ j, (M : ℤ) ∣ κ k (fun i => ((x i).val : ℤ)) j - cc k j := by
    intro j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
    have e := congrFun (congrFun hx k) j
    simp only [f] at e
    rw [e, sub_self]
  refine ⟨fun j => (κ k (fun i => ((x i).val : ℤ)) j - cc k j) / M, funext fun j => ?_⟩
  rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Int.mul_ediv_cancel' (hj j)]
  ring

end GlobalTheory.ZarhinFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinSymplecticTransferBijectiveModStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhinSymplecticTransfer_bijective_mod : ∀ (h M d : ℕ) (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), 1 ≤ M → GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a, (∀ k, ∃ b, κ k a = M • b) ↔ ∃ b, a = M • b) ∧ ∀ cc : Fin 8 → (Fin h ⊕ Fin h → ℤ), ∃ a, ∀ k, ∃ b, κ k a = cc k + M • b := by
  first | (exact @GlobalTheory.ZarhinFam.kappaOK_mod) | (exact GlobalTheory.ZarhinFam.kappaOK_mod) | (intros; apply GlobalTheory.ZarhinFam.kappaOK_mod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickLevelSymplecticGeometricPoints

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam

theorem siegPre_lev_nsmul {S : Scheme.{0}} {h M : ℕ} {Bs : Type} [CommRing Bs] {ζ : Bs} {s : S ⟶ Sp Bs}
    (c : SiegPre h M ζ s) (n : ℕ) (b : Fin h ⊕ Fin h → ℤ) : c.lev (n • b) = c.lev b ^ n := by
  have h0 : c.lev 0 = 1 := by
    have := c.lev_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, c.lev_add, ih, pow_succ]

theorem geom_levZ : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β → (z : k) = β (zetaAway M) → (∀ a, (toUnit (Over.mk x) ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a = 1 ↔ ∃ b, a = M • b)) ∧ (∀ g : Over.mk x ⟶ (GlobalTheory.ZarhinFam.Zob c.A B), g ^ M = 1 → ∃ a, toUnit _ ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a = g) ∧ ∀ a b, Out.WeilIs (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) M (toUnit (Over.mk x) ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a) (toUnit _ ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) (unitOn (z ^ (2 * omegaStd a b))) := by
  intro h M d S t c B _ _ Q la mu hZ hh hM hMo hd hcop hdu hker κ hκ k _ _ x β z hx hz
  have hla : IsMonHom la := hZ.2.2.2.1
  have hmu : IsMonHom mu := hZ.2.2.2.2.1
  have hlm : la ≫ mu = 𝟙 c.A ^ d := hZ.2.2.2.2.2.1
  have hml : mu ≫ la = 𝟙 B ^ d := hZ.2.2.2.2.2.2.1
  set X : Over.mk x ⟶ 𝟙_ (Over S) := toUnit (Over.mk x) with hXdef
  have hpt : ∀ a, X ≫ levZ c.lev (incZ c.A B) (actZ c.A B d la mu) (oMat d) κ a =
      mkZ c.A B (fun i => X ≫ c.lev (κ (Fin.castAdd 4 i) a)) (fun j => X ≫ c.lev (κ (Fin.natAdd 4 j) a) ≫ la) := by
    intro a
    rw [GlobalTheory.T.zarhinProductLevelStructure_eq_mkPoint c.A B d h (8 * h) la mu c.lev κ a]
    exact (GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B X _ _ 1 1).1
  have geo := c.geom k x β z hx hz
  have geo1 : ∀ q, X ≫ c.lev q = 1 ↔ ∃ b, q = M • b := geo.1
  have htA := GlobalTheory.T.isogeny_bijective_on_torsion_coprime_degree c.A B la mu d M (Over.mk x) hla hmu hlm hml hcop
  have hK := GlobalTheory.T.zarhinSymplecticTransfer_bijective_mod h M d κ (by omega) hκ
  have htor : ∀ q, (X ≫ c.lev q) ^ M = 1 := fun q => by rw [← comp_pow, c.lev_tors, comp_one]
  have hlev1 : ∀ q, (X ≫ c.lev q ≫ la = 1 ↔ X ≫ c.lev q = 1) := fun q => by
    constructor
    · intro e
      exact htA.1 _ (htor q) (by rw [Category.assoc]; exact e)
    · intro e
      rw [← Category.assoc, e, one_comp]
  have hlevM : ∀ q b, c.lev (q + M • b) = c.lev q := fun q b => by
    rw [c.lev_add, siegPre_lev_nsmul, c.lev_tors, _root_.mul_one]
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  ·
    rw [hpt a, (GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B (𝟙 _) (fun i => X ≫ c.lev (κ (Fin.castAdd 4 i) a))
      (fun j => X ≫ c.lev (κ (Fin.natAdd 4 j) a) ≫ la) 1 1).2.2.1, ← (hK.1 a)]
    simp only [hlev1, geo1]
    exact (Fin.forall_fin_add (m := 4) (n := 4) (fun k : Fin 8 => ∃ b, κ k a = M • b)).symm
  ·
    obtain ⟨-, hpow, hone, hg'⟩ := GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B (𝟙 _) (fun i => g ≫ pa c.A B i) (fun j => g ≫ pb c.A B j) g M
    have hgM : mkZ c.A B (fun i => (g ≫ pa c.A B i) ^ M) (fun j => (g ≫ pb c.A B j) ^ M) = 1 := by
      rw [← hpow, ← hg', hg]
    obtain ⟨hu, hv⟩ := (GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B (𝟙 _) (fun i => (g ≫ pa c.A B i) ^ M) (fun j => (g ≫ pb c.A B j) ^ M) g M).2.2.1.1 hgM
    have eu : ∀ i, ∃ q, X ≫ c.lev q = g ≫ pa c.A B i := fun i => geo.2.1 _ (hu i)
    have ev : ∀ j, ∃ q, X ≫ c.lev q ≫ la = g ≫ pb c.A B j := fun j => by
      obtain ⟨y, hyM, hy⟩ := htA.2 _ (hv j)
      obtain ⟨q, hq⟩ := geo.2.1 y hyM
      exact ⟨q, by rw [← Category.assoc, hq, hy]⟩
    choose qa hqa using eu
    choose qb hqb using ev
    let cc : Fin 8 → (Fin h ⊕ Fin h → ℤ) := fun k =>
      Fin.addCases (m := 4) (n := 4) (motive := fun _ => Fin h ⊕ Fin h → ℤ) qa qb k
    obtain ⟨a, ha⟩ := hK.2 cc
    refine ⟨a, ?_⟩
    rw [hpt a, hg']
    congr 1
    · funext i
      obtain ⟨b, hb⟩ := ha (Fin.castAdd 4 i)
      rw [hb, hlevM]
      exact (congrArg (X ≫ c.lev ·) (Fin.addCases_left (motive := fun _ => Fin h ⊕ Fin h → ℤ) (left := qa) (right := qb) i)).trans (hqa i)
    · funext j
      obtain ⟨b, hb⟩ := ha (Fin.natAdd 4 j)
      rw [hb, hlevM]
      exact (congrArg (fun q => X ≫ c.lev q ≫ la) (Fin.addCases_right (motive := fun _ => Fin h ⊕ Fin h → ℤ) (left := qa) (right := qb) j)).trans (hqb j)
  ·
    rw [hpt a, hpt b]
    have W := GlobalTheory.T.weilPairing_diagonal_zarhinBundle_eq_zeta_pow h M d S t c B Q la mu hZ hh hM hMo hd hcop hdu hker k x β z hx hz
      (fun k => κ k a) (fun k => κ k b)
    have hzM : z ^ M = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, hz, ← map_pow, zetaAway_pow_self (by omega : M ≠ 0), map_one, Units.val_one]
    obtain ⟨m, hm⟩ := (hκ.1 a b).symm.dvd
    have e : z ^ (2 * formZ d h (fun k => κ k a) (fun k => κ k b)) = z ^ (2 * omegaStd a b) := by
      have : 2 * formZ d h (fun k => κ k a) (fun k => κ k b) = 2 * omegaStd a b + (M : ℤ) * (2 * m) := by
        linear_combination 2 * hm
      rw [this, zpow_add, zpow_mul z (M : ℤ), zpow_natCast, hzM, one_zpow, _root_.mul_one]
    rw [e] at W
    exact W

end GlobalTheory.ZarhinFam
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickLevelSymplecticGeometricPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhinTrick_level_symplectic_geometricPoints : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β → (z : k) = β (zetaAway M) → (∀ a, (toUnit (Over.mk x) ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a = 1 ↔ ∃ b, a = M • b)) ∧ (∀ g : Over.mk x ⟶ (GlobalTheory.ZarhinFam.Zob c.A B), g ^ M = 1 → ∃ a, toUnit _ ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a = g) ∧ ∀ a b, Out.WeilIs (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) M (toUnit (Over.mk x) ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a) (toUnit _ ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) (unitOn (z ^ (2 * omegaStd a b))) := by
  first | (exact @GlobalTheory.ZarhinFam.geom_levZ) | (exact GlobalTheory.ZarhinFam.geom_levZ) | (intros; apply GlobalTheory.ZarhinFam.geom_levZ  <;> assumption)
end
end
