module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationWeilPairingProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplecticStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientFreeRankTwiceDimensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WpQTrivRight
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesOfExpansionLaws
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingLevelPushEqPow

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SympQ.PushPow

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem cubN_mul_iter (h : IsCub θ) (n m : ℕ) (b x : A) :
    cubN θ (n * m) 1 b x = cubN θ n 1 (b ^ m) x * cubN θ m 1 b x ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e : cubN θ ((n + 1) * m) 1 b x = cubN θ (n * m) 1 b x * cubN θ m (b ^ (n * m)) b x := by
      rw [Nat.succ_mul]
      simp only [cubN, Finset.prod_range_add]
      refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
      rw [_root_.one_mul, pow_add]
    have s1 : cubN θ (n + 1) 1 (b ^ m) x = cubN θ n 1 (b ^ m) x * θ ((b ^ m) ^ n) (b ^ m) x := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    rw [e, ih, h.N_split m (b ^ (n * m)) b x, s1, ← pow_mul' b n m, pow_succ (cubN θ m 1 b x) n]
    ac_rfl

theorem cubN_pow_right (h : IsCub θ) (k m : ℕ) (b x : A) :
    cubN θ k 1 b (x ^ m) * cubN θ m 1 x b ^ k = cubN θ k 1 b x ^ m * cubN θ m 1 x (b ^ k) := by
  induction m with
  | zero => simp [cubN, h.face₃]
  | succ m ih =>
    have e := h.N_add k 1 b (x ^ m) x
    rw [h.face, _root_.mul_one, _root_.one_mul] at e
    have s1 : cubN θ (m + 1) 1 x b = cubN θ m 1 x b * θ (x ^ m) x b := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have s2 : cubN θ (m + 1) 1 x (b ^ k) = cubN θ m 1 x (b ^ k) * θ (x ^ m) x (b ^ k) := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have t1 : θ b (x ^ m) x = θ (x ^ m) x b := by rw [h.s01, h.s12]
    have t2 : θ (b ^ k) (x ^ m) x = θ (x ^ m) x (b ^ k) := by rw [h.s01, h.s12]
    rw [t1, t2] at e
    rw [pow_succ x, s1, s2]
    apply Additive.ofMul.injective
    replace e := congrArg Additive.ofMul e
    replace ih := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow] at e ih ⊢
    linear_combination (norm := module) e + ih

variable {O : Type} [CommRing O] (N : NumD O)

theorem wp_pushRep (n m : ℕ) (hn : 0 < n) (p q : N.QT (n * m)) :
    N.wp (pushRep N (n * m) n p) (pushRep N (n * m) n q) = N.wp p q ^ m := by
  have hd : n ∣ n * m := dvd_mul_right n m
  have hM : n * m / n = m := Nat.mul_div_cancel_left m hn
  simp only [NumD.wp, NumD.tk, pushRep_fst N hd, pushRep_snd N hd, hM, NumD.Gt.pow_b]
  have ps1 := NumD.Gt.pow_s p.1.2 m q.1.1.toAdd
  have ps2 := NumD.Gt.pow_s q.1.2 m p.1.1.toAdd
  rw [← N.QT_pow_b q] at ps1
  rw [← N.QT_pow_b p] at ps2
  have i1 := cubN_mul_iter N.cub n m q.1.2.b p.1.2.b
  have i2 := cubN_mul_iter N.cub n m p.1.2.b q.1.2.b
  have a := cubN_pow_right N.cub n m (p.1.2.b ^ m) q.1.2.b
  have b := cubN_pow_right N.cub n m (q.1.2.b ^ m) p.1.2.b
  have c := cubN_pow_right N.cub m m q.1.2.b p.1.2.b
  rw [← pow_mul'] at a b
  apply Additive.ofMul.injective
  replace ps1 := congrArg Additive.ofMul ps1
  replace ps2 := congrArg Additive.ofMul ps2
  replace i1 := congrArg Additive.ofMul i1
  replace i2 := congrArg Additive.ofMul i2
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at ps1 ps2 i1 i2 a b c ⊢
  linear_combination (norm := module) ps1 - ps2 - (m : ℤ) • i1 + (m : ℤ) • i2 + b - a + (n : ℤ) • c

end GlobalTheory.SympQ.PushPow

theorem GlobalTheory.SympQ.wp_pushRep_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n m : ℕ), 0 < n → 0 < m → ∀ p q : N.QT (n * m), N.wp (GlobalTheory.SympQ.pushRep N (n * m) n p) (GlobalTheory.SympQ.pushRep N (n * m) n q) = N.wp p q ^ m := by
  intro R _ _ _ _ D F _ _ _ N ν n m hn hm p q
  exact GlobalTheory.SympQ.PushPow.wp_pushRep N n m hn p q
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingLevelPushEqPowStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.reprModTrivialQuotient_pairing_levelPush_eq_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n m : ℕ), 0 < n → 0 < m → ∀ p q : N.QT (n * m), N.wp (GlobalTheory.SympQ.pushRep N (n * m) n p) (GlobalTheory.SympQ.pushRep N (n * m) n q) = N.wp p q ^ m := by
  first | exact @GlobalTheory.SympQ.wp_pushRep_pow | exact GlobalTheory.SympQ.wp_pushRep_pow | (intros; apply GlobalTheory.SympQ.wp_pushRep_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingNondegenerate

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.SympQ

theorem qEq_one_of_wp {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ} (hk : (k : C) ≠ 0)
    (hdiv : ∀ x : N.A, ∃ y, y ^ k = x)
    (nd : ∀ b : N.A, b ^ k = 1 → (∀ b', b' ^ k = 1 → N.weil k b b' = 1) → b = 1) (p : N.QT k)
    (hp : ∀ p', N.wp p p' = 1) : N.QEq p 1 := by
  have hk0 : k ≠ 0 := fun h => hk (by rw [h, Nat.cast_zero])
  have h3 : ∀ y : N.X, ∃ p : N.QT k, p.1.1.toAdd = y := fun y => by
    obtain ⟨b, hb⟩ := hdiv (N.io y).b
    obtain ⟨g, -, h⟩ := QStr.root_over N hk0 (N.io y) b hb
    exact ⟨⟨(Multiplicative.ofAdd y, g), h⟩, rfl⟩
  obtain ⟨p₀, hq, h1, hb⟩ := (QStr.orth_iff N hk nd p).1 fun p' _ => hp p'
  have : p₀ = 1 := by
    refine Subtype.ext (Prod.ext h1 (NumD.Gt.ext hb (funext fun χ => ?_)))
    obtain ⟨p', rfl⟩ := h3 χ
    rw [← (WpPairing.wp_pairing C N _ p₀ p' p').2.2.2.2.2.1 h1 hb, ← WpPairing.wp_congr_left N hq p', hp p']
    rfl
  rwa [this] at hq

theorem wpQ_nondeg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → ∀ x : GlobalTheory.SympQ.Qq N n, (∀ y, GlobalTheory.SympQ.wpQ N n x y = 1) → x = 1 := by
  intro R _ _ _ hR D F _ _ _ N ν n hn x hx
  obtain ⟨⟨h1, h2, h3, h4⟩, hc⟩ := hR
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  have : CharZero F := by
    have : CharZero (FractionRing R) := inferInstance
    exact charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have h0 : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨hW, -⟩ := GlobalTheory.ThetaInValues.brUth_of_laws hL R D.toPre D.psi_even D.tau_bimult F N ν
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  induction x using QuotientGroup.induction_on with
  | H p =>
    have hq : N.QEq p 1 := by
      refine qEq_one_of_wp N h0 (fun a => ?_) (fun b hb h => ?_) p fun p' => hx (QuotientGroup.mk p')
      · obtain ⟨y, hy⟩ := GlobalTheory.ValuesTorsion.exists_pow_eq hL D.toPre.P (jFK (R := R) F ≫ jK R) (ν.eA a) hn
        exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
      · refine ν.eA.map_eq_one_iff.1 (GlobalTheory.ThetaRep.eq_one_of_weilIs hL D.toPre.P (jFK (R := R) F ≫ jK R) h0 _
          ((tor _ _).2 hb) fun y hy => ?_)
        obtain ⟨b', rfl⟩ := ν.eA.surjective y
        have hb' := (tor _ _).1 hy
        have := hW n hn b b' hb hb'
        rwa [h b' hb', show unitOn (1 : Fˣ) = 1 from map_one (Units.map _)] at this
    exact (qEq_iff_mk_eq N p 1).1 hq

end GlobalTheory.SympQ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingNondegenerateStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.reprModTrivialQuotient_pairing_nondegenerate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → ∀ x : GlobalTheory.SympQ.Qq N n, (∀ y, GlobalTheory.SympQ.wpQ N n x y = 1) → x = 1 := by
  first | exact @GlobalTheory.SympQ.wpQ_nondeg | exact GlobalTheory.SympQ.wpQ_nondeg | (intros; apply GlobalTheory.SympQ.wpQ_nondeg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplecticBasesLevelPoints

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.SympQ.compatible_symplectic_bases : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ g : ℕ, g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → ∃ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) ∧ (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) ∧ (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) ∧ ∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F) := by
  intro R _ _ _ hR D F _ _ _ ζ hζ hζc g hg
  subst hg
  have hL : Laws := GlobalTheory.allSixLaws.1
  have gt : GlobalTheory.Ex.BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  have wp : GlobalTheory.Ex.BrWpSt := GlobalTheory.WeilValues.weil_eq_values gt (GlobalTheory.Ex.brFam hL GlobalTheory.allSixLaws.2.1)
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, ν, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL R D.toPre D.psi_even D.tau_bimult F ⊤ (fun _ => trivial)
  obtain ⟨-, -, gAdd, -, gQ⟩ := gt R D.toPre D.psi_even D.tau_bimult F N ν
  have hW := wp R D.toPre D.psi_even D.tau_bimult F N ν
  have hcl : ∀ n (p p' : QkPt D.toPre F n) v v', ν.QPt p v → ν.QPt p' v' →
      (QkPt.Equiv D.toPre F p p' ↔ (QuotientGroup.mk v : GlobalTheory.SympQ.Qq N n) = QuotientGroup.mk v') :=
    fun n p p' v v' h h' => ((gQ n).2.2 p p' v v' h h').trans (GlobalTheory.SympQ.qEq_iff_mk_eq N v v')
  have h1 : ∀ n (x y z : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n (x + y).toMul z.toMul = GlobalTheory.SympQ.wpQ N n x.toMul z.toMul * GlobalTheory.SympQ.wpQ N n y.toMul z.toMul := by
    intro n x y z
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨p'', hp''⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
    simp only [toMul_add]
    rw [← hp, ← hp', ← hp'', ← QuotientGroup.mk_mul, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk,
      GlobalTheory.Ex.WpPairing.wp_mul_left]
  have h2 : ∀ n (x y z : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n x.toMul (y + z).toMul = GlobalTheory.SympQ.wpQ N n x.toMul y.toMul * GlobalTheory.SympQ.wpQ N n x.toMul z.toMul := by
    intro n x y z
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨p'', hp''⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
    simp only [toMul_add]
    rw [← hp, ← hp', ← hp'', ← QuotientGroup.mk_mul, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk,
      GlobalTheory.Ex.WpPairing.wp_mul_right]
  have h3 : ∀ n (x : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n x.toMul x.toMul = 1 := by
    intro n x
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    rw [← hp, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.Ex.NumD.wp_self]
  have h4 : ∀ n, 0 < n → ∀ x : Additive (GlobalTheory.SympQ.Qq N n), (∀ y : Additive (GlobalTheory.SympQ.Qq N n), GlobalTheory.SympQ.wpQ N n x.toMul y.toMul = 1) → x = 0 := by
    intro n hn x hx
    exact Additive.toMul.injective (GlobalTheory.T.reprModTrivialQuotient_pairing_nondegenerate R hR D F N ν n hn x.toMul fun y => hx (Additive.ofMul y))
  have h5 : ∀ n m, 0 < n → 0 < m → ∀ x y : Additive (GlobalTheory.SympQ.Qq N (n * m)), GlobalTheory.SympQ.wpQ N n ((GlobalTheory.SympQ.pushQ N (n * m) n).toAdditive x).toMul ((GlobalTheory.SympQ.pushQ N (n * m) n).toAdditive y).toMul = GlobalTheory.SympQ.wpQ N (n * m) x.toMul y.toMul ^ m := by
    intro n m hn hm x y
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    change GlobalTheory.SympQ.wpQ N n (GlobalTheory.SympQ.pushQ N (n * m) n x.toMul) (GlobalTheory.SympQ.pushQ N (n * m) n y.toMul) =
      GlobalTheory.SympQ.wpQ N (n * m) x.toMul y.toMul ^ m
    rw [← hp, ← hp', GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk]
    exact GlobalTheory.T.reprModTrivialQuotient_pairing_levelPush_eq_pow R hR D F N ν n m hn hm p p'
  have h6 : ∀ M n k, 0 < k → 0 < M → k ∣ n → n ∣ M → ∀ x : Additive (GlobalTheory.SympQ.Qq N M), (GlobalTheory.SympQ.pushQ N n k).toAdditive ((GlobalTheory.SympQ.pushQ N M n).toAdditive x) = (GlobalTheory.SympQ.pushQ N M k).toAdditive x := by
    intro M n k hk hM hkn hnM x
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    apply Additive.toMul.injective
    change GlobalTheory.SympQ.pushQ N n k (GlobalTheory.SympQ.pushQ N M n x.toMul) = GlobalTheory.SympQ.pushQ N M k x.toMul
    rw [← hp, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk]
    congr 1
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rw [GlobalTheory.SympQ.pushRep_fst N hkn, GlobalTheory.SympQ.pushRep_fst N hnM, GlobalTheory.SympQ.pushRep_fst N (hkn.trans hnM)]
    · have e : M / n * (n / k) = M / k := by
        obtain ⟨b, rfl⟩ := hkn
        obtain ⟨a, rfl⟩ := hnM
        have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
        rw [Nat.mul_div_cancel_left _ (Nat.mul_pos hk hb), Nat.mul_div_cancel_left _ hk, Nat.mul_assoc,
          Nat.mul_div_cancel_left _ hk, Nat.mul_comm]
      rw [GlobalTheory.SympQ.pushRep_snd N hkn, GlobalTheory.SympQ.pushRep_snd N hnM, GlobalTheory.SympQ.pushRep_snd N (hkn.trans hnM), ← pow_mul, e]
  obtain ⟨ev', hker, hsurj, htow, hweil⟩ := GlobalTheory.T.exists_compatible_symplectic_alt F ζ hζ hζc (D.toPre.P.g + Module.finrank ℤ D.toPre.X)
    (fun n => Additive (GlobalTheory.SympQ.Qq N n)) (fun n x y => GlobalTheory.SympQ.wpQ N n x.toMul y.toMul)
    (fun M n => (GlobalTheory.SympQ.pushQ N M n).toAdditive) (GlobalTheory.T.reprModTrivialQuotient_free_rank_twice_dimension R hR D F N ν) h1 h2 h3 h4 h5 h6
  have hrep : ∀ n a, ∃ q : N.QT n, (QuotientGroup.mk q : GlobalTheory.SympQ.Qq N n) = (ev' n a).toMul :=
    fun n a => QuotientGroup.mk_surjective _
  choose q hq using hrep
  choose P hP using fun n a => (gQ n).2.1 (q n a)
  refine ⟨P, fun n hn a b => ?_, fun n hn a b => ?_, fun n hn p => ?_, fun n m hn hm a => ?_, fun n hn a b => ?_⟩
  · obtain ⟨r, hr⟩ := (gQ n).2.1 (q n a * q n b)
    refine ⟨r, ?_, (gAdd _ _ _ _ _ _ (hP n a).2 (hP n b).2 hr.2).2 rfl, ?_⟩
    · rw [← hr.1, ← (hP n a).1, ← (hP n b).1, ← map_add (f := _)]
      rfl
    · rw [hcl n _ _ _ _ hr (hP n (a + b)), QuotientGroup.mk_mul, hq, hq, hq, map_add (f := _), toMul_add]
  · rw [hcl n _ _ _ _ (hP n a) (hP n b), hq, hq, Additive.toMul.injective.eq_iff]
    exact hker n hn a b
  · obtain ⟨v, hv⟩ := ((gQ n).1 p).exists
    obtain ⟨a, ha⟩ := hsurj n hn (Additive.ofMul (QuotientGroup.mk v))
    exact ⟨a, (hcl n _ _ _ _ (hP n a) hv).2 (by rw [hq, ha]; rfl)⟩
  · have hd : n ∣ n * m := dvd_mul_right n m
    obtain ⟨r, hr⟩ := (gQ n).2.1 (GlobalTheory.SympQ.pushRep N (n * m) n (q (n * m) a))
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [← hr.1, ← (hP (n * m) a).1, GlobalTheory.SympQ.pushRep_fst N hd]
    · refine (GlobalTheory.Ex.GtValues.isNsmul_val ν m (hP (n * m) a).2 hr.2).2 ?_
      rw [GlobalTheory.SympQ.pushRep_snd N hd, Nat.mul_div_cancel_left m hn]
    · rw [hcl n _ _ _ _ hr (hP n a), ← GlobalTheory.SympQ.pushQ_mk, hq, hq, ← htow n m hn hm a]
      rfl
  · refine (hW n hn (P n a) (P n b) (q n a) (q n b) _ (hP n a) (hP n b)).2 ?_
    rw [← GlobalTheory.SympQ.wpQ_mk, hq, hq]
    exact congrArg Units.val (hweil n hn a b).symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplecticBasesLevelPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_compatible_symplectic_bases_levelPoints : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ g : ℕ, g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → ∃ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) ∧ (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) ∧ (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) ∧ ∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F) := by
  first | exact @GlobalTheory.SympQ.compatible_symplectic_bases | exact GlobalTheory.SympQ.compatible_symplectic_bases | (intros; apply GlobalTheory.SympQ.compatible_symplectic_bases <;> assumption)
end
end
