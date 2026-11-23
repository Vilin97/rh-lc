module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupAbelianWhereTrivialisationsUnitsStatement
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtension
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalMumfordFamilyMonomialPeriodsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NTorsionRationalCanonicalFamilyDividedData
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XMemNonZeroDivisors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Mathlib.Algebra.Order.Star.Int
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibresAbelianOfPsiUnitOn

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UnifFibre

theorem fibres_abelian_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G :=
  fun R _ _ _ hB D A G _ _ hG U W hW => GlobalTheory.T.uniformised_group_abelian_where_trivialisations_units R hB D A G hG U W hW

end GlobalTheory.Mum.UnifFibre
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyBoundaryDivisor

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegChart

theorem isAdmissibleBase_of_completeNormalLocalCharZero {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (hA : IsCN A) : LN.admitted A (maximalIdeal A) :=
  ⟨admissibleBase_of_completeNormalLocalCharZero hA, hA.2.2.1, hA.2.2.2, inferInstance, inferInstanceAs (IsIntegrallyClosed (ResidueField A))⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

end GlobalTheory.SiegChart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbLocusIffOfMonomialTau

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.MonoAb

theorem exists_pos_of_ne_zero {X : Type} [AddCommGroup X] (d : LinearMap.BilinForm ℤ X)
    (hs : ∀ a b, d a b = d b a) (hn : ∀ a, 0 ≤ d a a) (h : d ≠ 0) : ∃ y, 0 < d y y := by
  by_contra hc
  push_neg at hc
  apply h
  ext a b
  have h1 := hc (a + b)
  have h2 : d a a = 0 := le_antisymm (hc a) (hn a)
  have h3 : d b b = 0 := le_antisymm (hc b) (hn b)
  have h4 := hn (a + b)
  have h5 : d (a + b) (a + b) = 0 := le_antisymm h1 h4
  simp only [map_add (f := _), LinearMap.add_apply, h2, h3, hs b a] at h5
  simp only [LinearMap.zero_apply]
  omega

end GlobalTheory.Mum.MonoAb

theorem GlobalTheory.Mum.abLocus_iff_of_monomialTau : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsMumPol Q G P → ∀ (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k, t k ∈ maximalIdeal R ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → (∀ k, δ k ≠ 0) → Q.IsMonomialTau t δ → ∀ p : Sp R, p ∈ abLocus G ↔ ∏ k, t k ∉ p.asIdeal := by
  intro R _ _ _ hR Q _ G _ _ P hM m t δ ht hsymm hnn hdef hne hmono p
  obtain ⟨R', _, _, _, ρ, r, D, e, hR', hinj, hfin, -, hr, href, hmon⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised R Q m t δ hR hmono (fun k => (ht k).1) (fun k => (ht k).2)
      (fun k a b => hsymm k a b) hnn hdef
  obtain ⟨-, -, hG, -, hU⟩ := hM
  obtain ⟨G', _, _, π, -, A, U, hpb, -, -⟩ := hU R' ρ hR' hinj hfin D e href
  have hG' : IsSemiAbelian G' := GlobalTheory.SiegLoc.TraitOrd.isSemiAbelian_of_isGrpPullback hpb hG
  haveI : IsNoetherianRing R' := hR'.1

  obtain ⟨q, hq⟩ : ∃ q : Sp R', spMap ρ q = p := by
    letI := ρ.toAlgebra
    haveI : p.asIdeal.IsPrime := p.isPrime
    haveI : Module.Finite R R' := hfin
    obtain ⟨Q', -, hQ', hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal R') (by
      intro x hx
      have : ρ x = 0 := hx
      rw [show x = 0 from hinj (this.trans (map_zero ρ).symm)]
      exact p.asIdeal.zero_mem)
    exact ⟨⟨Q', hQ'⟩, PrimeSpectrum.ext hc⟩
  subst hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  rw [abLocus_pullback abLocusOne hG hpb.1 q]
  have key : ∏ k, t k ∈ (spMap ρ q).asIdeal ↔ ∏ k, r k ∈ q.asIdeal := by
    show ρ (∏ k, t k) ∈ q.asIdeal ↔ _
    rw [map_prod, show (∏ k, ρ (t k)) = (∏ k, r k) ^ 2 by rw [← Finset.prod_pow]; simp only [hr]]
    exact ⟨fun h => q.isPrime.mem_of_pow_mem 2 h, fun h => Ideal.pow_mem_of_mem _ h 2 (by norm_num)⟩
  rw [key]
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have ho : IsOpen (abLocus G') := GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian G' hG'
  constructor
  · intro hab hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    obtain ⟨y, hy⟩ := GlobalTheory.Mum.MonoAb.exists_pos_of_ne_zero (δ k) (hsymm k) (hnn k) (hne k)
    obtain ⟨u, n, hn, hc⟩ := hmon (e.symm y)
    have hnk : 0 < n k := by
      have := hn k
      simp [pull] at this
      omega
    have hUo := GlobalTheory.PsiAbelian.psiUnitOn_abLocus h1 h2 h3 h4 h5 R' _ (GlobalTheory.SiegChart.isAdmissibleBase_of_completeNormalLocalCharZero hR') D A G' hG' U ho
      (e.symm y)
    refine GlobalTheory.PsiCoordLocal.not_mem_of_coord ho hab hUo hc ?_
    refine Ideal.mul_mem_left _ _ ?_
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
      (Ideal.pow_mem_of_mem _ hk _ hnk)
  · intro hnot
    let W : (Sp R').Opens := ⟨{x | ∏ k, r k ∉ x.asIdeal}, (PrimeSpectrum.basicOpen (∏ k, r k)).isOpen⟩
    exact GlobalTheory.Mum.UnifFibre.fibres_abelian_of_psiUnitOn R' ⟨admissibleBase_of_completeNormalLocalCharZero hR', hR'.2.2.2⟩ D A G' hG' U W
      (fun y => hmon.psiUnitOn y fun x hx => hx) hnot
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NTorsionRationalCanonicalFamilyDividedDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nTorsion_rational_canonicalFamily_dividedData : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → TorsRat G n := by
  first | exact @GlobalTheory.Mum.torsRat_of_canon | exact GlobalTheory.Mum.torsRat_of_canon | (intros; apply GlobalTheory.Mum.torsRat_of_canon <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.TChart

theorem torsRat_of_isGrpPullback_siegPre {S : Scheme.{0}} {h n : ℕ} {o : Type} [CommRing o] {ζ : o} (hζ : IsUnit ζ)
    {s : S ⟶ Sp o} (c : SiegPre h n ζ s) {R : Type} [CommRing R] [IsDomain R] (b : o →+* R) (B : Over (Sp R)) [GrpObj B]
    (f : Sp R ⟶ S) (hf : f ≫ s = spMap b) (β : B.left ⟶ c.A.left) (hβ : IsGrpPullback B c.A f β) : TorsRat B n := by
  intro K _ _ κ x hx
  let b₀ : o →+* K := (κ.comp (algebraMap R (FractionRing R))).comp b
  have hb₀ : ((spMap κ ≫ jK R) ≫ f) ≫ s = spMap b₀ := by
    rw [Category.assoc, hf]
    simp only [b₀, spMap, jK, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  obtain ⟨-, h2, -⟩ := c.geom K ((spMap κ ≫ jK R) ≫ f) b₀ (hζ.map b₀).unit hb₀ rfl
  obtain ⟨a, ha⟩ := h2 (pushHom hβ (Over.mk (spMap κ ≫ jK R)) x) (by rw [← map_pow, hx, map_one])
  have ha' : ((spMap κ ≫ jK R) ≫ f) ≫ (c.lev a).left = x.left ≫ β := congrArg (fun q => q.left) ha
  have hl : (c.lev a).left ≫ c.A.hom = 𝟙 S := Over.w (c.lev a)
  have w : (jK R ≫ f ≫ (c.lev a).left) ≫ c.A.hom = jK R ≫ f := by
    simp only [Category.assoc]
    erw [hl, Category.comp_id]
  refine ⟨Over.homMk (hβ.1.lift (jK R ≫ f ≫ (c.lev a).left) (jK R) w) (hβ.1.lift_snd _ _ _), ?_⟩
  apply hβ.1.hom_ext
  · rw [← ha']
    show _ = (spMap κ ≫ hβ.1.lift _ _ w) ≫ β
    rw [Category.assoc (spMap κ) (hβ.1.lift _ _ w), hβ.1.lift_fst]
    simp only [Category.assoc]
  · show _ = (spMap κ ≫ hβ.1.lift _ _ w) ≫ B.hom
    rw [Category.assoc (spMap κ) (hβ.1.lift _ _ w), hβ.1.lift_snd]
    exact Over.w x

theorem Taut.torsRat_B {o : Type} [CommRing o] {ζ : o} (hζ : IsUnit ζ) {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ) :
    TorsRat C.Q.B n := by
  obtain ⟨β, -, -, hβ, -⟩ := C.data
  refine torsRat_of_isGrpPullback_siegPre hζ C.F.univ C.b C.Q.B _ ?_ _ (IsGrpPullback.comp hβ C.cart)
  have := C.u_base
  rw [LowChart.toO] at this
  rw [Category.assoc, Category.assoc, this]
  simp only [Taut.b, Taut.iw, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

theorem Taut.exists_family : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ C : Taut (zetaAway n) g n φ, ∃ (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P ∧ GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P ∧ (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) ∧ TorsRat G₁ n := by
  intro g n φ hn _ C
  have hn0 : n ≠ 0 := by omega
  have hn1 : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  obtain ⟨hreg, hchar, hinj, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, -, hcone, hdef, ht⟩ := Taut.monomial_chart g n φ (by omega) C
  have hCN : IsCN C.R :=
    ⟨C.compl.1, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R).2, C.compl.2.1, hchar⟩
  have hsym : ∀ k a b, ((n : ℤ) • C.δ k) a b = ((n : ℤ) • C.δ k) b a := fun k a b => by
    simp only [LinearMap.smul_apply, (hcone.mem k).1 a b]
  have hnn : ∀ k a, 0 ≤ ((n : ℤ) • C.δ k) a a := fun k a => by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hn1.le (hcone.nonneg k a)
  have hpos : ∀ a, a ≠ 0 → ∃ k, 0 < ((n : ℤ) • C.δ k) a a := fun a ha => by
    obtain ⟨k, hk⟩ := hdef a ha
    exact ⟨k, by simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_pos hn1 hk⟩
  have hne : ∀ k, (n : ℤ) • C.δ k ≠ 0 := fun k hk => by
    apply C.ε.ne_zero (.inl k)
    apply Subtype.ext
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    have h1 : (n : ℤ) * (C.ε (.inl k) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e (C.e.symm a)) (C.e (C.e.symm b)) = 0 :=
      congrArg (fun B : LinearMap.BilinForm ℤ C.Q.X => B (C.e.symm a) (C.e.symm b)) hk
    rw [C.e.apply_symm_apply, C.e.apply_symm_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left hn1.ne'
  have hQ : C.Q.IsPos (maximalIdeal C.R) := hmono.isPos (fun k => C.bd k) hnn hpos
  obtain ⟨G, _, _, P, hM, hC⟩ := GlobalTheory.T.exists_canonical_mumford_family_monomial_periods C.R hCN C.Q hQ C.m C.t _ hmono ht hsym hnn hpos
  have hζ : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  refine ⟨G, inferInstance, inferInstance, P, hM, hC,
    GlobalTheory.Mum.abLocus_iff_of_monomialTau C.R hCN C.Q hQ G P hM C.m C.t _ (fun k => ⟨C.bd k, ht k⟩) hsym hnn hpos hne hmono, ?_⟩
  exact GlobalTheory.T.nTorsion_rational_canonicalFamily_dividedData C.T C.R _ _ _ n hCN (by omega) (by simpa using (isUnit_natCast hn0).map C.b) (C.b (zetaAway n))
    (hζ.map_of_injective hinj) C.Q C.e C.data (C.torsRat_B (hζ.isUnit hn0)) G P hC.canon

end GlobalTheory.TChart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_mumford_family : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ C : Taut (zetaAway n) g n φ, ∃ (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P ∧ GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P ∧ (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) ∧ TorsRat G₁ n := by
  first | exact @GlobalTheory.TChart.Taut.exists_family | exact GlobalTheory.TChart.Taut.exists_family | (intros; apply GlobalTheory.TChart.Taut.exists_family <;> assumption)
end
end
