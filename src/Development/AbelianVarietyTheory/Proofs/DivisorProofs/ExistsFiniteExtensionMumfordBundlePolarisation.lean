module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGaloisDescentPrincipalPolarisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtIntegralClosure
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteLocalExtensionFractionRingOfGalois

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_finExt_fractionRing_of_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [Algebra (FractionRing R) E], FiniteDimensional (FractionRing R) E → IsGalois (FractionRing R) E → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (t : E →+* FractionRing R'), FinExt ρ ∧ ∀ r : R, t (algebraMap (FractionRing R) E (algebraMap R (FractionRing R) r)) = algebraMap R' (FractionRing R') (ρ r) := by
  intro R _ _ _ hR E _ _ hfd hgal
  letI := hfd
  letI := hgal
  obtain ⟨hloc, hfe⟩ := finExt_integralClosure (E := E) hR
  letI : Algebra R E := (baseMap R E).toAlgebra
  haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : CharZero R := hR.2
  set R₂ := integralClosure R E
  haveI : IsFractionRing R₂ E := integralClosure.isFractionRing_of_finite_extension (FractionRing R) E
  let t : E ≃ₐ[R₂] FractionRing R₂ := IsLocalization.algEquiv (nonZeroDivisors R₂) E (FractionRing R₂)
  refine ⟨R₂, inferInstance, inferInstance, hloc, algebraMap R R₂, t.toRingEquiv.toRingHom, hfe, ?_⟩
  intro r
  have h1 : algebraMap (FractionRing R) E (algebraMap R (FractionRing R) r) = algebraMap R₂ E (algebraMap R R₂ r) := rfl
  rw [h1]
  change t (algebraMap R₂ E _) = _
  rw [AlgEquiv.commutes]

end GlobalTheory.GalClosure
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteLocalExtensionFractionRingOfGaloisStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finiteLocalExtension_fractionRing_of_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [Algebra (FractionRing R) E], FiniteDimensional (FractionRing R) E → IsGalois (FractionRing R) E → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (t : E →+* FractionRing R'), FinExt ρ ∧ ∀ r : R, t (algebraMap (FractionRing R) E (algebraMap R (FractionRing R) r)) = algebraMap R' (FractionRing R') (ρ r) := by
  first | exact @GlobalTheory.GalClosure.exists_finExt_fractionRing_of_galois | exact GlobalTheory.GalClosure.exists_finExt_fractionRing_of_galois | (intros; apply GlobalTheory.GalClosure.exists_finExt_fractionRing_of_galois <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipal

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PrincipalOfPairing

open GlobalTheory.CechPic

theorem lbIso_sq_diag {k : Type} [Field k] [IsAlgClosed k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {L : LB B.left} (hL : L.IsLB) (hs : Out.Sym B L) {P : LB (G2 B).left} (hP : P.IsLB)
    (hiso : LBIso (abelian₂ B L) P) : LBIso (lbPow L 2) (P.pull (lift (𝟙 B) (𝟙 B) : B ⟶ G2 B).left) := by
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hPow : (lbPow L 2).IsLB := LB.isLB_linComb hL _ _
  have hΘ := exists_gen_theta_of_isAbelianScheme k B hB L hL
  have h₀ : pull (1 : B ⟶ B).left (cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨N, hN, e⟩ := cls_surj (pull (η[B]).left (cls L hL))
    have z : cls N hN = 0 := (cls_eq_zero_iff hN).2 (DVR.exists_gen_of_isLB_local (V := k) N hN)
    rw [← e, z, map_zero]
  have h₁ : cls _ hlam = lam (cls L hL) (fst B B) (snd B B) := cls_cube_two hL _ _ hlam
  have h₂ := lam_mul_left hL hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left, lam.eq_1 _ (𝟙 B)⁻¹, inv_mul_cancel, h₀] at h₂
  have h₃ := exists_gen_neg_of_sym GlobalTheory.lawsAndExpansions.1.1.globalFns hB hL hs
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL] at h₃
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id] at h₃
  have einv : GrpObj.inv (X := B) = (𝟙 B)⁻¹ := by simp [Hom.inv_def]
  rw [einv, add_neg_eq_zero] at h₃
  rw [h₃, Over.id_left, pull_id] at h₂
  refine (cls_eq_iff hPow (pull_isLB hP _)).1 ?_
  rw [cls_lbPow hL 2 hPow, cls_pull hP, ← (cls_eq_iff hlam hP).2 hiso, h₁, pull_lam, lift_fst, lift_snd,
    eq_neg_of_add_eq_zero_left h₂.symm, two_smul]
  abel

theorem exists_principal : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∃ L : LB A.left, L.IsLB ∧ Out.Sym A L ∧ LBIso (abelian₂ A L) PP ∧ Out.RelAmple A L ∧ Out.KTriv A L := by
  intro K _ _ _ A _ _ hA P hP hs hb ha hk
  obtain ⟨L, hL, sL, iL⟩ := GlobalTheory.SymBiextHalf.exists_sym_lam K A hA P hP hs hb
  refine ⟨L, hL, sL, iL, ?_, GlobalTheory.KTrivOfLam.kTriv_of_lam_iso _ A hA P hP hk L hL iL⟩
  have := hA.proper
  have hMa := isAmpleLB_of_relAmple_of_isAffine A (pull_isLB hP _) ha
  have h2 : IsAmpleLB (lbPow L 2) := hMa.of_lbIso (isLB_lbPow hL 2) (lbIso_sq_diag hA hL sL hP iL)
  have hLa : IsAmpleLB L := (isAmpleLB_pow_iff hL (by norm_num)).1 h2
  refine relAmple_of_isAmpleLB A hL fun U hU => ?_
  have : CompactSpace (A.hom ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := A.hom) _ U.isOpen hU.isCompact)
  exact hLa.pull_of_isOpenImmersion _

end GlobalTheory.PrincipalOfPairing

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationMumfordBundleAlgClosu

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PrincipalBaseChange

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {f : S' ⟶ S}

theorem lift_comp_sq (w : pullback.fst A.hom f ≫ A.hom = ((Over.pullback f).obj A).hom ≫ f)
    {X : Over S'} (a b : X ⟶ (Over.pullback f).obj A) :
    (lift a b).left ≫ (lift (pushPt w (fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)))
        (pushPt w (snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)))).left =
      (lift (pushPt w a) (pushPt w b)).left := by
  apply pullback.hom_ext
  · change _ ≫ _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst]
    show (lift a b).left ≫ ((fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left ≫ pullback.fst A.hom f) = a.left ≫ pullback.fst A.hom f
    rw [← Category.assoc, ← Over.comp_left, lift_fst]
  · change _ ≫ _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd]
    show (lift a b).left ≫ ((snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left ≫ pullback.fst A.hom f) = b.left ≫ pullback.fst A.hom f
    rw [← Category.assoc, ← Over.comp_left, lift_snd]

theorem lift_comp_sq' (w : pullback.fst A.hom f ≫ A.hom = ((Over.pullback f).obj A).hom ≫ f)
    {X : Over S'} {Y : Over S} (U : Over.mk (X.hom ≫ f) ⟶ Y) (a b : X ⟶ (Over.pullback f).obj A) (c d : Y ⟶ A)
    (ha : pushPt w a = U ≫ c) (hb : pushPt w b = U ≫ d) :
    (lift a b).left ≫ (lift (pushPt w (fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)))
        (pushPt w (snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)))).left =
      U.left ≫ (lift c d).left := by
  rw [lift_comp_sq, ← Over.comp_left, comp_lift, ha, hb]

end GlobalTheory.PrincipalBaseChange

namespace GlobalTheory.PrincipalBaseChange

theorem exists_principal_algClosure : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∃ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB ∧ Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) ∧ Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L := by
  intro K _ _ A _ _ hA PP hP hs hb ha hk Ω _ _ _ κ hκ
  set f := spMap (algebraMap K Ω) with hf
  set AΩ := (Over.pullback f).obj A with hAΩ
  have h := isGrpPullback_pullback A f
  have w := h.1.w
  obtain rfl := GlobalTheory.LamPull.isSquare_unique hκ (GlobalTheory.LamPull.exists_isSquare w)
  have hAΩab : IsAbelianScheme AΩ := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hP' := pull_isLB hP (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left
  have pmul : ∀ {T : Over (Sp Ω)} (x y : T ⟶ AΩ), pushPt w (x * y) = pushPt w x * pushPt w y :=
    fun x y => map_mul (pushHom h _) x y
  refine GlobalTheory.PrincipalOfPairing.exists_principal Ω AΩ hAΩab _ hP' ?_ ?_ ?_ ?_
  · obtain ⟨u, hu⟩ := hs
    refine gen_chartPull (chartPullLinComb PP _ _ _ _ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left fun k => ?_) u hu
    fin_cases k
    · exact lift_comp_sq' w _ (snd AΩ AΩ) (fst AΩ AΩ) (snd A A) (fst A A) (lift_snd _ _).symm (lift_fst _ _).symm
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · obtain ⟨u, hu⟩ := hb
    let U3 : Over.mk ((AΩ ⊗ (AΩ ⊗ AΩ)).hom ≫ f) ⟶ A ⊗ (A ⊗ A) :=
      lift (pushPt w (fst AΩ (AΩ ⊗ AΩ)))
        (lift (pushPt w (snd AΩ (AΩ ⊗ AΩ) ≫ fst AΩ AΩ)) (pushPt w (snd AΩ (AΩ ⊗ AΩ) ≫ snd AΩ AΩ)))
    refine gen_chartPull (chartPullLinComb PP _ _ _ _ U3.left fun k => ?_) u hu
    fin_cases k
    · refine lift_comp_sq' w U3 _ _ _ _ ?_ (by simp [U3])
      rw [comp_mul, pmul]
      simp [U3]
    · exact lift_comp_sq' w U3 _ _ _ _ (by simp [U3]) (by simp [U3])
    · have e1 : snd AΩ (AΩ ⊗ AΩ) = lift (snd AΩ (AΩ ⊗ AΩ) ≫ fst AΩ AΩ) (snd AΩ (AΩ ⊗ AΩ) ≫ snd AΩ AΩ) := by simp
      have e2 : snd A (A ⊗ A) = lift (snd A (A ⊗ A) ≫ fst A A) (snd A (A ⊗ A) ≫ snd A A) := by simp
      show (snd AΩ (AΩ ⊗ AΩ)).left ≫ _ = U3.left ≫ (snd A (A ⊗ A)).left
      rw [e1, e2]
      exact lift_comp_sq' w U3 _ _ _ _ (by simp [U3]) (by simp [U3])
  · have e : (lift (𝟙 AΩ) (𝟙 AΩ)).left ≫ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left =
        pullback.fst A.hom f ≫ (lift (𝟙 A) (𝟙 A)).left := by
      rw [lift_comp_sq' w (pushPt w (𝟙 AΩ)) _ _ (𝟙 A) (𝟙 A) (by simp) (by simp)]
      simp [pushPt]
    refine GlobalTheory.AmpleLocalBase.relAmple_baseChange h.1 (pull_isLB hP _) (pull_isLB hP' _) ?_ ha
    refine LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _)
      (GlobalTheory.Mum.lbIso_pull_pull_comp hP _ _) ?_
    rw [e]
    exact (GlobalTheory.Mum.lbIso_pull_pull_comp hP _ _).symm
  · intro T x ⟨t, ht⟩
    let T₀ : Over (Sp K) := Over.mk (T.hom ≫ f)
    let x₀ : T₀ ⟶ A := pushPt w x
    let sT : Over.mk ((AΩ ⊗ T).hom ≫ f) ⟶ T₀ := Over.homMk (snd AΩ T).left (by
      show (snd AΩ T).left ≫ T.hom ≫ f = (AΩ ⊗ T).hom ≫ f
      rw [← Category.assoc, Over.w (snd AΩ T)])
    let V0 : Over.mk ((AΩ ⊗ T).hom ≫ f) ⟶ A ⊗ T₀ := lift (pushPt w (fst AΩ T)) sT
    have e : (lift (snd AΩ T ≫ x) (fst AΩ T)).left ≫ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left =
        V0.left ≫ (lift (snd A T₀ ≫ x₀) (fst A T₀)).left := by
      refine lift_comp_sq' w V0 _ _ _ _ ?_ (by simp [V0])
      rw [lift_snd_assoc]
      exact Over.OverMorphism.ext (by simp [pushPt, sT, x₀])
    have hV : IsIso V0.left := by
      have e3 : V0.left = (pullbackLeftPullbackSndIso A.hom f T.hom).hom := by
        apply pullback.hom_ext
        · change V0.left ≫ pullback.fst A.hom (T.hom ≫ f) =
            (pullbackLeftPullbackSndIso A.hom f T.hom).hom ≫ pullback.fst A.hom (T.hom ≫ f)
          rw [pullbackLeftPullbackSndIso_hom_fst]
          change V0.left ≫ (fst A T₀).left = _
          rw [← Over.comp_left, lift_fst]
          rfl
        · change V0.left ≫ pullback.snd A.hom (T.hom ≫ f) =
            (pullbackLeftPullbackSndIso A.hom f T.hom).hom ≫ pullback.snd A.hom (T.hom ≫ f)
          rw [pullbackLeftPullbackSndIso_hom_snd]
          change V0.left ≫ (snd A T₀).left = _
          rw [← Over.comp_left, lift_snd]
          rfl
      rw [e3]
      infer_instance
    have g1 := (exists_gen_pull_pull_iff hP _ _).1 ⟨t, ht⟩
    rw [e] at g1
    obtain ⟨t1, ht1⟩ := g1
    obtain ⟨t2, ht2⟩ := gen_chartPull (chartPullPull (PP.pull (V0.left ≫ (lift (snd A T₀ ≫ x₀) (fst A T₀)).left))
      (inv V0.left)) t1 ht1
    have g3 := (exists_gen_pull_pull_iff hP _ (inv V0.left)).1 ⟨t2, ht2⟩
    rw [IsIso.inv_hom_id_assoc] at g3
    have hx0 : x₀ = toUnit T₀ ≫ η[A] := hk T₀ x₀ g3
    have e1 : pushPt w (toUnit T ≫ η[AΩ]) = toUnit T₀ ≫ η[A] := by
      rw [← Hom.one_def, ← Hom.one_def]
      exact map_one (pushHom h T)
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · change x₀.left = (pushPt w (toUnit T ≫ η[AΩ])).left
      rw [hx0, e1]
    · rw [Over.w x, Over.w (toUnit T ≫ η[AΩ])]

end GlobalTheory.PrincipalBaseChange
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationMumfordBundleAlgClosuStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_principalPolarisation_mumfordBundle_algClosure : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∃ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB ∧ Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) ∧ Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L := by
  first | exact @GlobalTheory.PrincipalBaseChange.exists_principal_algClosure | exact GlobalTheory.PrincipalBaseChange.exists_principal_algClosure | (intros; apply GlobalTheory.PrincipalBaseChange.exists_principal_algClosure <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionMumfordBundlePolarisation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumDesc



theorem exists_polAV_field : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∃ (E : Type) (_ : Field E) (_ : Algebra K E), FiniteDimensional K E ∧ IsGalois K E ∧ ∃ (A₁ : PolAV (Sp E)) (gen : (Over.pullback (spMap (algebraMap K E))).obj A ≅ A₁.A), IsMonHom gen.hom ∧ ∀ κ : (G2 ((Over.pullback (spMap (algebraMap K E))).obj A)).left ⟶ (G2 A).left, Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K E))) κ → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K E))).obj A) (A₁.L.pull gen.hom.left)) (PP.pull κ) := by
  intro K _ _ A _ _ hA PP hPP hs ha hm hk
  obtain ⟨κ, hκ⟩ : ∃ κ : (G2 ((Over.pullback (spMap (algebraMap K (AlgebraicClosure K)))).obj A)).left ⟶ (G2 A).left,
      Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K (AlgebraicClosure K)))) κ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare (isGrpPullback_pullback A _).1.w⟩
  obtain ⟨L, hL, hS, hI, hM, hT⟩ := GlobalTheory.T.exists_principalPolarisation_mumfordBundle_algClosure K A hA PP hPP hs ha hm hk (AlgebraicClosure K) κ hκ
  exact GlobalTheory.T.exists_finite_galois_descent_principal_polarisation K A hA PP hPP (AlgebraicClosure K) κ hκ L hL hS hI hM hT



theorem exists_extLam_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ PP : LB (G2 G).left, PP.IsLB → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → Out.RelAmple ((Over.pullback (jK R)).obj G) ((PP.pull κ₀).pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left)) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((PP.pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → x = toUnit T ≫ η[((Over.pullback (jK R)).obj G)]) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (PP.pull β₂) := by
  intro R _ _ _ hR G _ _ hab PP hPP hsym hadd hamp hker
  have hp := isGrpPullback_pullback G (jK R)
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left,
      Geo.Tor.IsSquare (pullback.fst G.hom (jK R)) κ₀ := ⟨_, GlobalTheory.LamPull.exists_isSquare hp.1.w⟩
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨E, _, _, hfd, hgal, A₁, gen, hgen, hLam⟩ :=
    exists_polAV_field (FractionRing R) ((Over.pullback (jK R)).obj G) hab (PP.pull κ₀) (pull_isLB hPP κ₀)
      (hsym κ₀ hκ₀) (hadd κ₀ hκ₀) (hamp κ₀ hκ₀) (hker κ₀ hκ₀)
  obtain ⟨R', _, _, _, ρ, t, hρ, ht⟩ := GlobalTheory.T.exists_finiteLocalExtension_fractionRing_of_galois R hR E hfd hgal
  haveI := hgen
  have hsq : (spMap t) ≫ (spMap (algebraMap (FractionRing R) E)) ≫ jK R = jK R' ≫ spMap ρ := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact ht r
  have hE := isGrpPullback_pullback ((Over.pullback (jK R)).obj G) (spMap (algebraMap (FractionRing R) E))
  have hβ := isGrpPullback_pullback G (spMap ρ)
  have hp₁ := isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')
  have hc := (hp₁.comp hβ).congr hsq.symm rfl
  have hAEG := hE.comp hp
  have w1 : (pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) ≫ G.hom =
      (((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t) ≫ (spMap (algebraMap (FractionRing R) E))) ≫ jK R := by
    simpa only [Category.assoc] using hc.1.w
  let a : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶
      ((Over.pullback (jK R)).obj G).left := pullback.lift _ _ w1
  have w2 : a ≫ ((Over.pullback (jK R)).obj G).hom =
      (((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t)) ≫ (spMap (algebraMap (FractionRing R) E)) := by
    exact (pullback.lift_snd _ _ w1).trans (Category.assoc _ _ _).symm
  let φ₁ : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶
      ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)).left := pullback.lift _ _ w2
  have hφ₁fst : φ₁ ≫ pullback.fst ((Over.pullback (jK R)).obj G).hom (spMap (algebraMap (FractionRing R) E)) ≫ pullback.fst G.hom (jK R) =
      pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ) := by
    simp only [φ₁, a, pullback.lift_fst_assoc, pullback.lift_fst]
  have hφ₁w : φ₁ ≫ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)).hom =
      ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t) := pullback.lift_snd _ _ _
  have hφ := hAEG.cancel (hc.congr rfl hφ₁fst.symm) hφ₁w
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨A₀, g, hg, hgL⟩ := GlobalTheory.ArcDataDescent.exists_polPull hL.polBaseChange (spMap t) A₁
  have h1 := (hφ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  obtain ⟨e, he, heg⟩ := grpPullback_iso h1 hg
  obtain ⟨β₂, hβ₂⟩ : ∃ β₂ : (G2 ((Over.pullback (spMap ρ)).obj G)).left ⟶ (G2 G).left,
      Geo.Tor.IsSquare (pullback.fst G.hom (spMap ρ)) β₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ.1.w⟩
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, (Over.pullback (spMap ρ)).obj G, inferInstance, inferInstance,
    pullback.fst G.hom (spMap ρ), β₂, A₀, e, ?_, ?_, ?_, ?_, ?_⟩
  · exact hρ
  · exact hβ
  · exact hβ₂
  · exact he
  refine ⟨pull_isLB hPP β₂, fun κ₂' hκ₂' => ?_⟩
  have hL1 : (A₁.L.pull gen.hom.left).IsLB := pull_isLB A₁.isLB _
  have hL0 : (A₀.L.pull e.hom.left).IsLB := pull_isLB A₀.isLB _
  have hNL : LBIso (A₀.L.pull e.hom.left) ((A₁.L.pull gen.hom.left).pull φ₁) :=
    LBIso.trans hL0 (pull_isLB A₁.isLB _) (pull_isLB hL1 φ₁)
      (GlobalTheory.ArcDataDescent.lbIso_pull hgL e.hom.left heg.symm)
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull A₁.isLB gen.hom.left φ₁ rfl).symm
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂, Geo.Tor.IsSquare φ₁ φ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hφ.1.w⟩
  have h₁ := GlobalTheory.LamPull.lbIso_lam_pull hφ hL1 hL0 hNL hφ₂
  obtain ⟨κ, hκ⟩ : ∃ κ : (G2 ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G))).left ⟶ (G2 ((Over.pullback (jK R)).obj G)).left, Geo.Tor.IsSquare (pullback.fst ((Over.pullback (jK R)).obj G).hom (spMap (algebraMap (FractionRing R) E))) κ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hE.1.w⟩
  have hΛ : (abelian₂ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)) (A₁.L.pull gen.hom.left)).IsLB :=
    DVR.linComb_isLB _ hL1 _ _
  have hLK : LBIso (abelian₂ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)) (A₁.L.pull gen.hom.left))
      (PP.pull (κ ≫ κ₀)) :=
    LBIso.trans hΛ (pull_isLB (pull_isLB hPP _) κ) (pull_isLB hPP _) (hLam κ hκ)
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPP κ₀ κ rfl)
  have h₂ := GlobalTheory.ArcDataDescent.lbIso_pull hLK φ₂ (ψ := φ₂ ≫ κ ≫ κ₀) rfl
  have hsq2 : φ₂ ≫ κ ≫ κ₀ = κ₂' ≫ β₂ := by
    apply GlobalTheory.LamPull.isSquare_unique
      (φ := pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ))
    · constructor
      · simp only [Category.assoc, hκ₀.1, reassoc_of% hκ.1, reassoc_of% hφ₂.1, hφ₁fst]
      · simp only [Category.assoc, hκ₀.2, reassoc_of% hκ.2, reassoc_of% hφ₂.2, hφ₁fst]
    · constructor
      · simp only [Category.assoc, hβ₂.1, reassoc_of% hκ₂'.1]
      · simp only [Category.assoc, hβ₂.2, reassoc_of% hκ₂'.2]
  rw [hsq2] at h₂
  have h₃ : LBIso (PP.pull (κ₂' ≫ β₂)) ((PP.pull β₂).pull κ₂') :=
    (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPP β₂ κ₂' rfl).symm
  exact LBIso.trans (DVR.linComb_isLB _ hL0 _ _) (pull_isLB hΛ φ₂) (pull_isLB (pull_isLB hPP β₂) κ₂') h₁
    (LBIso.trans (pull_isLB hΛ φ₂) (pull_isLB hPP _) (pull_isLB (pull_isLB hPP β₂) κ₂') h₂ h₃)

end GlobalTheory.MumDesc
end
end
end
