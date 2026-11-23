module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTorsionBundleAbelianSchemeSqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTrivialityOfNoetherianDescent
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
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactors
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTrivialityOfNoetherianDescentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.localTriviality_of_noetherian_descent : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  first | (exact @GlobalTheory.LocTrivDescent.locTriv_of_noetherian) | (exact GlobalTheory.LocTrivDescent.locTriv_of_noetherian) | (intros; apply GlobalTheory.LocTrivDescent.locTriv_of_noetherian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLineBundleTrivialBasicOpenOfTrivialFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.TorsionSpread

theorem triv_lbPow_pull {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) (k : ℕ) (φ : Y ⟶ X)
    (h : ∃ t : (Hecke.lbPow M k).Gen, t.IsGen) : ∃ t : (Hecke.lbPow (M.pull φ) k).Gen, t.IsGen := by
  have hP : (Hecke.lbPow M k).IsLB := LB.isLB_linComb hM _ _
  have hM' : (M.pull φ).IsLB := LB.isLB_pull hM φ
  have hP' : (Hecke.lbPow (M.pull φ) k).IsLB := LB.isLB_linComb hM' _ _
  have e : ∀ {Z : Scheme.{0}} {N : LB Z} (hN : N.IsLB) (h' : (Hecke.lbPow N k).IsLB),
      CechPic.cls _ h' = k • CechPic.cls N hN := by
    intro Z N hN h'
    apply (CechPic.cls_linComb hN (fun _ : Fin k => 𝟙 Z) (fun _ => 1) h').trans
    simp [CechPic.pull_id]
  rw [← CechPic.cls_eq_zero_iff hP']
  rw [← CechPic.cls_eq_zero_iff hP] at h
  rw [e hM' hP', CechPic.cls_pull hM φ hM', ← map_nsmul, ← e hM hP, h, map_zero]

theorem triv_basicOpen_of_triv_fibre : (∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T), (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T → ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ, IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})), IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  intro hinf R _ _ A _ hA M hM _hrig k hk hpow K _ g₀ ht₀
  haveI := hA.proper
  haveI := hA.smooth
  have hP := GlobalTheory.ProperFinite.nonempty_perf_of_isProper A.hom hM
  haveI : Surjective A.hom := by
    haveI : Surjective ((1 : 𝟙_ (Over (Sp R)) ⟶ A).left ≫ A.hom) := by
      rw [Over.w]
      change Surjective (𝟙 _)
      infer_instance
    exact Surjective.of_comp (1 : 𝟙_ (Over (Sp R)) ⟶ A).left A.hom
  have h₀ := IsPullback.of_hasPullback A.hom (spMap g₀)
  obtain ⟨r, I, hr, hI, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R A.left A.hom M hM hP inferInstance inferInstance K g₀
    _ _ _ h₀ (GlobalTheory.AbLaw.CubeOpen.bijective_appTop GlobalTheory.ExpansionTotal.globalFns A hA h₀) ht₀
  haveI : (RingHom.ker g₀).IsPrime := RingHom.ker_isPrime g₀
  obtain ⟨c, hc, hcI⟩ := GlobalTheory.AbLaw.CubeOpen.exists_ann (RingHom.ker g₀) I hI
    ((H K g₀ _ _ _ h₀ (Ne.isUnit hr)).1 ht₀) (fun T _ _ g e hu he he' hle => by
      have hg := IsPullback.of_hasPullback A.hom (spMap g)
      refine (H T g _ _ _ hg (hu r hr)).1 ?_
      have hkT : IsUnit (k : T) := by simpa using hk.map g
      letI : GrpObj ((Over.pullback (spMap g)).obj A) := Functor.grpObjObj
      have hp := IsPullback.of_hasPullback ((Over.pullback (spMap g)).obj A).hom
        (spMap (Ideal.Quotient.mk (Ideal.span {e})))
      refine hinf T e he he' ((Over.pullback (spMap g)).obj A)
        (Out.TLinPf.isAb_pullback (spMap g) A hA) (M.pull (pullback.fst A.hom (spMap g)))
        (LB.isLB_pull hM _) k hkT (triv_lbPow_pull hM k _ hpow) _ _ _ hp ?_
      have hq := hp.paste_horiz hg
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hq
      exact GlobalTheory.AbLaw.CubeOpen.triv_pull_pull _ _
        ((H _ _ _ _ _ hq ((hu r hr).map (Ideal.Quotient.mk (Ideal.span {e})))).2 hle))
  refine ⟨r * c, by rw [map_mul]; exact mul_ne_zero hr hc, ?_⟩
  let L := Localization.Away (r * c)
  have hu : IsUnit (algebraMap R L (r * c)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, IsUnit.mul_iff] at hu
  have hp := IsPullback.of_hasPullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  have ht := (H L (algebraMap R L) _ _ _ hp hu.1).2 fun x hx => by
    rw [RingHom.mem_ker, ← hu.2.mul_right_eq_zero, ← map_mul, hcI x hx, map_zero]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
    IsOpenImmersion.of_isLocalization (r * c)
  have hsub : Set.range ((A.hom ⁻¹ᵁ (PrimeSpectrum.basicOpen (r * c))).ι ≫ A.hom) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rintro _ ⟨y, rfl⟩
    have := PrimeSpectrum.localization_away_comap_range L (r * c)
    change _ ∈ Set.range (PrimeSpectrum.comap (algebraMap R L))
    rw [this]
    exact y.2
  exact GlobalTheory.AbLaw.CubeOpen.triv_comp (hp.lift _ _ (IsOpenImmersion.lift_fac _ _ hsub).symm)
    (hp.lift_fst _ _ _) ht

end GlobalTheory.TorsionSpread
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLineBundleTrivialBasicOpenOfTrivialFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.torsionLineBundle_trivial_basicOpen_of_trivial_fibre : (∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T), (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T → ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ, IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})), IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  first | (exact @GlobalTheory.TorsionSpread.triv_basicOpen_of_triv_fibre) | (exact GlobalTheory.TorsionSpread.triv_basicOpen_of_triv_fibre) | (intros; apply GlobalTheory.TorsionSpread.triv_basicOpen_of_triv_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedLineBundleTrivialOfTorsionGeometricFib

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.AbDual

noncomputable section

namespace GlobalTheory.RigTorsTriv

theorem triv_of_geometricFibres : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over S) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit ((k : Γ(S, ⊤))) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (M.pull (pullback.fst A.hom y)).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  intro S A _ _ hA M hM hrig k hk hpow hfib
  have key : ∀ {Y : Scheme.{0}} (f : Y ⟶ A.left), (∃ t : (M.pull f).Gen, t.IsGen) ↔ pull f (cls M hM) = 0 :=
    fun f => (cls_eq_zero_iff (pull_isLB hM f)).symm.trans (by rw [cls_pull hM f])
  have hsurj : ∀ V : S.Opens, Function.Surjective (A.hom ∣_ V).appTop.hom := fun V => by
    have hG : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
    have h1 := hG _ _ (Out.TLinPf.isAb_pullback V.ι A hA)
    let e := IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict A.hom V)
      (IsPullback.of_hasPullback A.hom V.ι).flip
    have he : e.hom ≫ pullback.snd A.hom V.ι = A.hom ∣_ V := IsPullback.isoIsPullback_hom_fst _ _ _ _
    have hi : Function.Surjective e.hom.appTop.hom := by
      have : IsIso (e.hom.app ⊤) := inferInstance
      exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
    rw [← he, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    exact hi.comp h1.2
  have hc0 : pull (1 : 𝟙_ (Over S) ⟶ A).left (cls M hM) = 0 := (key _).1 hrig
  have hkM : k • cls M hM = 0 := by
    have h := (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).2 hpow
    rw [cls_linComb hM] at h
    simpa [pull_id] using h
  refine GlobalTheory.CubeGlue.triv_of_locally_triv hM A.hom (1 : 𝟙_ (Over S) ⟶ A).left
    (by simpa using Over.w (1 : 𝟙_ (Over S) ⟶ A)) hsurj hrig ?_
  intro s
  obtain ⟨R, j, hj, ⟨p, hp⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial
  let j' : Sp R ⟶ S := j
  haveI : IsOpenImmersion j' := hj
  let A' := (Over.pullback j').obj A
  have hA' : IsAbelianScheme A' := Out.TLinPf.isAb_pullback j' A hA
  let φ := pullback.fst A.hom j'
  have hM' : (M.pull φ).IsLB := pull_isLB hM φ
  have key' : ∀ {Y : Scheme.{0}} (f : Y ⟶ A'.left),
      (∃ t : ((M.pull φ).pull f).Gen, t.IsGen) ↔ pull (f ≫ φ) (cls M hM) = 0 := fun f =>
    (cls_eq_zero_iff (pull_isLB hM' f)).symm.trans (by rw [cls_pull hM' f, cls_pull hM φ, pull_comp])
  have hone : (1 : 𝟙_ (Over (Sp R)) ⟶ A').left ≫ φ = j' ≫ (1 : 𝟙_ (Over S) ⟶ A).left := by
    rw [Hom.one_def, Hom.one_def]
    simp [φ]
  have hrig' := (key' _).2 (by rw [hone, pull_comp, hc0, map_zero])
  have hk' : IsUnit (k : R) := by
    have h := hk.map ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp j'.appTop.hom)
    simpa using h
  have hpow' : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (M.pull φ) k).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM' _ _)).1 ?_
    rw [cls_linComb hM']
    simp [pull_id, cls_pull hM φ, ← map_nsmul, hkM]
  let P : PrimeSpectrum R := p
  haveI : P.asIdeal.IsPrime := P.isPrime
  let F := AlgebraicClosure P.asIdeal.ResidueField
  let ψ : R →+* F := (algebraMap P.asIdeal.ResidueField F).comp (algebraMap R P.asIdeal.ResidueField)
  have hfib' : ∃ t : ((M.pull φ).pull (pullback.fst A'.hom (spMap ψ))).Gen, t.IsGen := by
    rw [key']
    have h0 := (key _).1 (hfib F (spMap ψ ≫ j'))
    have e : pullback.fst A'.hom (spMap ψ) ≫ φ =
        pullback.lift (pullback.fst A'.hom (spMap ψ) ≫ φ) (pullback.snd A'.hom (spMap ψ))
          (by
            have hc : pullback.fst A'.hom (spMap ψ) ≫ A'.hom = pullback.snd A'.hom (spMap ψ) ≫ spMap ψ :=
              pullback.condition
            rw [Category.assoc, pullback.condition, ← Category.assoc]
            exact (congrArg (· ≫ j') hc).trans (Category.assoc _ _ _))
          ≫ pullback.fst A.hom (spMap ψ ≫ j') := (pullback.lift_fst _ _ _).symm
    rw [e, pull_comp, h0, map_zero]
  obtain ⟨r, hr, ht⟩ := GlobalTheory.T.localTriviality_of_noetherian_descent (GlobalTheory.T.torsionLineBundle_trivial_basicOpen_of_trivial_fibre GlobalTheory.T.exists_generator_torsion_bundle_abelianScheme_sqZero) R A' hA' (M.pull φ) hM' hrig' k hk' hpow' F ψ hfib'
  have hrp : P ∈ PrimeSpectrum.basicOpen r := by
    intro hm
    apply hr
    show algebraMap _ F (algebraMap R P.asIdeal.ResidueField r) = 0
    rw [(Ideal.algebraMap_residueField_eq_zero).2 hm, map_zero]
  refine ⟨j' ''ᵁ PrimeSpectrum.basicOpen r, ⟨p, hrp, hp⟩, ?_⟩
  refine (key _).2 ?_
  let D : (Sp R).Opens := PrimeSpectrum.basicOpen r
  let W := A.hom ⁻¹ᵁ (j' ''ᵁ D)
  have h1 : Set.range (W.ι ≫ A.hom) ⊆ Set.range j' := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨q, -, hq⟩ := y.2
    exact ⟨q, hq⟩
  let m : W.toScheme ⟶ A'.left :=
    pullback.lift W.ι (IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1) (IsOpenImmersion.lift_fac _ _ _).symm
  have h2 : Set.range m ⊆ Set.range (A'.hom ⁻¹ᵁ D).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have e : m ≫ A'.hom = IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1 := pullback.lift_snd _ _ _
    show (m ≫ A'.hom) y ∈ D
    rw [e]
    obtain ⟨q, hqD, hq⟩ := y.2
    have : IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1 y = q := j'.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]; exact hq.symm)
    rw [this]; exact hqD
  have hfac : W.ι = IsOpenImmersion.lift (A'.hom ⁻¹ᵁ D).ι m h2 ≫ (A'.hom ⁻¹ᵁ D).ι ≫ φ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (pullback.lift_fst _ _ _).symm
  rw [hfac, pull_comp, (key' _).1 ht, map_zero]

end GlobalTheory.RigTorsTriv
end
end
end
