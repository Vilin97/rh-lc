module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLinearLiftAdditiveHolomorphicAbelian
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculus
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuli
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelPrincipalSiegelAlgClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteFibrePoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerE8BundleIsoOfPrincipalSiegelIso

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
open GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.SharpIso

theorem iso_of_sRel : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N) (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (t : TObj (8 * g) N J b (𝟙 (Sp K))) (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ Q.A, ∀ u, x ≫ pr u = y u) → LBIso Q.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → SRel C c 0 0 (𝟙 _) → IsSharp W a bas t C → ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
  intro g n N B _ ζ K _ s c b C W J a bas t Q pr hpr huniv hQ hrel hsharp
  obtain ⟨φ, hpb, ⟨φ₂, hsq, hP⟩, -⟩ := hrel
  obtain ⟨pr', hpr', huniv', ht, -, -⟩ := hsharp
  have w : φ ≫ c.A.hom = C.A.hom := by simpa using hpb.1.w
  let f : C.A ⟶ c.A := Over.homMk φ w
  haveI : IsIso φ := hpb.1.isIso_fst_of_isIso
  haveI : IsIso f := by
    have : IsIso ((Over.forget _).map f) := by simpa [f] using (inferInstance : IsIso φ)
    exact isIso_of_reflects_iso f (Over.forget _)
  haveI hf : IsMonHom f := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f
    (fun _ x y => GlobalTheory.AbelianLetters.mul_comp_of_isGrpPullback_id f hpb x y)
  obtain ⟨ψ, hψ, -⟩ := huniv t.A (fun u => pr' u ≫ f)
  obtain ⟨χ, hχ, -⟩ := huniv' Q.A (fun u => pr u ≫ inv f)
  have h1 : ψ ≫ χ = 𝟙 _ := (huniv' t.A pr').unique (fun u => by
      rw [Category.assoc, hχ, ← Category.assoc, hψ, Category.assoc, IsIso.hom_inv_id, Category.comp_id])
    (fun u => Category.id_comp _)
  have h2 : χ ≫ ψ = 𝟙 _ := (huniv Q.A pr).unique (fun u => by
      rw [Category.assoc, hψ, ← Category.assoc, hχ, Category.assoc, IsIso.inv_hom_id, Category.comp_id])
    (fun u => Category.id_comp _)
  have hm : ∀ u, IsMonHom (ψ ≫ pr u) := fun u => by
    rw [hψ]; haveI := hpr' u; infer_instance
  have hψm : IsMonHom ψ := by
    refine ⟨(huniv _ fun u => η[Q.A] ≫ pr u).unique (fun u => ?_) fun _ => rfl,
      (huniv _ fun u => μ[t.A] ≫ ψ ≫ pr u).unique (fun u => Category.assoc _ _ _) fun u => ?_⟩
    · have := hm u
      have := hpr u
      rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · have := hm u
      have := hpr u
      rw [Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom]
  refine ⟨⟨ψ, χ, h1, h2⟩, hψm, ?_⟩
  have hsq' : Geo.Tor.IsSquare φ (f ⊗ₘ f).left :=
    ⟨by rw [← Over.comp_left, tensorHom_fst]; rfl, by rw [← Over.comp_left, tensorHom_snd]; rfl⟩
  obtain rfl := GlobalTheory.LamPull.isSquare_unique hsq hsq'
  have key : ∀ uv : Fin 8 × Fin 8, (lift (pr' uv.1) (pr' uv.2)).left ≫ (f ⊗ₘ f).left =
      ψ.left ≫ (lift (pr uv.1) (pr uv.2)).left := fun uv => by
    rw [← Over.comp_left, ← Over.comp_left, lift_map, comp_lift, hψ, hψ]
  rw [← cls_eq_iff t.isLB (pull_isLB Q.isLB _), (cls_eq_iff t.isLB (LB.isLB_linComb C.isLB _ _)).2 ht,
    cls_linComb C.isLB, (cls_eq_iff C.isLB (pull_isLB c.isLB _)).2 hP, cls_pull c.isLB,
    cls_pull Q.isLB, (cls_eq_iff Q.isLB (LB.isLB_linComb c.isLB _ _)).2 hQ, cls_linComb c.isLB]

  simp only [map_sum, map_zsmul, ← pull_comp, key]

end GlobalTheory.SharpIso
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerE8BundleIsoOfPrincipalSiegelIsoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

theorem _root_.GlobalTheory.T.eighthPower_E8Bundle_iso_of_principalSiegelIso : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N) (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (t : TObj (8 * g) N J b (𝟙 (Sp K))) (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ Q.A, ∀ u, x ≫ pr u = y u) → LBIso Q.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → SRel C c 0 0 (𝟙 _) → IsSharp W a bas t C → ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
  first | exact @GlobalTheory.SharpIso.iso_of_sRel | exact GlobalTheory.SharpIso.iso_of_sRel | (intros; apply GlobalTheory.SharpIso.iso_of_sRel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFiniteOfPolarisedAVIsoAlgClosed

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

noncomputable section

namespace GlobalTheory.ThetaFiniteIso

theorem thetaPts_finite : ∀ (G N' : ℕ) (J : Type) (K : Type) [Field K] [IsAlgClosed K] (b : TBase K (N' ^ 2)) (Q : PolAV (Sp K)), Odd N' → 3 ≤ N' → ∃ V : Set (Ix G (N' ^ 2) → K), V.Finite ∧ ∀ t : TObj G (N' ^ 2) J b (𝟙 (Sp K)), (∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left)) → ∃ v ∈ V, t.HasTh (𝟙 _) v := by
  intro G N' J K _ _ b Q ho _
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ ho.pos.ne'⟩
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let T₀ : Over (Sp K) := Over.mk (T.hom ≫ 𝟙 (Sp K))
  let fn : K → Γ(T.left, ⊤) := fun c => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c
  let Tor := {y : T₀ ⟶ Q.A // y ^ (N' ^ 2) = 1}
  have e : T₀ ≅ 𝟙_ (Over (Sp K)) :=
    (CartesianMonoidalCategory.isTerminalTensorUnit).uniqueUpToIso
      (IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom (by simp [T₀, T]))
        (fun Y m => Over.OverMorphism.ext (by simpa [T₀, T] using Over.w m))) |>.symm
  haveI hTor : Finite Tor := by
    have := GlobalTheory.AbTorsionFinite.finite_torsion K Q.A Q.isAb (N' ^ 2) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ ho.pos.ne'))
    refine Finite.of_injective (fun y : Tor => (⟨e.inv ≫ y.1, by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]⟩ :
      {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q.A // x ^ (N' ^ 2) = 1})) ?_
    intro y y' h
    exact Subtype.ext ((cancel_epi e.inv).1 (congrArg Subtype.val h))
  let ch : (Ix G (N' ^ 2) → Tor) → (Ix G (N' ^ 2) → K) := fun l =>
    if h : ∃ v : Ix G (N' ^ 2) → K, IsThetaPt Q N' (fun a => (l a).1) (fun a => fn (v a)) then h.choose else 0
  refine ⟨Set.range ch, Set.finite_range ch, fun t ⟨φ, hφ, hw⟩ => ?_⟩
  haveI := hφ
  let x : Ix G (N' ^ 2) → (T ⟶ t.pol.A) := fun a => (Over.homMk (𝟙 (Sp K)) (by simp [T]) : T ⟶ Out.baseOver (Sp K)) ≫ t.lab a
  have hk : ∀ a, x a ^ (N' ^ 2) = 1 := fun a => by
    exact (MonObj.comp_pow _ _ _).symm.trans ((congrArg (_ ≫ ·) (GlobalTheory.ThetaPtUp.lab_pow t a)).trans (MonObj.comp_one _))
  let x₀ : Ix G (N' ^ 2) → (T₀ ⟶ Q.A) := fun a => Over.homMk ((x a).left ≫ φ.hom.left) (by
    exact (Category.assoc _ _ _).trans ((congrArg ((x a).left ≫ ·) (Over.w φ.hom)).trans
      ((Over.w (x a)).trans (Category.comp_id _).symm)))
  have hx : ∀ a, (x₀ a).left = (x a).left ≫ φ.hom.left := fun a => rfl
  have hp : IsGrpPullback t.pol.A Q.A (𝟙 (Sp K)) φ.hom.left := isGrpPullback_of_iso φ
  have key : ∀ v : Ix G (N' ^ 2) → K, t.HasTh (𝟙 _) v ↔ IsThetaPt Q N' x₀ (fun a => fn (v a)) := fun v =>
    GlobalTheory.ThetaPtUp.isThetaPt_iff (P := t.pol) (P₀ := Q) (T := T) hp hw hx hk _
  let r : T₀ ⟶ T := Over.homMk (𝟙 (Sp K)) (by simp [T₀, T])
  have hk₀ : ∀ a, x₀ a ^ (N' ^ 2) = 1 := fun a => by
    have e₁ : x₀ a = r ≫ x a ≫ φ.hom := Over.OverMorphism.ext (Category.id_comp _).symm
    have h2 : (x a ≫ φ.hom) ^ (N' ^ 2) = 1 := by
      have := map_pow (IsMonHom.monoidHom φ.hom T) (x a) (N' ^ 2)
      have h1 : IsMonHom.monoidHom φ.hom T (x a ^ (N' ^ 2)) = 1 := by
        erw [hk a]; exact map_one _
      exact this.symm.trans h1
    rw [e₁, ← MonObj.comp_pow, h2, MonObj.comp_one]
  let l : Ix G (N' ^ 2) → Tor := fun a => ⟨x₀ a, hk₀ a⟩
  obtain ⟨v, hv⟩ := GlobalTheory.FamRep.exists_hasTh_field GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 ho t K (𝟙 _)
  have h : ∃ v : Ix G (N' ^ 2) → K, IsThetaPt Q N' (fun a => (l a).1) (fun a => fn (v a)) := ⟨v, (key v).1 hv⟩
  refine ⟨ch l, ⟨l, rfl⟩, (key _).2 ?_⟩
  simp only [ch, dif_pos h]
  exact h.choose_spec

end GlobalTheory.ThetaFiniteIso

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFiniteOfPolarisedAVIsoAlgClosedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

theorem _root_.GlobalTheory.T.thetaConstants_finite_of_polarisedAVIso_algClosed : ∀ (G N' : ℕ) (J : Type) (K : Type) [Field K] [IsAlgClosed K] (b : TBase K (N' ^ 2)) (Q : PolAV (Sp K)), Odd N' → 3 ≤ N' → ∃ V : Set (Ix G (N' ^ 2) → K), V.Finite ∧ ∀ t : TObj G (N' ^ 2) J b (𝟙 (Sp K)), (∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left)) → ∃ v ∈ V, t.HasTh (𝟙 _) v := by
  first | exact @GlobalTheory.ThetaFiniteIso.thetaPts_finite | exact GlobalTheory.ThetaFiniteIso.thetaPts_finite | (intros; apply GlobalTheory.ThetaFiniteIso.thetaPts_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSiegelPointsE8ThetaPower

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SharpFiniteTh
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

theorem finite_sharpOver : ∀ (g n : ℕ), 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)), Set.Finite {y : Sp K ⟶ F.X | GlobalTheory.Poinc.SharpOver F W Q y} := by
  intro g n hn2 F W hW K _ _ Q
  have hn : n ≠ 0 := by omega
  have hζ : IsUnit (zetaAway n) := by rw [← cycBase_ζ hn]; exact Units.isUnit _
  obtain ⟨ℓ, hℓ, hodd, hℓK⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ (ℓ : K) ≠ 0 := by
    by_cases h3 : ((3 : ℕ) : K) = 0
    · refine ⟨5, by norm_num, by decide, fun h5 => ?_⟩
      have h2 : (2 : K) = 0 := by
        have e : ((5 : ℕ) : K) - ((3 : ℕ) : K) = 0 := by rw [h5, h3, sub_zero]
        push_cast at e; linear_combination e
      have h1 : (1 : K) = 0 := by
        have e : ((3 : ℕ) : K) - 2 = 0 := by rw [h3, h2, sub_zero]
        push_cast at e; linear_combination e
      exact one_ne_zero h1
    · exact ⟨3, Nat.prime_three, by decide, h3⟩
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨bas, hbas⟩ := GlobalTheory.SiegEighth.exists_isSharpBasis g W hW
  let a : Fin 8 × Fin 8 → Matrix (Fin 8) (Fin 8) ℤ := fun uv => Matrix.single uv.1 uv.2 1
  have he : ∀ u v : Fin 8, ∃ j : Fin 8 × Fin 8, a j = Matrix.single u v 1 := fun u v => ⟨(u, v), rfl⟩
  obtain ⟨Mat, κ, hsh⟩ := GlobalTheory.ThetaQuasiFinite.exists_shape hL hW a bas
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ThetaQuasiFinite.tMap_of_hasTh hL hL2 (Fin 8 × Fin 8) Mat κ ℓ hℓ hodd
  set N' := ℓ ^ (j₀ + 1) with hN'
  have hN'odd : Odd N' := hodd.pow
  have hN'3 : 3 ≤ N' := le_trans (by have := hℓ.two_le; rcases hodd with ⟨r, hr⟩; omega) (Nat.le_self_pow (by omega) ℓ)
  set N := N' ^ 2 with hN
  have hNodd : Odd N := hN'odd.pow
  have hN3 : 3 ≤ N := le_trans hN'3 (Nat.le_self_pow (by omega) N')
  have hNK : ((N : ℕ) : K) ≠ 0 := by
    rw [hN, hN', Nat.cast_pow, Nat.cast_pow]; exact pow_ne_zero _ (pow_ne_zero _ hℓK)
  haveI : NeZero ((N : ℕ) : K) := ⟨hNK⟩
  obtain ⟨z0, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K N
  have hz0 : z0 ≠ 0 := hz.ne_zero (by omega)
  let b : TBase K N := ⟨Units.mk0 z0 hz0, hNK.isUnit, fun K' _ β => hz.map_of_injective β.injective⟩
  have hbζ : b.ζ ^ N = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hz.pow_eq_one)
  have key : ∀ y : Sp K ⟶ F.X, GlobalTheory.Poinc.SharpOver F W Q y → ∃ (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K)))
      (t : TObj (8 * g) N (Fin 8 × Fin 8) b (𝟙 (Sp K))), C.Principal ∧ SRel C F.univ 0 0 y ∧ IsSharp W a bas t C ∧
      ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
    intro y hy
    obtain ⟨c, hc, pr, hpr, huniv, hiso⟩ := hy
    have hc0 := GlobalTheory.ThetaQuasiFinite.sRel_zero_of_siegPB hc
    have hcP : c.Principal := sRel_principal hc0 F.princ
    have hd : SmoothOfRelativeDimension g c.A.hom := GlobalTheory.SiegSharpCover.smoothDim c hn2 hζ (isUnit_natCast hn)
    obtain ⟨C, hC⟩ := GlobalTheory.T.exists_symplecticLevel_principalSiegel_algClosed g n N _ _ K _ c b hNodd hN3 hcP hd
    have hCP : C.Principal := sRel_principal hC hcP
    obtain ⟨t, ht⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp hL hL2 g (8 * g) W _ a bas hW hbas N K b (Sp K) (𝟙 _) C hNodd hN3 hbζ hCP
    have hCF : SRel C F.univ 0 0 y := by simpa using sRel_comp hc0 hC
    exact ⟨C, t, hCP, hCF, ht, GlobalTheory.T.eighthPower_E8Bundle_iso_of_principalSiegelIso g n N _ _ K _ c b C W _ a bas t Q pr hpr huniv hiso hC ht⟩
  obtain ⟨V, hVf, hV⟩ := GlobalTheory.T.thetaConstants_finite_of_polarisedAVIso_algClosed (8 * g) N' (Fin 8 × Fin 8) K b Q hN'odd hN'3
  have := GlobalTheory.ThetaQuasiFinite.finite_points_cycAway hn K
  let T : (Ix (8 * g) N → K) → (Sp K ⟶ Sp (cycAway n)) → Set (Sp K ⟶ F.X) := fun v x₀ =>
    {y | y ≫ F.s = x₀ ∧ ∃ (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (t : TObj (8 * g) N (Fin 8 × Fin 8) b (𝟙 (Sp K))),
      C.Principal ∧ SRel C F.univ 0 0 y ∧ IsSharp W a bas t C ∧ t.HasTh (𝟙 _) v}
  have hT : ∀ v x₀, (T v x₀).Finite := by
    intro v x₀
    rcases (T v x₀).eq_empty_or_nonempty with h0 | ⟨y₀, -, C₀, t₀, hC₀, -, H₀, hv₀⟩
    · rw [h0]; exact Set.finite_empty
    refine (GlobalTheory.ThetaQuasiFinite.finite_of_fibre (Nat.one_le_iff_ne_zero.2 hn) F K x₀ C₀).subset ?_
    rintro y ⟨hx, C, t, hC, hCF, H, hv⟩
    have hNz : N ≠ 0 := by omega
    have m := hj₀ (j₀ + 1) (by omega) K b K (𝟙 _) t t₀ v (hsh N hNz K b (Sp K) (𝟙 _) C t hC H)
      (hsh N hNz K b (Sp K) (𝟙 _) C₀ t₀ hC₀ H₀) hv hv₀
    have p := PowerPullback.backward hL.globalFns hW hC hC₀ H H₀ he m
    have := sRel_comp hCF (GlobalTheory.ThetaQuasiFinite.sRel_zero_of_siegPB p)
    exact ⟨hx, by simpa using this⟩
  refine (Set.Finite.biUnion hVf fun v _ => Set.finite_iUnion fun x₀ => hT v x₀).subset ?_
  intro y hy
  obtain ⟨C, t, hC, hCF, H, φ⟩ := key y hy
  obtain ⟨v, hvV, hv⟩ := hV t φ
  exact Set.mem_biUnion hvV (Set.mem_iUnion.2 ⟨y ≫ F.s, rfl, C, t, hC, hCF, H, hv⟩)

end GlobalTheory.SharpFiniteTh
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSiegelPointsE8ThetaPowerStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_siegelPoints_e8ThetaPower : ∀ (g n : ℕ), 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)), Set.Finite {y : Sp K ⟶ F.X | GlobalTheory.Poinc.SharpOver F W Q y} := by
  first | exact @GlobalTheory.SharpFiniteTh.finite_sharpOver | exact GlobalTheory.SharpFiniteTh.finite_sharpOver | (intros; apply GlobalTheory.SharpFiniteTh.finite_sharpOver <;> assumption)
end
end
