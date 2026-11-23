module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfSymmetric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialDegenerationUnitPartExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPsiTauTangentVectorVariation
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartPeriodTauZeroValueOne

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitTauZero

theorem exists_isUnitTau_zero_val_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (mu : P.D.toPre.X), ∃ τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam mu 0 τ₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := by
  intro E _ _ _ H k _ _ m d t P gam mu
  have hF : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim
      (K' := Fin 4) ![(P.D.toPre.c (mu + 0)).left, (P.D.toPre.c mu).left, (P.D.toPre.c 0).left, (P.D.toPre.c 0).left] ![-1, 1, 1, -1] := by
    intro U _ h
    simp only [add_zero, Finset.univ_eq_empty, Finset.prod_empty, Fin.prod_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
    simp [Matrix.vecHead, Matrix.vecTail]
  obtain ⟨τ₀, hτ, hv⟩ := exists_gen P.D.toPre.P.isLB hF (LB.oneGen P.D.toPre.P.L) (LB.isGen_oneGen _)
  have h1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι),
      Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨τ₀, ⟨hτ, 1, ?_, fun zz J hJ => ?_⟩, h1⟩
  · simp
  · have hB : P.D.toPre.TauBimult := P.D.tau_bimult
    rw [h1 _ _ zz J hJ, _root_.mul_one]
    have vτ : val (P.D.toPre.tau mu 0) (𝟙 _) zz J =
        val (P.D.toPre.psi (mu + 0)) (𝟙 _) zz J * (val (P.D.toPre.psi mu) (𝟙 _) zz J)⁻¹ *
          (val (P.D.toPre.psi 0) (𝟙 _) zz J)⁻¹ * (val P.D.toPre.rigK (𝟙 _) zz J)⁻¹ :=
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have vρ : val P.D.toPre.rigK (𝟙 _) zz J = val P.D.toPre.rig (jK _) zz J := by
      refine (val_pull hJ _ _ _).trans ?_
      rw [Category.id_comp]
      rfl
    have hp : ∀ a : P.D.toPre.X, a = mu → val (P.D.toPre.psi a) (𝟙 _) zz J = val (P.D.toPre.psi mu) (𝟙 _) zz J := by
      rintro a rfl; rfl
    have h0 := GlobalTheory.PsiZero.val_psi_zero hB hJ
    have hu : unitOn (1 : (FractionRing (ChartRing k m d))ˣ) = 1 := map_one _
    rw [vτ, hp _ (add_zero mu), h0, vρ, hu, map_one, mul_inv_cancel, _root_.one_mul, inv_inv, mul_inv_cancel]

end GlobalTheory.UnitTauZero
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartPeriodTauZeroValueOneStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unitPartPeriodTau_zero_value_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (mu : P.D.toPre.X), ∃ τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam mu 0 τ₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := by
  intro E _ _ _ H k _ _ m d t P gam mu
  exact GlobalTheory.UnitTauZero.exists_isUnitTau_zero_val_one E H k m d t P gam mu
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvCompOfIsGrpPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymSpread

theorem inv_comp_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
  simpa [pushHom, pushPt, Hom.inv_def] using e

end GlobalTheory.SymSpread
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullOfConst

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ConstDefSym

open GlobalTheory.CechPic

theorem lbIso_pull_of_const : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : Type) [Field k] [CharZero k] (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (Q.P.L.pull π₁) (Q.P.L.pull π₂) := by
  intro R _ _ Q k _ _ ρ B' _ π₁ π₂ h₁ h₂ hfib

  let ρ₀ : R →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ
  let A₀ : Over (Sp k) := (Over.pullback (spMap ρ₀)).obj Q.P.A
  letI : GrpObj A₀ := Functor.grpObjObj
  have hj : IsGrpPullback A₀ Q.P.A (spMap ρ₀) (pullback.fst Q.P.A.hom (spMap ρ₀)) := isGrpPullback_pullback Q.P.A (spMap ρ₀)
  have ec : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫ spMap ρ₀ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have h₂' : IsGrpPullback B' Q.P.A (spMap (algebraMap k (DualNumber k)) ≫ spMap ρ₀) π₂ := h₂.congr ec rfl
  let q : B'.left ⟶ A₀.left := hj.1.lift π₂ (B'.hom ≫ spMap (algebraMap k (DualNumber k)))
    (by rw [h₂'.1.w, Category.assoc])
  have hq₁ : q ≫ pullback.fst Q.P.A.hom (spMap ρ₀) = π₂ := hj.1.lift_fst _ _ _
  have hq₂ : q ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) := hj.1.lift_snd _ _ _
  have hq : IsGrpPullback B' A₀ (spMap (algebraMap k (DualNumber k))) q :=
    IsGrpPullback.cancel hj (h₂'.congr rfl hq₁.symm) hq₂
  have eid : GlobalTheory.DeRham.epsRed k ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [GlobalTheory.DeRham.epsRed, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of k)
    ext x
    simp
  let i : A₀.left ⟶ B'.left := hq.1.lift (𝟙 _) (A₀.hom ≫ GlobalTheory.DeRham.epsRed k)
    (by rw [Category.id_comp, Category.assoc, eid, Category.comp_id])
  have e : i ≫ q = 𝟙 _ := hq.1.lift_fst _ _ _
  have hi₂ : i ≫ B'.hom = A₀.hom ≫ GlobalTheory.DeRham.epsRed k := hq.1.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl A₀).hom := inferInstanceAs (IsMonHom (𝟙 A₀))
  have hi : IsGrpPullback A₀ B' (GlobalTheory.DeRham.epsRed k) i :=
    IsGrpPullback.cancel hq ((isGrpPullback_of_iso (Iso.refl A₀)).congr eid.symm (by rw [e]; rfl)) hi₂
  have hA₀ : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback Q.P.isAb hj

  have hL := Q.P.isLB
  have hsymA : pull (GrpObj.inv : Q.P.A ⟶ Q.P.A).left (cls Q.P.L hL) = cls Q.P.L hL := by
    have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨Q.sym, Q.sym_gen⟩
    rw [cls_linComb hL] at h0
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul,
      pull_id] at h0
    exact sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h0)
  have key : ∀ {f : Sp (DualNumber k) ⟶ Sp R} (π : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A f π →
      LBIso ((Q.P.L.pull π).pull (GrpObj.inv : B' ⟶ B').left) (Q.P.L.pull π) := by
    intro f π hπ
    rw [← cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _)]
    show pull _ (pull π (cls Q.P.L hL)) = pull π (cls Q.P.L hL)
    rw [← pull_comp, GlobalTheory.SymSpread.inv_comp_of_isGrpPullback hπ, pull_comp, hsymA]
  have hfib' : i ≫ π₁ = i ≫ π₂ := hfib A₀.left i A₀.hom hi₂
  have hclosed : LBIso ((Q.P.L.pull π₁).pull i) ((Q.P.L.pull π₂).pull i) := by
    rw [← cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)]
    show pull i (pull π₁ (cls Q.P.L hL)) = pull i (pull π₂ (cls Q.P.L hL))
    rw [← pull_comp, ← pull_comp, hfib']
  exact GlobalTheory.SymFirstOrder.lbIso_of_symmetric k A₀ B' i q hA₀ hi hq e _ _ (pull_isLB hL _) (pull_isLB hL _)
    (key π₁ h₁) (key π₂ h₂) hclosed

end GlobalTheory.ConstDefSym
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPsiTauTangentVectorVariationStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitPart_psi_tau_tangent_vector_variation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ lam : ℕ → P.D.toPre.X → k, ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ ee : (DualNumber k)ˣ, (ee : DualNumber k) = 1 + TrivSqZeroExt.inr (lam e mu - ∑ i, ((e : k) * (n i : k) + (gam i mu α : k)) * MvPowerSeries.constantCoeff (q i)) → ∀ zz J, Good P.D.toPre.P.L zz J → (val ψ₀ (spMap ρ) zz J) ^ e * val τ₀ (spMap ρ) zz J * (val P.D.toPre.rig (spMap ρ) zz J) ^ e = gm (c' (mu)) zz _ (w.s (fun _ => J (c' (mu) ≫ π₂), fun _ => J (c' (mu) ≫ π₁))) ^ ((e : ℤ) - 1) * gm (c' (mu + α)) zz _ (w.s (fun _ => J (c' (mu + α) ≫ π₂), fun _ => J (c' (mu + α) ≫ π₁))) * (gm (c' (α)) zz _ (w.s (fun _ => J (c' (α) ≫ π₂), fun _ => J (c' (α) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) ^ (1 - (e : ℤ)) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) * (val ψ₀ (spMap (constHom ρ)) zz J) ^ e * val τ₀ (spMap (constHom ρ)) zz J * (val P.D.toPre.rig (spMap (constHom ρ)) zz J) ^ e := by
  first | exact @GlobalTheory.UnitsEval.units_eval | exact GlobalTheory.UnitsEval.units_eval | (intros; apply GlobalTheory.UnitsEval.units_eval <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPeriodsConstantAlongTangent

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitsAlong

theorem alg {G : Type} [CommGroup G] (P T Rg Wy Wyz Wz W0 U2 E Pc Tc Rgc : G) (e : ℕ) (n n' : ℤ)
    (hA : P ^ e * T * Rg ^ e = Wy ^ n * Wyz * Wz⁻¹ * W0 ^ n' * (U2 * E) * Pc ^ e * Tc * Rgc ^ e)
    (hB : P ^ e * 1 * Rg ^ e = Wy ^ n * Wy * W0⁻¹ * W0 ^ n' * U2 * Pc ^ e * 1 * Rgc ^ e) :
    T = Wyz * Wy⁻¹ * Wz⁻¹ * W0 * E * Tc := by
  apply Additive.ofMul.injective
  have hA' := congrArg Additive.ofMul hA
  have hB' := congrArg Additive.ofMul hB
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, ofMul_one, add_zero] at hA' hB' ⊢
  calc Additive.ofMul T = (e • Additive.ofMul P + Additive.ofMul T + e • Additive.ofMul Rg) -
        (e • Additive.ofMul P + e • Additive.ofMul Rg) := by abel
    _ = _ := by rw [hA', hB']; abel

theorem unitTau_along : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ c : ℚ, c ≠ 0 ∧ ∃ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen ∧ ∀ y z τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam y z τ₀ → ∀ e : (DualNumber k)ˣ, (e : DualNumber k) = 1 + TrivSqZeroExt.inr (∑ i, (c : k) * MvPowerSeries.constantCoeff (q i) * gam i y z) → ∀ zz J, Good P.D.toPre.P.L zz J → val τ₀ (spMap ρ) zz J = gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) * (gm (c' (y)) zz _ (w.s (fun _ => J (c' (y) ≫ π₂), fun _ => J (c' (y) ≫ π₁))))⁻¹ * (gm (c' (z)) zz _ (w.s (fun _ => J (c' (z) ≫ π₂), fun _ => J (c' (z) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn e) * val τ₀ (spMap (constHom ρ)) zz J := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  intro Y n' v' dd hdd D q hq h hB hdef hΘ ρ hρ B' _ π₁ π₂ c' h₁ h₂ hfib hc'
  obtain ⟨w, hw⟩ := GlobalTheory.ConstDefSym.lbIso_pull_of_const (ChartRing k m d) P.D.toPre k ρ B' inferInstance π₁ π₂ h₁ h₂ hfib
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.unitPart_psi_tau_tangent_vector_variation E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hB hdef hΘ ρ hρ B' π₁ π₂ c' h₁ h₂ hfib hc' w hw
  refine ⟨-1, by norm_num, w, hw, ?_⟩
  intro y z τ₀ hτ ee hee zz J hJ
  obtain ⟨n, ψ₀, hψ⟩ := GlobalTheory.UnitPart.exists_isUnitPart P.D.toPre (bdParam k m d) gam hmon y
  obtain ⟨τ₁, hτ₁, hv₁⟩ := GlobalTheory.T.exists_unitPartPeriodTau_zero_value_one E H k m d t P gam y
  obtain ⟨e₁, he₁⟩ := hlam y z n ψ₀ τ₀ hψ hτ
  obtain ⟨e₂, he₂⟩ := hlam y 0 n ψ₀ τ₁ hψ hτ₁
  obtain ⟨u₂, hu₂⟩ : ∃ u : (DualNumber k)ˣ, (u : DualNumber k) = 1 + TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i)) :=
    ⟨⟨_, 1 - TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i)),
      by ext <;> simp, by ext <;> simp⟩, rfl⟩
  have hu₁ : ((u₂ * ee : (DualNumber k)ˣ) : DualNumber k) = 1 + TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y z : k)) * MvPowerSeries.constantCoeff (q i)) := by
    rw [Units.val_mul, hu₂, hee]
    have hs : ∀ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y z : k)) * MvPowerSeries.constantCoeff (q i) =
        (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i) -
          (((-1 : ℚ) : k) * MvPowerSeries.constantCoeff (q i) * (gam i y z : k)) := by
      intro i
      simp only [map_zero, Int.cast_zero, add_zero, Rat.cast_neg, Rat.cast_one]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_sub_distrib]
    ext <;> simp
    ring
  have A := he₁ (max e₁ e₂) (le_max_left _ _) (u₂ * ee) hu₁ zz J hJ
  have B := he₂ (max e₁ e₂) (le_max_right _ _) u₂ hu₂ zz J hJ
  rw [hv₁ _ (spMap ρ) zz J hJ, hv₁ _ (spMap (constHom ρ)) zz J hJ] at B
  have hW : ∀ a : P.D.toPre.X, a = y →
      gm (c' a) zz _ (w.s (fun _ => J (c' a ≫ π₂), fun _ => J (c' a ≫ π₁))) =
        gm (c' y) zz _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))) := by
    rintro a rfl; rfl
  rw [hW (y + 0) (add_zero y)] at B
  have hG : gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn (u₂ * ee)) =
      gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn u₂) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) := by
    rw [← map_mul]; congr 1; simp only [unitOn, map_mul]
  rw [hG] at A
  exact alg (hA := A) (hB := B)

end GlobalTheory.UnitsAlong
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPeriodsConstantAlongTangentStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitPart_periods_constant_along_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ c : ℚ, c ≠ 0 ∧ ∃ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen ∧ ∀ y z τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam y z τ₀ → ∀ e : (DualNumber k)ˣ, (e : DualNumber k) = 1 + TrivSqZeroExt.inr (∑ i, (c : k) * MvPowerSeries.constantCoeff (q i) * gam i y z) → ∀ zz J, Good P.D.toPre.P.L zz J → val τ₀ (spMap ρ) zz J = gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) * (gm (c' (y)) zz _ (w.s (fun _ => J (c' (y) ≫ π₂), fun _ => J (c' (y) ≫ π₁))))⁻¹ * (gm (c' (z)) zz _ (w.s (fun _ => J (c' (z) ≫ π₂), fun _ => J (c' (z) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn e) * val τ₀ (spMap (constHom ρ)) zz J := by
  first | exact @GlobalTheory.UnitsAlong.unitTau_along | exact GlobalTheory.UnitsAlong.unitTau_along | (intros; apply GlobalTheory.UnitsAlong.unitTau_along <;> assumption)
end
end
