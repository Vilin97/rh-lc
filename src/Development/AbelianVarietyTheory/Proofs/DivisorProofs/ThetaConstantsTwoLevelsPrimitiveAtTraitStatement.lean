module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrSplitExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianModelFiniteExtCompleteDVR
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitThetaConstantsTwoLevelsIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSemiAbelianModelAfterExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitSemiAbModel

theorem exists_split_model : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (P : PolAV (Sp (FractionRing V))), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (f : V →+* W) (fK : FractionRing V →+* FractionRing W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ f.IsIntegral ∧ Function.Injective f ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) ∧ ∃ (A : PolAV (Sp (FractionRing W))) (β : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap fK) β ∧ LBIso A.L (P.L.pull β) ∧ ∃ (G : Over (Sp W)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK W)).obj G ≅ A.A), IsSemiAbelian G ∧ IsMonHom gen.hom ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj G) := by
  intro V _ _ _ hV P
  obtain ⟨V₁, _, _, _, f₁, fK₁, hV₁, hinj₁, -, hfin₁, hK₁, A₁, β₁, hpb₁, -, G₁, _, _, gen₁, hG₁, hgen₁⟩ :=
    GlobalTheory.PolSemiAbModel.exists_model V hV P
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff V₁).1 hV₁
  obtain ⟨W, _, _, _, _, g, hcW, hgi, hginj, -, E, hE⟩ :=
    GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V₁ hcpl G₁ hG₁
  have hj : Function.Injective ((algebraMap W (FractionRing W)).comp g) :=
    (IsFractionRing.injective W (FractionRing W)).comp hginj
  obtain ⟨fK₂, hK₂'⟩ : ∃ fK₂ : FractionRing V₁ →+* FractionRing W,
      ∀ a, fK₂ (algebraMap V₁ (FractionRing V₁) a) = algebraMap W (FractionRing W) (g a) :=
    ⟨IsFractionRing.lift (A := V₁) (K := FractionRing V₁) hj,
      fun a => IsFractionRing.lift_algebraMap (K := FractionRing V₁) hj a⟩
  have hK₂ : fK₂.comp (algebraMap V₁ (FractionRing V₁)) = (algebraMap W (FractionRing W)).comp g :=
    RingHom.ext hK₂'
  obtain ⟨A, β, hpb, -, hLB⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P (fK₂.comp fK₁)
  have hG : IsSemiAbelian ((Over.pullback (spMap g)).obj G₁) := IsSemiAbelian.pullback _ G₁ hG₁
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, g.comp f₁, fK₂.comp fK₁, hcW,
    RingHom.IsIntegral.trans _ _ hfin₁.to_isIntegral hgi, hginj.comp hinj₁, ?_, A, β, hpb, hLB, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hK₁]
    exact hK₂' _
  · let G := (Over.pullback (spMap g)).obj G₁
    let X := (Over.pullback (jK V₁)).obj G₁
    let T := (Over.pullback (spMap fK₂)).obj X
    have h₁ := (isGrpPullback_pullback G (jK W)).comp (isGrpPullback_pullback G₁ (spMap g))
    have hTX := isGrpPullback_pullback X (spMap fK₂)
    have hXG := isGrpPullback_pullback G₁ (jK V₁)
    have hsq : spMap fK₂ ≫ jK V₁ = jK W ≫ spMap g := by
      show spMap fK₂ ≫ spMap (algebraMap V₁ _) = spMap (algebraMap W _) ≫ spMap g
      rw [GlobalTheory.PolSemiAbModel.spMap_comp', GlobalTheory.PolSemiAbModel.spMap_comp', hK₂]
    have hTG := (hTX.comp hXG).congr hsq rfl
    obtain ⟨e₁, he₁, -⟩ := grpPullback_iso h₁ hTG
    have hXY := isGrpPullback_of_iso gen₁
    have hTP := (hTX.comp (hXY.comp hpb₁)).congr
      (by rw [Category.id_comp, GlobalTheory.PolSemiAbModel.spMap_comp']) rfl
    obtain ⟨e₂, he₂, -⟩ := grpPullback_iso hTP hpb
    exact ⟨G, inferInstance, hG.comm, e₁ ≪≫ e₂, hG, by simp only [Iso.trans_hom]; infer_instance, E, hE⟩

end GlobalTheory.SplitSemiAbModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSemiAbelianModelAfterExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_split_semiAbelian_model_after_extension : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (P : PolAV (Sp (FractionRing V))), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (f : V →+* W) (fK : FractionRing V →+* FractionRing W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ f.IsIntegral ∧ Function.Injective f ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) ∧ ∃ (A : PolAV (Sp (FractionRing W))) (β : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap fK) β ∧ LBIso A.L (P.L.pull β) ∧ ∃ (G : Over (Sp W)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK W)).obj G ≅ A.A), IsSemiAbelian G ∧ IsMonHom gen.hom ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj G) := by
  first | exact @GlobalTheory.SplitSemiAbModel.exists_split_model | exact GlobalTheory.SplitSemiAbModel.exists_split_model | (intros; apply GlobalTheory.SplitSemiAbModel.exists_split_model <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitThetaConstantsTwoLevelsIntegralStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformised_trait_theta_constants_two_levels_integral : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (_ : Unif (IsLocalRing.maximalIdeal W) D A G) (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing W →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : W) → Odd m' → 3 ≤ m' → IsUnit (m' : W) → (letI := A.isAb.comm; HasTh₂ A.A A.L ρ m m' (spMap io) d d') → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d' b / a) := by
  first | exact @GlobalTheory.SiegTh.CmpUnif.cmp_unif | exact GlobalTheory.SiegTh.CmpUnif.cmp_unif | (intros; apply GlobalTheory.SiegTh.CmpUnif.cmp_unif <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTwoLevelsPrimitiveAtTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegCmp

theorem prim_comp_of_isIntegral : ∀ {V W K : Type} [CommRing V] [CommRing W] [Field K] (f : V →+* W) (j : W →+* K), f.IsIntegral → ∀ {J : Type} (c : J → K), Prim j c → Prim (j.comp f) c := by
  intro V W K _ _ _ f j hf J c hc
  letI := f.toAlgebra
  letI := j.toAlgebra
  letI : Algebra V K := (j.comp f).toAlgebra
  haveI : IsScalarTower V W K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral V W := ⟨hf⟩
  have key : ∀ x : K, j.IsIntegralElem x → (j.comp f).IsIntegralElem x := fun x hx =>
    (isIntegral_trans (R := V) (A := W) x hx : IsIntegral V x)
  exact ⟨fun a => key _ (hc.1 a), let ⟨a, h0, h1⟩ := hc.2; ⟨a, h0, key _ h1⟩⟩

theorem exists_ext_fractionRing : ∀ (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (f : V →+* W) (fK : FractionRing V →+* FractionRing W), f.IsIntegral → (∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K), ∃ io' : FractionRing W →+* K, io'.comp fK = io := by
  intro V W _ _ _ _ f fK hf hfK K _ _ io
  letI := fK.toAlgebra
  letI := io.toAlgebra
  have hint : ∀ w : W, IsIntegral (FractionRing V) (algebraMap W (FractionRing W) w) := by
    intro w
    obtain ⟨p, hp, hpe⟩ := hf w
    refine ⟨p.map (algebraMap V (FractionRing V)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap (FractionRing V) (FractionRing W)).comp (algebraMap V (FractionRing V)) =
        (algebraMap W (FractionRing W)).comp f := by
      ext a; exact hfK a
    rw [this, ← Polynomial.hom_eval₂, hpe, map_zero]
  have hmem : ∀ w : W, algebraMap W (FractionRing W) w ∈ algebraicClosure (FractionRing V) (FractionRing W) :=
    fun w => mem_algebraicClosure_iff.2 (hint w).isAlgebraic
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing W) := by
    constructor
    intro z
    rw [← mem_algebraicClosure_iff]
    obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors W) z
    simp only [IsFractionRing.mk'_eq_div]
    exact div_mem (hmem w) (hmem s)
  refine ⟨(IsAlgClosed.lift : FractionRing W →ₐ[FractionRing V] K).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : FractionRing W →ₐ[FractionRing V] K).commutes x

theorem theta_two_levels_prim : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ S) (P : PolAV (Sp (FractionRing V))) (α : P.A.left ⟶ G.left), IsGrpPullback P.A G y α → LBIso P.L (L.pull α) → (letI := P.isAb.comm; HypS P.A P.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ G L ρ m m' (spMap io ≫ y) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by

  intro S G _ _ L ρ hL hρ V _ _ _ hV y P α hα hLα hS K _ _ io m m' N N' d d' hm hm3 hmu hm' hm3' hmu' hth
  letI := P.isAb.comm
  obtain ⟨ρP, hρP⟩ := P.rigid
  have h1 : HasTh₂ P.A P.L ρP m m' (spMap io) d d' :=
    (ThMove.hasTh₂_move S G L ρ hL hρ _ P.A P.L ρP y α P.isLB hρP hα hLα m m' N N' K (spMap io) d d').2 hth
  obtain ⟨W, _, _, _, _, f, fK, hWc, hfi, hfinj, hfK, A, β, hβ, hLβ, G', _, _, gen, hG', hgen, E, hE⟩ := GlobalTheory.T.exists_split_semiAbelian_model_after_extension V hV P
  letI := A.isAb.comm
  have hSA : HypS A.A A.L :=
    SymBaseChange.hypS_baseChange _ _ P.A A.A (spMap fK) β P.L A.L P.isLB A.isLB hβ hLβ hS
  obtain ⟨D, U, -⟩ := GlobalTheory.ZH.thmU_and_uTors.1 W hWc A G' hG' ⟨E, hE⟩ hSA gen hgen
  obtain ⟨io', hio'⟩ := exists_ext_fractionRing V W f fK hfi hfK K io
  obtain ⟨ρA, hρA⟩ := A.rigid
  have hx : spMap io' ≫ spMap fK = spMap io := by
    rw [← hio']; simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h2 : HasTh₂ A.A A.L ρA m m' (spMap io') d d' := by
    refine (ThMove.hasTh₂_move _ P.A P.L ρP P.isLB hρP _ A.A A.L ρA (spMap fK) β A.isLB hρA hβ hLβ
      m m' N N' K (spMap io') d d').2 ?_
    rw [hx]; exact h1
  have hmuW : IsUnit (m : W) := by simpa using hmu.map f
  have hmuW' : IsUnit (m' : W) := by simpa using hmu'.map f
  obtain ⟨a, ha, hp, hp'⟩ := GlobalTheory.T.uniformised_trait_theta_constants_two_levels_integral W hWc D A G' hG' U ρA hρA K io' m m' N N' d d' hm hm3 hmuW hm' hm3' hmuW' h2
  have hcomp : (io'.comp (algebraMap W (FractionRing W))).comp f = io.comp (algebraMap V (FractionRing V)) := by
    ext x; simp [← hfK, ← hio']
  refine ⟨a, ha, ?_, ?_⟩
  · rw [← hcomp]; exact prim_comp_of_isIntegral f _ hfi _ hp
  · rw [← hcomp]; exact prim_comp_of_isIntegral f _ hfi _ hp'

end GlobalTheory.SiegCmp

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTwoLevelsPrimitiveAtTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstants_two_levels_primitive_at_trait : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ S) (P : PolAV (Sp (FractionRing V))) (α : P.A.left ⟶ G.left), IsGrpPullback P.A G y α → LBIso P.L (L.pull α) → (letI := P.isAb.comm; HypS P.A P.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ G L ρ m m' (spMap io ≫ y) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by
  first | exact @GlobalTheory.SiegCmp.theta_two_levels_prim | exact GlobalTheory.SiegCmp.theta_two_levels_prim | (intros; apply GlobalTheory.SiegCmp.theta_two_levels_prim <;> assumption)
end
end
