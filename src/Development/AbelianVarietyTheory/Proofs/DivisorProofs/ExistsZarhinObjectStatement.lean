module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinSymplecticTransferStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundlePrincipalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleRigidifiedSymmetricStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickLevelSymplecticGeometricPointsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinFamilyInclusionPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

open GlobalTheory.CechPic GlobalTheory.AbDual

noncomputable section

namespace GlobalTheory.ZarhinFam

section
variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem incZ_pa (i : Fin 4) : incZ A B ≫ pa A B i = if i = 0 then 𝟙 A else 1 := by
  unfold incZ pa mkZ
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk A _) ⟨i⟩

theorem incZ_pb (j : Fin 4) : incZ A B ≫ pb A B j = 1 := by
  unfold incZ pb mkZ
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk A _) ⟨j⟩
end

theorem zarhinBundle_pullback_inclusion : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → LBIso c.P ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (GlobalTheory.ZarhinFam.incZ c.A B ⊗ₘ GlobalTheory.ZarhinFam.incZ c.A B).left) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _
  have hQ : Q.IsLB := hZ.2.1.isLB
  have hq0 : ∀ {Y : Over S} (a : Y ⟶ c.A), CechPic.pull (lift a (1 : Y ⟶ B)).left (cls Q hZ.2.1.isLB) = 0 :=
    fun a => evc_one_right hZ.2.1.isLB hZ.2.1.zero a
  have hp0 : ∀ {Y : Over S}, CechPic.pull (lift (1 : Y ⟶ c.A) (1 : Y ⟶ c.A)).left (cls c.P c.isLB) = 0 :=
    evc_one_left c.isLB c.rig₁ 1
  have hp1 : CechPic.pull (lift (fst c.A c.A) (snd c.A c.A)).left (cls c.P c.isLB) = cls c.P c.isLB := by
    rw [lift_fst_snd, Over.id_left, pull_id]
  refine (cls_eq_iff c.isLB (pull_isLB (zarhinBundle_isLineBundle _ _ _ _ _ _) _)).1 ?_
  rw [cls_pull (zarhinBundle_isLineBundle _ _ _ _ _ _), cls_zP]
  unfold zCls

  simp only [map_add (f := _), map_sum, map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, tensorHom_fst_assoc,
  tensorHom_snd_assoc, incZ_pa, incZ_pb, Fin.sum_univ_four]
  simp only [MonObj.comp_one, Category.comp_id, ↓reduceIte, Fin.isValue, Fin.reduceEq, one_ne_zero, hq0, hp0, hp1, smul_zero, add_zero, zero_add, Finset.sum_const_zero]

end GlobalTheory.ZarhinFam
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleIsomorphism

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhin_bundle_isomorphism : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → LBIso c.P ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (GlobalTheory.ZarhinFam.incZ c.A B ⊗ₘ GlobalTheory.ZarhinFam.incZ c.A B).left) := by
  first | (exact @GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (exact GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (intros; apply GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhinLevel_additive_killed_by_level : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a b, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (a + b) = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a * (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) ∧ ∀ a, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a ^ M = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors) | (exact GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors) | (intros; apply GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhinOrderAction_rosati_adjoint : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Adj (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) (GlobalTheory.ZarhinFam.bar d) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  first | (exact @GlobalTheory.ZarhinFam.AdjPf.adj_actZ) | (exact GlobalTheory.ZarhinFam.AdjPf.adj_actZ) | (intros; apply GlobalTheory.ZarhinFam.AdjPf.adj_actZ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProductStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhinOrder_isRingAction_on_product : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → IsRAct (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  first | (exact @GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (exact GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (intros; apply GlobalTheory.ZarhinFam.RAct.actZ_isRAct <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClausesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhinProduct_relation_algebraic_clauses : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → IsMonHom (GlobalTheory.ZarhinFam.incZ c.A B) ∧ IsMonHom (GlobalTheory.ZarhinFam.prZ c.A B) ∧ GlobalTheory.ZarhinFam.incZ c.A B ≫ GlobalTheory.ZarhinFam.prZ c.A B = 𝟙 c.A ∧ GlobalTheory.ZarhinFam.prZ c.A B ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.idem d) ∧ ∀ a, c.lev a ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (GlobalTheory.ZarhinFam.jlMap h a) := by
  first | (exact @GlobalTheory.ZarhinFam.zRel_alg) | (exact GlobalTheory.ZarhinFam.zRel_alg) | (intros; apply GlobalTheory.ZarhinFam.zRel_alg  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinObject

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem exists_zarhin_object : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  intro h M d h1 hM hodd hd hcop
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_zarhinSymplecticTransfer h M d h1 hM hodd hd hcop
  refine ⟨GlobalTheory.ZarhinFam.jlMap h, 8, GlobalTheory.ZarhinFam.oMat d, κ, fun S t c hdu hk => ?_⟩
  obtain ⟨B, _, _, Q, la, mu, hZ⟩ := GlobalTheory.T.exists_zarhin_data h M d S t c h1 hM hodd hd hcop hdu hk
  obtain ⟨r1, r2, sy⟩ := GlobalTheory.T.zarhinBundle_rigidified_symmetric h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk
  obtain ⟨la1, la2⟩ := GlobalTheory.T.zarhinLevel_additive_killed_by_level h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  have hab : IsAbelianScheme (GlobalTheory.ZarhinFam.Zob c.A B) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ (AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 3)
      (AbelianSchemeGerms.isAbelianScheme_powObj B hZ.1 3)
  let z : SiegPre (8 * h) M (zetaAway M) t :=
    { A := GlobalTheory.ZarhinFam.Zob c.A B
      ab := hab
      P := GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu
      isLB := GlobalTheory.ZarhinFam.zarhinBundle_isLineBundle c.A B c.isLB hZ.2.1.isLB d mu
      rig₁ := r1
      rig₂ := r2
      symm := sy
      lev := GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ
      lev_add := la1
      lev_tors := la2
      geom := GlobalTheory.T.zarhinTrick_level_symplectic_geometricPoints h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ }
  obtain ⟨i1, i2, i3, i4, i5⟩ := GlobalTheory.T.zarhinProduct_relation_algebraic_clauses h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  refine ⟨z, GlobalTheory.ZarhinFam.actZ c.A B d la mu, GlobalTheory.T.zarhinBundle_principal h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.T.zarhinOrder_isRingAction_on_product h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, GlobalTheory.T.zarhinOrderAction_rosati_adjoint h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.ZarhinFam.incZ c.A B, GlobalTheory.ZarhinFam.prZ c.A B, i1, i2, i3, i4,
    GlobalTheory.T.zarhin_bundle_isomorphism h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, i5, fun a => rfl⟩

end GlobalTheory.ZarhinFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinObjectStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.exists_principal_zarhin_object_of_siegKerBy : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  first | (exact @GlobalTheory.ZarhinFam.exists_zarhin_object) | (exact GlobalTheory.ZarhinFam.exists_zarhin_object) | (intros; apply GlobalTheory.ZarhinFam.exists_zarhin_object  <;> assumption)
end
end
