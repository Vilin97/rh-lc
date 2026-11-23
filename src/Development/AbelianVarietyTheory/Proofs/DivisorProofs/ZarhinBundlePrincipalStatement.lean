module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomZarhinProductToEighthPowerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulZarhinDiagonalClassEqFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelFirstCoordEquationsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjoint
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
import Mathlib.Tactic.Basify
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelSecondCoordEquations
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinKernelLinearAlgebraTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelOfSecondCoordTrivial

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam.KerC

theorem ker_zarhinPolarization_of_pullback : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → (∀ j, x ≫ GlobalTheory.ZarhinFam.pb c.A B j = 1) → ∀ j, ∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx hv j
  obtain ⟨hB, hD1, hD2, hla, hmu, hlm, hml, hPiso⟩ := id hZ
  haveI : IsMonHom la := hla
  have hQ : Q.IsLB := hD1.isLB
  have hPQ : ∀ (Y : Over S) (a a' : Y ⟶ c.A), evc c.isLB a a' = evc hQ a (a' ≫ la) := by
    have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hPiso
    intro Y a a'
    show CechPic.pull (lift a a').left (cls c.P c.isLB) = _
    rw [e, pull_evc, lift_fst, lift_snd_assoc]
  have hz := zarhinBundle_isLineBundle c.A B c.isLB hQ d mu
  have h0 : CechPic.pull (lift (snd (Zob c.A B) T ≫ x) (fst (Zob c.A B) T)).left
      (zCls c.A B c.isLB hQ d mu) = 0 := by
    rw [← cls_zP c.A B c.isLB hQ d mu, ← cls_pull hz]
    exact (cls_eq_zero_iff (pull_isLB hz _)).2 hx
  have h1 := congrArg (CechPic.pull
    (lift (mkZ c.A B (fun _ => 1) (fun j' => if j' = j then snd T B else 1)) (fst T B) :
      T ⊗ B ⟶ Zob c.A B ⊗ T).left) h0
  rw [← pull_comp, ← Over.comp_left, comp_lift, map_zero, lift_snd_assoc, lift_fst,
    AdjPf.pull_zCls c.isLB hQ d la mu hPQ] at h1
  simp only [AdjPf.zf, Category.assoc, AdjPf.mkZ_pa, AdjPf.mkZ_pb, hv, MonObj.comp_one, MonObj.one_comp,
    evc_one_right hQ hD1.zero, hD1.additive.evc_one hQ, smul_zero, Finset.sum_const_zero, zero_add, add_zero] at h1
  simp only [apply_ite (evc hQ _), evc_one_right hQ hD1.zero, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h1
  refine (hD1.isPerfect hD2).ker_left T _ ((triv_ev_iff hQ _ _).2 ?_)
  let F : (T ⊗ B ⟶ c.A) →* Multiplicative (Pic (T ⊗ B).left) :=
    MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hQ a (snd T B))) fun a a' => by
      rw [(isAdditive_iff hQ).1 hD1.additive, ofAdd_add]
  have eF : ∀ a, evc hQ a (snd T B) = Multiplicative.toAdd (F a) := fun _ => rfl
  have ep : fst T B ≫ ∏ i, (x ≫ pa c.A B i) ^ quat d j i = ∏ i, (fst T B ≫ x ≫ pa c.A B i) ^ quat d j i := by
    have := map_prod (AdjPf.pre (G := c.A) (fst T B)) (fun i => (x ≫ pa c.A B i) ^ quat d j i) Finset.univ
    simp only [map_zpow] at this
    exact this
  rw [ep, eF, map_prod, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, ← eF]
  exact h1

end GlobalTheory.ZarhinFam.KerC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelOfSecondCoordTrivialStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhinBundle_kernel_of_secondCoord_trivial : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → (∀ j, x ≫ GlobalTheory.ZarhinFam.pb c.A B j = 1) → ∀ j, ∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.KerC.ker_zarhinPolarization_of_pullback) | (exact GlobalTheory.ZarhinFam.KerC.ker_zarhinPolarization_of_pullback) | (intros; apply GlobalTheory.ZarhinFam.KerC.ker_zarhinPolarization_of_pullback  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelSecondCoordEquationsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhinBundle_kernel_secondCoord_equations : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ j, ((∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i) ≫ la) * (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ d = 1 := by
  first | (exact @GlobalTheory.ZarhinKerB.zarhinBundle_kernel) | (exact GlobalTheory.ZarhinKerB.zarhinBundle_kernel) | (intros; apply GlobalTheory.ZarhinKerB.zarhinBundle_kernel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTriangularMatrixSymmetrisationPosDef

section

@[expose] public section

open Matrix

namespace GlobalTheory.ZarhinFam

theorem zW_symm_blocks (d : ℕ) (i j : Fin 4 ⊕ Fin 4) :
    Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 i j +
      Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 j i =
    2 * Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1 i j := by
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.zero_apply, smul_eq_mul]
  all_goals (try simp only [@eq_comm _ b a])
  all_goals (try split_ifs)
  all_goals ring

theorem zarhin_block_posDef {d : ℕ} (hd : 0 < d) :
    (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
      (Int.cast : ℤ → ℝ) |>.PosDef := by
  set x : Matrix (Fin 4) (Fin 4) ℝ := (quat d).map (Int.cast : ℤ → ℝ) with hx
  have hxx : xᵀ * x = ((d : ℝ) - 1) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    have h1 : (((d - 1 : ℕ) : ℤ) : ℝ) = (d : ℝ) - 1 := by
      rw [Int.cast_natCast, Nat.cast_sub (by omega)]; simp
    ext i j
    have h0 := congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun (quat_transpose_mul d) i) j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Int.cast_sum, Int.cast_mul, hx, Matrix.map_apply] at h0 ⊢
    rw [h0]
    split_ifs <;> simp [Nat.cast_sub (show 1 ≤ d by omega)]
  set C : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 x 1 with hC
  set C' : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 (-x) 1 with hC'
  have hCC : C' * C = 1 := by
    rw [hC, hC', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]; simp
  have hinj : Function.Injective C.mulVec := by
    intro v w hvw
    have := congrArg (C'.mulVec) hvw
    simpa [Matrix.mulVec_mulVec, hCC] using this
  have key : Cᴴ * 1 * C =
      (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
        (Int.cast : ℤ → ℝ) := by
    rw [Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial, hC, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map]
    congr 1
    · rw [Matrix.transpose_one, Matrix.one_mul, hxx]; ext i j
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> simp
    · simp [hx, Matrix.transpose_map]
    · simp [hx]
    · simp
  rw [← key]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

theorem zW_symm_posDef : ∀ (d : ℕ), 0 < d →
    ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  intro d hd
  have hsig : Function.Injective sig := by
    intro a b h; revert a b h; decide
  have h := ((zarhin_block_posDef hd).smul (a := (2 : ℝ)) two_pos).submatrix hsig
  convert h using 1
  ext k l
  have e := zW_symm_blocks d (sig k) (sig l)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [zW, zW, e]
  push_cast
  ring

end GlobalTheory.ZarhinFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTriangularMatrixSymmetrisationPosDefStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.zarhinTriangularMatrix_symmetrisation_posDef : ∀ (d : ℕ), 0 < d → ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  first | (exact @GlobalTheory.ZarhinFam.zW_symm_posDef) | (exact GlobalTheory.ZarhinFam.zW_symm_posDef) | (intros; apply GlobalTheory.ZarhinFam.zW_symm_posDef  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundlePrincipal

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic

theorem principal_zP : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Out.RelAmple (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) ∧ ∀ (T : Over S) (x : T ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → x = 1 := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ hunit hK
  refine ⟨?_, fun T x hx => ?_⟩
  · have hAb : IsAbelianScheme (Zob c.A B) := AbelianSchemeGerms.isAbelianScheme_tensor _ _
      (AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 3) (AbelianSchemeGerms.isAbelianScheme_powObj B hZ.1 3)
    have := hAb.proper
    have hA : Out.RelAmple c.A c.diag := hK.1
    have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ Out.powObj c.A 8,
        ∀ u, x ≫ Out.powPr c.A u = y u := fun T y =>
      ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
        fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
    have h8 := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef GlobalTheory.SemiRigid.globalFns h M 8 _ _ S t c
      (Out.powObj c.A 8) (Out.powPr c.A) (zW d) (fun u => inferInstance) huniv hA (GlobalTheory.T.zarhinTriangularMatrix_symmetrisation_posDef d hd)
    have := GlobalTheory.T.isAffineHom_zarhinProduct_to_eighthPower h M d S t c B Q la mu hZ hd hunit
    have hF : (LB.LinComb c.P (K := Fin 8 × Fin 8)
        (fun uv => (lift (Out.powPr c.A uv.1) (Out.powPr c.A uv.2)).left) (fun uv => zW d uv.1 uv.2)).IsLB :=
      LB.isLB_linComb c.isLB _ _
    have hp := GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom (zphi c.A B mu) hF h8
    have hzP := zarhinBundle_isLineBundle c.A B c.isLB hZ.2.1.isLB d mu
    refine GlobalTheory.PosDefAmple.relAmple_of_nsmul (pull_isLB hzP _) (pull_isLB hF _) (N := d) hd ?_ hp

    rw [cls_pull hzP, cls_zP, cls_pull hF, cls_linComb c.isLB, GlobalTheory.T.nsmul_zarhinDiagonalClass_eq_form h M d S t c B Q la mu hZ hd, map_sum]
    refine Finset.sum_congr rfl fun kl _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, zphi_powPr, zphi_powPr]
  · have hla := hZ.2.2.2.1
    have hmu := hZ.2.2.2.2.1
    let f : (T ⟶ c.A) →* (T ⟶ B) := MonoidHom.mk' (fun a => a ≫ la) (fun a b => MonObj.mul_comp a b la)
    let g : (T ⟶ B) →* (T ⟶ c.A) := MonoidHom.mk' (fun a => a ≫ mu) (fun a b => MonObj.mul_comp a b mu)
    have hfg : ∀ a, g (f a) = a ^ d := fun a => by
      change (a ≫ la) ≫ mu = a ^ d
      rw [Category.assoc, hZ.2.2.2.2.2.1, MonObj.comp_pow, Category.comp_id]
    obtain ⟨hu, hv⟩ := GlobalTheory.T.zarhin_kernel_linearAlgebra_trivial d (T ⟶ c.A) (T ⟶ B) f g hd hfg (fun i => x ≫ pa c.A B i) (fun j => x ≫ pb c.A B j)
      (fun i => by simpa [f, Category.assoc] using GlobalTheory.T.zarhinBundle_kernel_firstCoord_equations h M d S t c B Q la mu hZ T x hx i)
      (fun j => GlobalTheory.T.zarhinBundle_kernel_secondCoord_equations h M d S t c B Q la mu hZ T x hx j)
      (GlobalTheory.T.zarhinBundle_kernel_of_secondCoord_trivial h M d S t c B Q la mu hZ T x hx)
    have e1 : x ≫ fst _ _ = 1 := (Out.powIsLimit c.A 4).hom_ext fun ⟨i⟩ => by
      change (x ≫ fst _ _) ≫ Out.powPr c.A i = 1 ≫ Out.powPr c.A i
      rw [MonObj.one_comp]
      exact (Category.assoc _ _ _).trans (hu i)
    have e2 : x ≫ snd _ _ = 1 := (Out.powIsLimit B 4).hom_ext fun ⟨j⟩ => by
      change (x ≫ snd _ _) ≫ Out.powPr B j = 1 ≫ Out.powPr B j
      rw [MonObj.one_comp]
      exact (Category.assoc _ _ _).trans (hv j)
    ext1
    · rw [e1, MonObj.one_comp]
    · rw [e2, MonObj.one_comp]

end GlobalTheory.ZarhinFam
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundlePrincipalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhinBundle_principal : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Out.RelAmple (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) ∧ ∀ (T : Over S) (x : T ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → x = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.principal_zP) | (exact GlobalTheory.ZarhinFam.principal_zP) | (intros; apply GlobalTheory.ZarhinFam.principal_zP <;> assumption)
end
end
