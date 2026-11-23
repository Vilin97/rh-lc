module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BaseAt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumShift
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumShift
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TargetFact
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEGen

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountBase

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.CountBase

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.AtPt
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem zhatOM_sg (X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    ZhatOM X * Sg D.host.E D.R.rS = X := by
  ext a b
  simp only [ZhatOM, Sg, Matrix.mul_diagonal]
  rw [mul_comm, ← mul_assoc, ← mul_pow]
  simp

theorem modMat_ord (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D) (hM : (M p).split = none)
    (w : Point D.host.E (D.R.rS + 1)) :
    Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) *
        (ptMat w).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) =
      modMat δ T T' p w := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hR : (D.s.atP p).split = none := by
    have h := (hA p).2.2.2.2.2
    rw [hM] at h
    cases h' : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [h'] at h; exact h.elim
  ext a b
  rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
  by_cases hb : b = sgF w a
  · rw [if_pos hb, if_pos hb, modMat_blk Zd]
    simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul]
    subst hb
    ring
  · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]

theorem baseConj_L (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (hM : (M p).split = none) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) :
    Formalism.L2.SG.Pf.ProdE.Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p +
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w = a.mat := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hY := Formalism.L2.SG.Pf.PCount.zzp_sgn_ord Zd u u' p hM (ZhatOM (ptMat w))
  rw [zhatOM_sg] at hY
  have hmat := Formalism.L2.SG.Pf.LocOrbSumPf.modShift_holds δ (D.mem u).A.T (D.mem u').A.T p w a ha
  rw [hmat]
  unfold Formalism.L2.SG.Pf.ProdE.Y0
  congr 1
  rw [show Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p =
    Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p from rfl, hY]
  exact modMat_ord hA _ _ p hM w

end Formalism.L2.SG.Pf.CountBase
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountBaseT

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Corner

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isLo_of_uni {L : Matrix (Fin n) (Fin n) R} (h : IsLoUni L) : IsLo L :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h a b).1 hab⟩

theorem isUp_of_uni {U : Matrix (Fin n) (Fin n) R} (h : IsUpUni U) : IsUp U :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h b a).1 hab⟩

theorem uni_of_isLo {L : Matrix (Fin n) (Fin n) R} (h : IsLo L) : IsLoUni L :=
  fun a b => ⟨fun hab => h.2 a b hab, fun e => by subst e; exact h.1 a⟩

theorem uni_of_isUp {U : Matrix (Fin n) (Fin n) R} (h : IsUp U) : IsUpUni U :=
  fun a b => ⟨fun hab => h.2 b a hab, fun e => by subst e; exact h.1 a⟩

end Corner

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def glOfLo {L : MP p} (h : IsLo L) : GLp p :=
  ⟨L, L⁻¹, Matrix.mul_nonsing_inv L (by
      rw [Matrix.det_of_lowerTriangular L (fun a b hab => h.2 a b hab)]
      simp [h.1]),
    Matrix.nonsing_inv_mul L (by
      rw [Matrix.det_of_lowerTriangular L (fun a b hab => h.2 a b hab)]
      simp [h.1])⟩

def glOfUp {U : MP p} (h : IsUp U) : GLp p :=
  ⟨U, U⁻¹, Matrix.mul_nonsing_inv U (by
      rw [Matrix.det_of_upperTriangular (fun a b hab => h.2 b a hab)]
      simp [h.1]),
    Matrix.nonsing_inv_mul U (by
      rw [Matrix.det_of_upperTriangular (fun a b hab => h.2 b a hab)]
      simp [h.1])⟩

theorem glue_one_one {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] (e : K ≃ₐ[Fp] Fp × Fp) {n : ℕ} :
    glue e (1 : Matrix (Fin n) (Fin n) Fp) 1 = 1 :=
  mat_eq e (by rw [glue_map_fst, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [glue_map_snd, Matrix.map_one _ (map_zero _) (map_one _)])

theorem corner_fix {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] (e : K ≃ₐ[Fp] Fp × Fp) {n : ℕ}
    {l ρ Δ : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hl : IsLoUni l) (hρ : IsUpUni ρ) (k1 k2 : Fp)
    (h1 : Δ.map (p1 e) = k1 • Ecorner n) (h2 : Δ.map (p2 e) = k2 • Ecorner n) : l * Δ * ρ = Δ := by
  apply mat_eq e
  · rw [Matrix.map_mul, Matrix.map_mul, h1, Matrix.mul_smul, Matrix.smul_mul,
      lo_corner_up (isLo_map _ (isLo_of_uni hl)) (isUp_map _ (isUp_of_uni hρ))]
  · rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_smul, Matrix.smul_mul,
      lo_corner_up (isLo_map _ (isLo_of_uni hl)) (isUp_map _ (isUp_of_uni hρ))]



theorem baseAt_typed (hA : ∀ p, Agree δ M p) (g : Loc.SplitG (M p).L) (hM : (M p).split = some g)
    (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) :
    BaseAt M δ u u' w p a := by
  have hAg := (hA p).2.2.2.2.2
  rw [hM] at hAg
  obtain ⟨sg, hR, hge, hgq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q := by
    rcases hs : (D.s.atP p).split with _ | sg
    · rw [hs] at hAg; exact hAg.elim
    · rw [hs] at hAg; exact ⟨sg, rfl, hAg.1, hAg.2⟩
  let Zd : LocDat D := ⟨δ, M, hA⟩
  have hzz := Formalism.L2.SG.Pf.PCountEx.zz_fact Zd p sg hR g hM hge hgq u u' w (L := 1) (B := 1)
    Formalism.L2.SG.Pf.PCountEx.isLo_one' Formalism.L2.SG.Pf.PCountEx.isUp_one'
  have e1 : Matrix.diagonal (cf Zd p) * (1 : PairVal.MatR D).map ((p1 sg.e).comp (D.s.atP p).ιE) *
      Matrix.diagonal (cfi Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      show (fun a => cf Zd p a * cfi Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cf_cfi Zd p),
      Matrix.diagonal_one]
  have e2 : Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
      ((1 : PairVal.MatR D).map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cfi Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, sg_sq, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal,
      show (fun a => cf Zd p a * cfi Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cf_cfi Zd p),
      Matrix.diagonal_one]
  have e3 : Matrix.diagonal (cfi Zd p) * (1 : PairVal.MatR D).map ((p1 sg.e).comp (D.s.atP p).ιE) *
      Matrix.diagonal (cf Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      show (fun a => cfi Zd p a * cf Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cfi_cf Zd p),
      Matrix.diagonal_one]
  have e4 : Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
      ((1 : PairVal.MatR D).map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cf Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, sg_sq, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal,
      show (fun a => cfi Zd p a * cf Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cfi_cf Zd p),
      Matrix.diagonal_one]
  rw [e1, e2, e3, e4, glue_one_one, Matrix.one_mul, Matrix.mul_one] at hzz
  have hz : ZhatOM (ptMat w) = ptMat w * Sg D.host.E D.R.rS := by
    have h := Formalism.L2.SG.Pf.CountBase.zhatOM_sg (ptMat w)
    calc ZhatOM (ptMat w) = ZhatOM (ptMat w) * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS := by
          rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
      _ = ptMat w * Sg D.host.E D.R.rS := by rw [h]
  rw [Matrix.one_mul, Matrix.mul_one, ← hz] at hzz
  have hYg : Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p = _ := hzz
  obtain ⟨Gl, Gu, hGl, hGu, hT⟩ := Formalism.L2.SG.Pf.PCountEx.target_fact Zd p sg hR g hM hge hgq u u' w
  have hY0 : Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p = Gl * modMat δ (D.mem u).A.T (D.mem u').A.T p w * Gu :=
    hzz.trans hT
  have hshE : Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
      Formalism.MainNotions.S.LocalSplitGroups.cornerSh δ (D.mem u).A.T (D.mem u').A.T p w • Ecorner D.R.rS := by
    ext i j
    simp only [Formalism.L2.SG.Pf.LocOrbSumPf.shM, Ecorner, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hsh : Gl * Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w * Gu =
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [hshE, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hGl hGu]
  have hmod := Formalism.L2.SG.Pf.LocOrbSumPf.modShift_holds δ (D.mem u).A.T (D.mem u').A.T p w a ha
  refine ⟨⟨(glOfLo p hGl, MulOpposite.op (glOfUp p hGu)), uni_of_isLo hGl, uni_of_isUp hGu⟩, ?_, ?_⟩
  · show Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
      Gl * a.mat * Gu
    rw [hmod, Matrix.mul_add, Matrix.add_mul, hsh, ← hY0]
  · intro x

    have hd1 : (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w).map
        (p1 sg.e) = ((if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then -((D.mem u).A.T : (D.s.atP p).Fp) /
          (sg.q : (D.s.atP p).Fp) else 0) - (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))) •
          Ecorner D.R.rS := by
      rw [Matrix.map_sub _ (map_sub _), hYg, glue_map_fst, Formalism.L2.SG.Pf.PCount.mm1' Zd p sg hR g hM hge hgq, sub_sub_sub_cancel_left,
        ← sub_smul]
    have hd2 : (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w).map
        (p2 sg.e) = ((if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then ((D.mem u').A.T : (D.s.atP p).Fp) /
          (sg.q : (D.s.atP p).Fp) else 0) - ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))) •
          Ecorner D.R.rS := by
      rw [Matrix.map_sub _ (map_sub _), hYg, glue_map_snd, Formalism.L2.SG.Pf.PCount.mm2' Zd p sg hR g hM hge hgq, sub_sub_sub_cancel_left,
        ← sub_smul]
    have hfix := corner_fix sg.e x.2.1 x.2.2 _ _ hd1 hd2
    have hphi : phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = a.mat +
        (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w) := by
      show Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
        _
      rw [hmod]; abel
    rw [hphi, smul_def, smul_def, Matrix.mul_add, Matrix.add_mul, hfix]
    constructor
    · intro h; exact add_right_cancel h
    · intro h; rw [h]

theorem baseAt_holds (hA : ∀ p, Agree δ M p) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) : BaseAt M δ u u' w p a := by
  rcases hM : (M p).split with _ | g
  · have h := Formalism.L2.SG.Pf.CountBase.baseConj_L hA u u' w p hM a ha
    refine ⟨1, ?_, fun x => ?_⟩
    · rw [OneMemClass.coe_one, one_smul]; exact h
    · show _ ↔ _
      rw [show phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = a.mat from h]
  · exact baseAt_typed M δ u u' w p hA g hM a ha

end Formalism.L2.SG.Pf.CountAt
end
end
end
