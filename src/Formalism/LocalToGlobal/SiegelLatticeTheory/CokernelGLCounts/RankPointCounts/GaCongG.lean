module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnipotentMatrixMapSecondComponent
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CjTFromBlocks

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CondXG

section

@[expose] public section

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L) {r : ℕ}

theorem q_ne (g : Formalism.MainNotions.S.Loc.SplitG M.L) : ((g.q : F)) ≠ 0 := by
  exact fun h => g.q_irr.ne_zero (Subtype.ext h)

theorem zzrel_G (hs : M.split = some g) {X X' L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (T T' : F)
    (h : Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X' T T' = L * Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X T T' * P) :
    X'.map (π1 M g) = L.map (π1 M g) * X.map (π1 M g) * P.map (π1 M g) ∧
    (X'.map (π2 M g))ᵀ = L.map (π2 M g) * (X.map (π2 M g))ᵀ * P.map (π2 M g) := by
  classical
  have hq : (g.q : F) ≠ 0 := q_ne M g
  have hπ1 : ∀ x : E, π1 M g x = (g.e x).1 := fun x => rfl
  have hπ2 : ∀ x : E, π2 M g x = (g.e x).2 := fun x => rfl
  have hZ : ∀ (Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)),
      Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T' a b =
        g.e.symm ((g.e (Y a b)).1 / (g.q : F), -((g.e (Y b a)).2 / (g.q : F))) -
        (if a = Fin.last r ∧ b = Fin.last r then g.e.symm (-T / (g.q : F), T' / (g.q : F)) else 0) := by
    intro Y a b
    simp only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs, Matrix.of_apply]
  let Ec : Matrix (Fin (r + 1)) (Fin (r + 1)) F :=
    Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then 1 else 0
  have hZ1 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π1 M g) =
      (g.q : F)⁻¹ • Y.map (π1 M g) + (T / (g.q : F)) • Ec := by
    intro Y
    ext a b
    by_cases hab : a = Fin.last r ∧ b = Fin.last r
    · simp only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_pos hab,
        Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_one]
      ring
    · simp only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_neg hab,
        map_zero, Prod.fst_zero, sub_zero, Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul,
        mul_zero, add_zero]
      ring
  have hZ2 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π2 M g) =
      -((g.q : F)⁻¹ • (Y.map (π2 M g))ᵀ) - (T' / (g.q : F)) • Ec := by
    intro Y
    ext a b
    by_cases hab : a = Fin.last r ∧ b = Fin.last r
    · simp only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_pos hab,
        Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, Ec, Matrix.of_apply,
        smul_eq_mul, mul_one]
      ring
    · simp only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_neg hab,
        map_zero, Prod.snd_zero, sub_zero, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
        Matrix.transpose_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_zero]
      ring
  have hE : ∀ φ : E →+* F, L.map φ * Ec * P.map φ = Ec := by
    intro φ
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Ec, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [Finset.sum_eq_single (Fin.last r)]
      · simp only [and_self, if_true, mul_one, hL, hP]
        split_ifs <;> simp_all
      · intro k _ hk
        simp [hk]
      · simp
    · intro l _ hl
      simp [hl]
    · simp
  have hinv : (g.q : F)⁻¹ ≠ 0 := inv_ne_zero hq
  constructor
  · have hmap := congrArg (fun Z => Matrix.map Z (π1 M g)) h
    simp only [Matrix.map_mul] at hmap
    rw [hZ1, hZ1] at hmap
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hE] at hmap
    exact smul_right_injective _ hinv (add_right_cancel hmap)
  · have hmap := congrArg (fun Z => Matrix.map Z (π2 M g)) h
    simp only [Matrix.map_mul] at hmap
    rw [hZ2, hZ2] at hmap
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
      hE] at hmap
    exact smul_right_injective _ hinv (neg_inj.1 (sub_left_inj.1 hmap))

theorem condX_G (hs : M.split = some g) {X X' L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (T T' : F)
    (h : Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X' T T' = L * Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X T T' * P) :
    cjT (M.L.cj : E →+* E) (mmG M g L P) * X * uuG M g L P = X' := by
  obtain ⟨h1, h2⟩ := zzrel_G M g hs hL hP T T' h
  have hπ1 : ∀ x : E, π1 M g x = (g.e x).1 := fun x => rfl
  have hπ2 : ∀ x : E, π2 M g x = (g.e x).2 := fun x => rfl
  have hcj : ∀ x : E, g.e ((M.L.cj : E →+* E) x) = (g.e x).swap := fun x => g.e_cj x
  ext i j
  apply g.e.injective
  refine Prod.ext ?_ ?_
  · have h1' := congrArg (fun A => A i j) h1
    simp only [Matrix.map_apply, Matrix.mul_apply, hπ1, Finset.sum_mul] at h1'

    simp only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.fst_sum,
    Prod.fst_mul, hcj, Prod.fst_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]
    rw [h1']
  · have h2' := congrArg (fun A => A j i) h2
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, hπ2, Finset.sum_mul] at h2'

    simp only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.snd_sum,
    Prod.snd_mul, hcj, Prod.snd_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]
    rw [h2', Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

theorem condM_G {L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : E) :
    cjT (M.L.cj : E →+* E) (mmG M g L P) * cornerM c * mmG M g L P = cornerM c := by
  have hm : ∀ i, mmG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0 := by
    intro i
    simp only [mmG, Matrix.of_apply, hP, hL]
    split_ifs <;> simp
  ext i j
  simp only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · simp only [and_self, if_true, hm]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    simp [hl]
  · simp

theorem condU_G {L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : E) :
    cjT (M.L.cj : E →+* E) (uuG M g L P) * cornerM c * uuG M g L P = cornerM c := by
  have hm : ∀ i, uuG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0 := by
    intro i
    simp only [uuG, Matrix.of_apply, hP, hL]
    split_ifs <;> simp
  ext i j
  simp only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · simp only [and_self, if_true, hm]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    simp [hl]
  · simp

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GaCongG

section

@[expose] public section

noncomputable section

open Matrix ValuativeRel
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents



variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

theorem e_alg (p : PlF D) (g : Loc.SplitG (M p).L) (x : (D.s.atP p).Fp) :
    g.e (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep x) = (x, x) := by
  rw [AlgEquiv.commutes]; rfl

theorem gaCong_G (hA : ∀ q, Agree δ M q) (p : PlF D) (g : Loc.SplitG (M p).L) (hs : (M p).split = some g)
    (T T' : D.host.E) (Tf Tf' : (D.s.atP p).Fp) (Z Z' : MatZ D)
    (L P : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)
    (hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0)
    (hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0)
    (hLR : ∀ i j, L i j ∈ (M p).R) (hPR : ∀ i j, P i j ∈ (M p).R)
    (hLu : ∃ y ∈ (M p).R, L.det * y = 1) (hPu : ∃ y ∈ (M p).R, P.det * y = 1)
    (hX : Loc.HermSp.ZZplusOf (M p) (ZhatLoc M δ p Z') Tf Tf' =
      L * Loc.HermSp.ZZplusOf (M p) (ZhatLoc M δ p Z) Tf Tf' * P) :
    ∃ A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
      GaPlus M δ p T T' Z' = (A.map (M p).L.cj).transpose * GaPlus M δ p T T' Z * A := by
  set cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep := ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) with hcj
  have hinv : ∀ x, cj (cj x) = x := fun x => (M p).L.cj_cj x
  set Mm := mmG (M p) g L P with hMm
  set U := uuG (M p) g L P with hU
  set qi : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) with hqi
  set A0 : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    Matrix.fromBlocks 1 (-qi • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) 0
      (qi • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) with hA0
  set B : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    Matrix.fromBlocks Mm (qi • (U - Mm)) 0 U with hB
  set At : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    Matrix.fromBlocks Mm 0 0 U with hAt
  have hplus : ∀ Y : MatZ D, GaPlus M δ p T T' Y = cjT cj A0 * GaLoc M δ p T T' Y * A0 := by
    intro Y; unfold GaPlus; rw [hs]; rfl
  have hloc : GaLoc M δ p T T' Z' = cjT cj At * GaLoc M δ p T T' Z * At := by
    rw [gaLoc_blocks δ M hA, gaLoc_blocks δ M hA]
    refine (block_cong cj hinv _ _ _ _ _ _ _ _ ?_ ?_ ?_).symm
    · rw [gDiag_corner]; exact condM_G (M p) g hL hP _
    · exact condX_G (M p) g hs hL hP Tf Tf' hX
    · rw [gDiag_corner]; exact condU_G (M p) g hL hP _
  have hcomm : A0 * B = At * A0 := by
    rw [hA0, hB, hAt, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_zero] <;> module
  refine ⟨B, ?_, ?_, ?_⟩
  ·
    have hcomp : ∀ x ∈ (M p).R, (g.e x).1 ∈ 𝒪[(D.s.atP p).Fp] ∧ (g.e x).2 ∈ 𝒪[(D.s.atP p).Fp] ∧
        ∃ c : 𝒪[(D.s.atP p).Fp], (g.e x).1 - (g.e x).2 = (g.q : (D.s.atP p).Fp) * c :=
      fun x hx => Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.comp_of_mem_R hs hx
    have hq := q_ne (M p) g
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · refine Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ ?_ ?_
      · simp [hB, hMm, mmG, (hcomp _ (hPR i j)).2.1]
      · simp [hB, hMm, mmG, (hcomp _ (hLR j i)).1]
    · obtain ⟨-, -, c, hc⟩ := hcomp _ (hPR i j)
      obtain ⟨-, -, c', hc'⟩ := hcomp _ (hLR j i)
      refine Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ ?_ ?_
      · have : (g.e (B (Sum.inl i) (Sum.inr j))).1 = c := by
          simp only [hB, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul,
            map_sub, hqi, e_alg, hU, hMm, uuG, mmG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Prod.fst_mul,
            Prod.fst_sub]
          rw [hc]; field_simp
        rw [this]; exact c.2
      · have : (g.e (B (Sum.inl i) (Sum.inr j))).2 = -c' := by
          simp only [hB, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul,
            map_sub, hqi, e_alg, hU, hMm, uuG, mmG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Prod.snd_mul,
            Prod.snd_sub]
          rw [show (g.e (L j i)).2 - (g.e (L j i)).1 = -((g.e (L j i)).1 - (g.e (L j i)).2) by ring, hc']
          field_simp
        rw [this]; exact (-c').2
    · simp [hB]
    · refine Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ ?_ ?_
      · simp [hB, hU, uuG, (hcomp _ (hPR i j)).1]
      · simp [hB, hU, uuG, (hcomp _ (hLR j i)).2.1]
  ·
    obtain ⟨yL, hyL, hLy⟩ := hLu
    obtain ⟨yP, hyP, hPy⟩ := hPu
    have cL := Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.comp_of_mem_R hs hyL
    have cP := Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.comp_of_mem_R hs hyP
    refine ⟨g.e.symm ((g.e yP).2 * (g.e yP).1, (g.e yL).1 * (g.e yL).2),
      Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ (by simpa using mul_mem cP.2.1 cP.1)
        (by simpa using mul_mem cL.1 cL.2.1), ?_⟩
    rw [hB, Matrix.det_fromBlocks_zero₂₁]
    apply g.e.injective
    have d1 : (g.e Mm.det).1 = (g.e P.det).2 := by
      have := RingHom.map_det (π1 (M p) g) Mm
      rw [π1_apply] at this
      rw [this, RingHom.mapMatrix_apply, middleMatrix_map_firstComponent, ← RingHom.mapMatrix_apply, ← RingHom.map_det, π2_apply]
    have d2 : (g.e Mm.det).2 = (g.e L.det).1 := by
      have := RingHom.map_det (π2 (M p) g) Mm
      rw [π2_apply] at this
      rw [this, RingHom.mapMatrix_apply, middleMatrix_map_secondComponent, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, π1_apply]
    have d3 : (g.e U.det).1 = (g.e P.det).1 := by
      have := RingHom.map_det (π1 (M p) g) U
      rw [π1_apply] at this
      rw [this, RingHom.mapMatrix_apply, unipotentMatrix_map_firstComponent, ← RingHom.mapMatrix_apply, ← RingHom.map_det, π1_apply]
    have d4 : (g.e U.det).2 = (g.e L.det).2 := by
      have := RingHom.map_det (π2 (M p) g) U
      rw [π2_apply] at this
      rw [this, RingHom.mapMatrix_apply, unipotentMatrix_map_secondComponent, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, π2_apply]
    have eL := congrArg g.e hLy
    have eP := congrArg g.e hPy
    rw [map_mul, map_one] at eL eP
    refine Prod.ext ?_ ?_
    · simp only [map_mul, Prod.fst_mul, AlgEquiv.apply_symm_apply, map_one, Prod.fst_one, d1, d3]
      have e1 := congrArg Prod.fst eP
      have e2 := congrArg Prod.snd eP
      simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_one, Prod.snd_one] at e1 e2
      linear_combination (g.e P.det).1 * (g.e yP).1 * e2 + e1
    · simp only [map_mul, Prod.snd_mul, AlgEquiv.apply_symm_apply, map_one, Prod.snd_one, d2, d4]
      have e1 := congrArg Prod.fst eL
      have e2 := congrArg Prod.snd eL
      simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_one, Prod.snd_one] at e1 e2
      linear_combination (g.e L.det).2 * (g.e yL).2 * e1 + e2
  ·
    show GaPlus M δ p T T' Z' = cjT cj B * GaPlus M δ p T T' Z * B
    rw [hplus, hplus, hloc]
    calc cjT cj A0 * (cjT cj At * GaLoc M δ p T T' Z * At) * A0
        = cjT cj (At * A0) * GaLoc M δ p T T' Z * (At * A0) := by
          rw [cjT_mul]; simp only [Matrix.mul_assoc]
      _ = cjT cj (A0 * B) * GaLoc M δ p T T' Z * (A0 * B) := by rw [hcomm]
      _ = cjT cj B * (cjT cj A0 * GaLoc M δ p T T' Z * A0) * B := by
          rw [cjT_mul]; simp only [Matrix.mul_assoc]

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end
end
