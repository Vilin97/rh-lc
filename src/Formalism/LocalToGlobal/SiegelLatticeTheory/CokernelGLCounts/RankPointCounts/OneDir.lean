module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrFacInvMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemSpanO
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXFinsetSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
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
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
import Mathlib.Tactic.ReduceModChar
import Formalism.PeriodIntegrals.PairValDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LmatUp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemSpanAaF
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SgnConjIntUp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.StepGram
import Mathlib.Tactic.ENatToNat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AaF

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntPFmat

section

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs PI.NRCW IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable (D : D7)

theorem intP_fmat (P : HeightOneSpectrum (𝓞 D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E}
    (G : LFlag (D.sp.Y 0) D.R.rS T) (m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hm : m ∈ NLam Λ G)
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (hz : G.fl.z ∈ Λ)
    (c b : Fin (D.R.rS + 1)) : IntP P (fmat D G m c b) := by
  have hfLP : ∀ c, frame G c ∈ LP P Λ := by
    intro c
    induction c using Fin.lastCases with
    | last => rw [frame_last]; exact mem_localization_of_mem₃ P hz
    | cast i => rw [frame_castSucc]; exact e_mem_LP P hC hP i
  have hmLP : m (frame G b) - frame G b ∈ LP P Λ :=
    sub_mem_localization P (LP_map P (m : (VS D).V →ₗ[D.host.E] (VS D).V) (fun v hv => nlam_mem hm hv) (hfLP b)) (hfLP b)
  have h01 : ∀ (t : Prop) [Decidable t], IntP P (if t then (1 : D.host.E) else 0) := by
    intro t _
    split_ifs
    · simpa using intP_O P 1
    · simpa using intP_O P 0
  unfold fmat
  apply intP_add P (h01 _)
  split_ifs with h
  · exact coef_intP P hC hP hmLP (frame_d_mem G hm b) _
  · simpa using intP_O P 0

theorem frame_nm (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (G₁ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (b : Fin (D.R.rS + 1)) :
    n (m (frame G₁ b)) = ∑ d, (fmat D G n * fmat D G₁ m) d b • frame G d +
      n (∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c)) := by
  rw [(stepExp D Λ G₁ m hm).2 b]
  have e1 : ∑ c, fmat D G₁ m c b • frame G₁ c =
      ∑ c, fmat D G₁ m c b • frame G c + ∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← smul_add, add_sub_cancel]
  rw [e1, map_add (f := _)]
  congr 1

  rw [map_sum]
  simp only [map_smul, (stepExp D Λ G n hn).2, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ => ?_))
  rw [mul_comm]

theorem cong_at (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (G₁ G₂ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (hfr : ∀ a, frame G₂ a = n (m (frame G₁ a))) (hC : IsFixedConv Λ (gS D) G)
    (hC₁ : IsFixedConv Λ (gS D) G₁) (hA1 : AdmWit Λ (gS D) G G₁ 1) (hA2 : AdmWit Λ (gS D) G G₂ 1)
    (hz₁ : G₁.fl.z ∈ Λ) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hg : ((gS D : ℕ) : D.host.E) ≠ 0) (d : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    IntP P ((fmat D G n * fmat D G₁ m - 1) d.castSucc b / (gS D : D.host.E)) := by
  have hw : ∀ c, frame G₁ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA1.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hw2 : ∀ c, frame G₂ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA2.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hNU := (stepExp D Λ G n hn).1
  have hMU := (stepExp D Λ G₁ m hm).1

  set Y := ∑ d', (fmat D G n * fmat D G₁ m - 1) d' b • frame G d' with hYdef
  have hYeq : Y = (frame G₂ b - frame G b) - n (∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c)) := by
    rw [hfr b, frame_nm D Λ G G₁ n m hn hm b, hYdef]
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
    have e1 : ∑ d', (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) d' b • frame G d' = frame G b := by
      simp [Matrix.one_apply]
    rw [e1]
    abel
  have hYLg : Y ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    rw [hYeq]
    refine sub_mem (hw2 b) ?_
    exact LP_map P (n : (VS D).V →ₗ[D.host.E] (VS D).V) (nlam_gLam hn _)
      (LP_sum P _ _ fun c _ => smul_mem_localization P (intP_fmat D P Λ G₁ m hm hC₁ hP hz₁ c b) (hw c))

  have hlast : (fmat D G n * fmat D G₁ m - 1) (Fin.last D.R.rS) b = 0 := by
    rw [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.last D.R.rS)]
    · rw [(hNU _ _).2 rfl, one_mul, Matrix.one_apply]
      by_cases hb : Fin.last D.R.rS = b
      · rw [(hMU _ _).2 hb, if_pos hb, sub_self]
      · have hlt : b < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last b) (Ne.symm hb)
        rw [(hMU _ _).1 hlt, if_neg hb, sub_self]
    · intro c _ hc
      have hlt : c < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last c) hc
      rw [(hNU _ _).1 hlt, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hYsum : Y = ∑ d' : Fin D.R.rS, (fmat D G n * fmat D G₁ m - 1) d'.castSucc b • G.fl.e d' := by
    rw [hYdef, Fin.sum_univ_castSucc, hlast, zero_smul, add_zero]
    refine Finset.sum_congr rfl (fun d' _ => ?_)
    rw [frame_castSucc]
  have hYX : Y ∈ G.fl.X := by
    rw [hYsum]
    exact Submodule.sum_mem _ fun d' _ => Submodule.smul_mem _ _ (e_mem_X _ d')
  have hcoef := coef_intP_g P hC hP hg hYLg hYX d
  have hYd : G.fl.coefX Y d = (fmat D G n * fmat D G₁ m - 1) d.castSucc b := by
    rw [hYsum, coefX_finset_sum _ _ _ (fun d' => Submodule.smul_mem _ _ (e_mem_X _ d'))]
    simp only [coefX_smul_e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hYd] at hcoef
  exact hcoef

end Cong

end Formalism.L2.SG.Pf.FibQ
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IotaMemO

section

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Bridge

variable {D : D7}

def condI (y : D.host.E) : Ideal (𝓞 D.host.E) where
  carrier := {t | ∃ o : 𝓞 D.host.E, (t : D.host.E) * y = o}
  add_mem' := by
    rintro a b ⟨o₁, h₁⟩ ⟨o₂, h₂⟩
    exact ⟨o₁ + o₂, by push_cast; rw [add_mul, h₁, h₂]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ⟨o, h⟩
    exact ⟨c * o, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, h]⟩

theorem iota_mem_O (p : PlF D) (y : D.host.E)
    (h : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → IntP P y) :
    (D.s.atP p).ιE y ∈ (D.s.atP p).O := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.iE_mem_O_iff_D]
  have := p.isPrime
  by_contra hno
  push Not at hno
  have hle : (condI y).comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ p.asIdeal := by
    intro s hs
    by_contra hsp
    obtain ⟨o, ho⟩ := hs
    apply hno s hsp
    have e : algebraMap D.host.F D.host.E (s : D.host.F) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s : 𝓞 D.host.E) : D.host.E) := by
      rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E,
        IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E]
    rw [e, ho]
    exact o.2
  obtain ⟨Q, hIQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (condI y) hle
  have hQ0 : Q ≠ ⊥ := by
    intro hb
    apply p.ne_bot
    rw [← hQc, hb]
    change Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ⊥ = ⊥
    rw [Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E)
  obtain ⟨t, ht, o, hto⟩ := h ⟨Q, hQp, hQ0⟩ hQc
  exact ht (hIQ ⟨o, hto⟩)

end Bridge

end Formalism.L2.SG.Pf.FibQ
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUSubOne

section

@[expose] public section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LocU

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem locU_mul (A B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    locU Z p A * locU Z p B = locU Z p (A * B) := by
  ext i j

  simp only [Matrix.mul_apply, locU_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc _ = Ring.inverse (frFac Z.δ p i) * (D.s.atP p).ιE (A i k) *
        (frFac Z.δ p k * Ring.inverse (frFac Z.δ p k)) * (D.s.atP p).ιE (B k j) * frFac Z.δ p j := by ring
    _ = _ := by rw [frFac_mul_inv, mul_one]; ring

theorem locU_sub_one (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    locU Z p A - 1 = locU Z p (A - 1) := by
  ext i j
  simp only [Matrix.sub_apply, locU_apply, map_sub, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [map_one, mul_sub, sub_mul, mul_one, frFac_inv_mul]
  · simp only [map_zero, sub_zero]

end LocU

end Formalism.L2.SG.Pf.FibQ
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TypedSplit

section

@[expose] public section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneDir

variable {D : D7} (Zd : LocDat D)

theorem typed_split (p : PlF D) {g : Formalism.MainNotions.S.Loc.SplitG (Zd.M p).L} (hs : (Zd.M p).split = some g) :
    ∃ sg, (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q := by
  have h := (Zd.agree p).2.2.2.2.2
  rw [hs] at h
  cases hsg : (D.s.atP p).split with
  | none => rw [hsg] at h; exact h.elim
  | some sg => rw [hsg] at h; exact ⟨sg, rfl, h.1, h.2⟩

theorem gS_mem_of_split (p : PlF D) {sg} (hsg : (D.s.atP p).split = some sg) :
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal →
      ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := fun P hP =>
  (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P hP).2 (by rw [← D.s_split p, hsg]; rfl)

end OneDir

end Formalism.L2.SG.Pf.FibQ
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OneDir

section

@[expose] public section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneDir2

variable {D : D7} (Zd : LocDat D)

theorem nm_last (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (G₁ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (b : Fin (D.R.rS + 1)) :
    (fmat D G n * fmat D G₁ m - 1) (Fin.last D.R.rS) b = 0 := by
  have hNU := (stepExp D Λ G n hn).1
  have hMU := (stepExp D Λ G₁ m hm).1
  rw [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.last D.R.rS)]
  · rw [(hNU _ _).2 rfl, one_mul, Matrix.one_apply]
    by_cases hb : Fin.last D.R.rS = b
    · rw [(hMU _ _).2 hb, if_pos hb, sub_self]
    · have hlt : b < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last b) (Ne.symm hb)
      rw [(hMU _ _).1 hlt, if_neg hb, sub_self]
  · intro c _ hc
    have hlt : c < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last c) hc
    rw [(hNU _ _).1 hlt, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem one_dir {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hRL : IsRowLat D F0 Λ)
    (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hP₁ : Formalism.L2.SG.TermDef.PD D Λ (lf D F0) u' F₁) (hA₁ : AdmWit Λ (gS D) (lf D F0) F₁ 1)
    (hA₂ : AdmWit Λ (gS D) (lf D F0) F₂ 1) (hdc : Formalism.L2.SG.TermDef.DCRel Λ (lf D F0) F₁ F₂) (p : PlF D) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Zd.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Zd.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatL (lf D F0) F₂) * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatL (lf D F0) F₁) * Formalism.L2.SG.LsDatumB.sgnP p) *
          ρ := by
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hdc
  have hEn := stepExp D Λ (lf D F0) n hn
  have hEm := stepExp D Λ F₁ m hm
  have hrel := stepGram D (lf D F0) F₁ F₂ n m (fmat D (lf D F0) n) (fmat D F₁ m) hn.1.1 hEn.2 hEm.2 hfr
  have hXS : XLam Λ (lf D F0) = XS D (lf D F0).fl := hRL.2.2
  have hz : (lf D F0).fl.z ∈ Λ := hRL.2.1.2.2.1.1
  have hNb := entry_mem D Λ (lf D F0) n hn hXS hz
  have hMb := entry_mem D Λ F₁ m hm hP₁.2.2.2 hP₁.1.1
  have hNU : ∀ a b, b < a → fmat D (lf D F0) n a b = 0 := fun a b h => (hEn.1 a b).1 h
  have hNd : ∀ a, fmat D (lf D F0) n a a = 1 := fun a => (hEn.1 a a).2 rfl
  have hMU : ∀ a b, b < a → fmat D F₁ m a b = 0 := fun a b h => (hEm.1 a b).1 h
  have hMd : ∀ a, fmat D F₁ m a a = 1 := fun a => (hEm.1 a a).2 rfl
  cases hs : (Zd.M p).split with
  | none => exact modeL Zd p hs u u' _ _ _ _ hNU hNd hMU hMd hNb hMb hrel
  | some g =>
    refine modeG Zd p g hs u u' _ _ _ _ hNU hNd hMU hMd hNb hMb hrel ?_
    obtain ⟨sg, hsg, -, hq⟩ := typed_split Zd p hs
    have hgP := gS_mem_of_split p hsg
    have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := by
      have : gS D ≠ 0 := by
        unfold Lat.gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      exact_mod_cast this
    have hφ := fun a => Formalism.L2.SG.Pf.BBTie.bt_typed_frFac Zd (Formalism.L2.SG.Pf.locEqC_holds D Zd)
      (Formalism.L2.SG.Pf.locDiffC_holds D Zd) p F0 Λ hRL.2.1.1.fg hRL.2.2 hRL.2.1.2.2.2 hgP a
    have hκ := (Formalism.L2.SG.Pf.BBTie.bt_kappa Zd p sg hsg).1
    have hq0 : (sg.q : (D.s.atP p).Fp) ≠ 0 := by
      intro h
      exact sg.q_irr.ne_zero (Subtype.ext h)
    have hOO : (Zd.M p).L.O = (D.s.atP p).O := (Zd.agree p).2.2.2.1
    rw [locU_mul, locU_sub_one]
    intro i j
    rw [locU_apply]
    obtain ⟨w, hwO, hw⟩ := (hφ i).2
    have hinv : Ring.inverse (frFac Zd.δ p i) = w := by
      calc Ring.inverse (frFac Zd.δ p i) = (w * frFac Zd.δ p i) * Ring.inverse (frFac Zd.δ p i) := by
            rw [hw, one_mul]
        _ = w := by rw [mul_assoc, frFac_mul_inv, mul_one]
    induction i using Fin.lastCases with
    | last =>
      rw [nm_last Λ (lf D F0) F₁ n m hn hm j, map_zero, mul_zero, zero_mul]
      exact ⟨0, Subring.zero_mem _, by rw [mul_zero]⟩
    | cast d =>
      set x := (fmat D (lf D F0) n * fmat D F₁ m - 1) d.castSucc j with hxdef
      have hint : (D.s.atP p).ιE (x / (gS D : D.host.E)) ∈ (Zd.M p).L.O := by
        rw [hOO]
        exact iota_mem_O p _ (fun P hP => cong_at D Λ (lf D F0) F₁ F₂ n m hn hm hfr hRL.2.1.2.2.2 hP₁.2.2.1
          hA₁ hA₂ hP₁.1.1 P (hgP P hP) hg d j)
      have hx : (D.s.atP p).ιE x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) *
          ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
            (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)) * (D.s.atP p).ιE (x / (gS D : D.host.E))) := by
        rw [← mul_assoc, ← mul_assoc, ← map_mul (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), mul_inv_cancel₀ hq0,
          map_one, one_mul, ← map_mul, mul_div_cancel₀ x hg]
      refine ⟨w * ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
          (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)) * (D.s.atP p).ιE (x / (gS D : D.host.E))) * frFac Zd.δ p j,
        Subring.mul_mem _ (Subring.mul_mem _ hwO (Subring.mul_mem _ hκ hint)) (hφ j).1, ?_⟩
      rw [hinv, hx, hq]
      ring

end OneDir2

end Formalism.L2.SG.Pf.FibQ
end
end
end
