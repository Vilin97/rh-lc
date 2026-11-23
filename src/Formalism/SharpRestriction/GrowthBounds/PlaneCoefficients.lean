module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.WordLossNonneg
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.WBound
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RestOneOpOf
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.DoubleMonomialApply
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.XXgZeroP
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.FrMemLetters
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDd
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosTLSurj
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundJoint
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundReal
import Mathlib.Tactic.Linter.Style
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RenameMemSupported
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.CompDEqHomComp
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ValSCongrSupp
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffOneTTens
import Mathlib.Tactic.TypeStar
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.FortyEightBoundArith
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ProdRangeZmod
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.SupportedOfSupport
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RestPlOf
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.MemTSetIff
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.MultidegSingle
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport
public import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.GeZSum
public import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.Lam1SPderivAndXMulLeAddIndicator

-- Source module: Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.WithThModelLet

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def withTh {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m) :
    SignedChainData p O r J :=
  SignedChainData.mk Dt.nL Dt.sgn Dt.d Dt.gP Dt.nch Dt.chain Dt.chain_mono Dt.chain_w th Dt.sl thL h Dt.ga Dt.ga_unit Dt.ga_dig
    Dt.c Dt.one_le_c

section With

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m)

theorem withTh_modelLet : (withTh Dt th thL h).modelLet = Dt.modelLet := by
  unfold SignedChainData.modelLet withTh
  congr 1
  funext x
  cases x <;> rfl

theorem withTh_trueLet : (withTh Dt th thL h).trueLet = Dt.trueLet := by
  unfold SignedChainData.trueLet withTh
  congr 1
  funext x
  obtain ⟨j, l | m⟩ := x <;> rfl

theorem withTh_levToML (j) : (withTh Dt th thL h).levToML j = Dt.levToML j := by
  funext x
  cases x <;> rfl

theorem withTh_chainML (j i) : (withTh Dt th thL h).chainML j i = Dt.chainML j i := by
  unfold SignedChainData.chainML
  rw [withTh_levToML]
  rfl

theorem withTh_TSet (j i) : (withTh Dt th thL h).TSet j i = Dt.TSet j i := rfl

theorem withTh_digOK (rho) : (withTh Dt th thL h).digOK rho = Dt.digOK rho := rfl

theorem withTh_liftVar : (withTh Dt th thL h).liftVar = Dt.liftVar := by
  funext x
  obtain ⟨⟨j, l | m⟩, a⟩ := x <;> rfl

theorem withTh_liftExp : (withTh Dt th thL h).liftExp = Dt.liftExp := by
  funext mo x
  obtain ⟨⟨j, l | m⟩, a⟩ := x <;> rfl

theorem withTh_Fdig (rho F) : (withTh Dt th thL h).Fdig rho F = Dt.Fdig rho F := by
  simp only [SignedChainData.Fdig, withTh_digOK, withTh_liftVar, withTh_liftExp]
  rfl

theorem withTh_normE (K : ℕ) [NeZero K] [NeZero J] : normE p K (withTh Dt th thL h) = normE p K Dt := by
  unfold normE
  rw [withTh_trueLet]
  rfl

theorem XX_withTh [NeZero J] [NeZero r] (hth : ∀ j i, Dt.th j i ≤ th j i)
    (hthL : ∀ j (m : Fin r), m.val + 2 ≤ r → Dt.thL j m ≤ thL j m)
    (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) (hF : (withTh Dt th thL h).XX F) : Dt.XX F := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨h1, fun rho j i => ?_, fun j m hm => ?_⟩
  · have hx := h2 rho j i
    erw [withTh_modelLet, withTh_chainML, withTh_Fdig] at hx
    exact geZ_anti (hth j i) hx
  · have hx := h3 j m hm
    erw [withTh_trueLet, withTh_TSet] at hx
    exact geZ_anti (hthL j m hm) hx

end With

theorem restLeOfG : RestLeOfG := by
  intro sc sL p n' r K m _ _ _ O _ _ _ hk Fr deg Y N₁ G' cP F hG J _ Dt dPl dNo ka hT rho e he nu
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hT
  let th : ∀ j, Fin (Dt.nch j) → ℝ := fun j i =>
    thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j (i : ℕ) -
      sc * slU Fr p deg Y (r + K) Dt.nL j (i : ℕ)
  let thL : ZMod J → Fin r → ℝ := fun j mm =>
    thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j (Dt.nL j + (r - 1 - (mm : ℕ))) -
      sL * slU Fr p deg Y (r + K) Dt.nL j (Dt.nL j + (r - 1 - (mm : ℕ)))
  have hpos : ∀ j (mm : Fin r), mm.val + 2 ≤ r → 0 < thL j mm := by
    intro j mm hmm
    have a := Dt.thL_pos j mm hmm
    have b := t9 j mm hmm
    simp only [sub_zero] at b
    exact lt_of_lt_of_le a b
  have hT' : TwistedSubstitutionGrowthBound Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL
      (withTh Dt th thL hpos) dPl ka :=
    ⟨t1, t2, t3, t4, t5, t6, t7, fun j i => rfl, fun j mm _ => rfl⟩
  have hX := hG J (withTh Dt th thL hpos) dPl dNo ka hT' rho e (by rw [withTh_normE]; exact he) nu
  refine XX_withTh Dt th thL hpos (fun j i => ?_) (fun j mm hmm => ?_) _ hX
  · have b := t8 j i
    simp only [sub_zero] at b
    exact b
  · have b := t9 j mm hmm
    simp only [sub_zero] at b
    exact b

end Formalism.MainNotions.PairMembershipBlocks
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.GeoTouch

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics

theorem geoTop : GeoTop := by
  intro n' r _ _ Fr L₁ N₁ hV J _ nL hJ hnL s hs
  have hr : 1 ≤ r := NeZero.pos r
  obtain ⟨x0, hx0⟩ := posTL_surj Fr hV hr hJ hnL s hs
  refine ⟨x0, hx0, fun x' hx' => ?_⟩
  exact posTL_inj Fr hV hr hJ hnL (hx'.trans hx0.symm)

theorem geoTouch : GeoTouch := by
  intro n' r _ _ Fr L₁ N₁ hV J _ nL hJ hnL x0 j u hu hx
  have hr : 1 ≤ r := NeZero.pos r
  have hu' : u < (Fr.LLset (segZ j)).card + r := by rw [← hnL]; exact hu
  unfold touchT
  rcases hx with (⟨l, hl, hlt⟩ | ⟨m, hm, hlt⟩) | ⟨m, hm⟩
  · subst hl
    have hl' : l.val < (Fr.LLset (segZ j)).card := by rw [← hnL]; exact l.isLt
    refine ⟨llPos Fr (segZ j) l.val, (LL_sub_letters hV hr _ _ (llPos_mem Fr (segZ j) l.val hl')).1, rfl, ?_⟩
    rw [← posU_ll (Fr := Fr) (segZ j) l.val hl']
    exact (posU_le_iff hV (segZ j) _ _ (by omega) hu').2 (by omega)
  · subst hm
    have hm' := m.isLt
    refine ⟨Fr.fr (segZ j) (r - 1 - m.val), fr_mem_letters hV hr _ _ (by omega), rfl, ?_⟩
    rw [← posU_fr (Fr := Fr) (segZ j) (r - 1 - m.val)]
    refine (posU_le_iff hV (segZ j) _ _ (by omega) hu').2 ?_
    rw [← hnL]
    omega
  · subst hm
    have hm' := m.isLt
    obtain ⟨s, hs, hsh⟩ := DdG.shift Fr hV.2.1 hJ (j - 1)
    rw [sub_add_cancel] at hsh
    refine ⟨Fr.fr (segZ j - 1) (r - 1 - m.val), w_mem_letters hV hr _ _ (by omega), ?_,
      (w_lt_posU hV hr _ _ _ (by omega) hu').le⟩
    show _ = posOf n' (Fr.fr (segZ (j - 1)) (r - 1 - m.val))
    rw [(hsh (r - 1 - m.val)).1]
    rcases hs with rfl | rfl
    · rw [add_zero]
    · rw [DdG.posOf_add_n]

end Formalism.MainNotions.PairMembershipBlocks
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PmatDetMem

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem det_mem_sub {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {r : ℕ}
    (M : Matrix (Fin r) (Fin r) A) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun i _ => h _ _) _

theorem X_mem_supp {R σ : Type*} [CommRing R] (s : Set σ) (i : σ) (hi : i ∈ s) :
    (X i : MvPolynomial σ R) ∈ supported R s := by
  rw [supported_eq_adjoin_X]
  exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hi)

theorem pmat_det_mem (R : Type) [CommRing R] {n' r k : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n') (P : Fin r → ℕ)
    (hA : ∀ l, Even (A l).val) :
    (pmat R hrk A P).det ∈ supported R {v : TV n' k | v.2.val < r ∧ Even v.1.val} := by
  apply det_mem_sub
  intro l i
  unfold pmat
  rw [Matrix.of_apply]
  exact Subalgebra.pow_mem _ (X_mem_supp {v : TV n' k | v.2.val < r ∧ Even v.1.val} (A l, Fin.castLE hrk i)
    (show (Fin.castLE hrk i).val < r ∧ Even (A l).val from ⟨i.isLt, hA l⟩)) _

theorem restSP : RestSP := by
  intro p n' r k _ R _ F hrk c' Q L₁ N₁ hV hn hr ga hga v hv
  have hfr : ∀ (j : ℤ) (l : Fin r), Even (posOf n' (F.fr j l.val)).val := fun j l =>
    (posOf_even hn _).2 (hV.2.2.2.2.1 j l.val l.isLt).2
  have hAr : ∀ (s : ℤ) (l : Fin r), Even (posOf n' (Arow F s l.val)).val := fun s l =>
    (posOf_even hn _).2 (window_holds_even_tops n' r F L₁ N₁ hV hn hr s l.val l.isLt).1
  have hmem : SPR R p F hrk c' Q ∈ supported R {v : TV n' k | v.2.val < r ∧ Even v.1.val} := by
    unfold SPR
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _)
      (Subalgebra.prod_mem _ fun j _ => ?_)) (Subalgebra.prod_mem _ fun s _ => ?_)
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hfr j)) _
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hfr j)) _
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hAr _)) _
  have hvars : v ∈ (SPR R p F hrk c' Q).vars :=
    (mem_vars_iff_mem_support v).2 ⟨ga, hga, Finsupp.mem_support_iff.2 hv⟩
  exact (mem_supported.1 hmem) (Finset.mem_coe.2 hvars)

end Formalism.MainNotions.PairMembershipBlocks
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.SumFiberMultideg

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G3

theorem sum_fiber_multideg {r : ℕ} (μ : ℤ × Fin r →₀ ℕ) (y : ℤ) :
    ∑ v ∈ μ.support, (if v.1 = y then μ v else 0) = multideg μ y := by
  unfold multideg
  rw [← Finset.sum_filter]
  have h1 : ∑ c : Fin r, μ (y, c) = ∑ v ∈ (Finset.univ.image fun c : Fin r => (y, c)), μ v := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact (Prod.mk.inj h).2
  rw [h1]
  apply Finset.sum_subset
  · intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_image]
    exact ⟨v.2, Finset.mem_univ _, by rw [← hv.2]⟩
  · intro v hv hnot
    rw [Finset.mem_image] at hv
    obtain ⟨c, -, rfl⟩ := hv
    by_contra h
    exact hnot (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 h, rfl⟩)

theorem lkW {n' r : ℕ} (Fr : Frames n' r) (jz : ℤ) (μ : ℤ × Fin r →₀ ℕ) :
    wDeg (wSet Fr jz) μ ≤ ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val)) := by
  unfold wDeg
  calc ∑ v ∈ μ.support, (if v.1 ∈ wSet Fr jz then μ v else 0)
      ≤ ∑ v ∈ μ.support, ∑ m' : Fin r, (if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0) := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs with h
        · obtain ⟨m, hm⟩ := h
          calc μ v = (if v.1 = Fr.fr (jz - 1) (r - 1 - m.val) then μ v else 0) := by rw [if_pos hm]
            _ ≤ _ := Finset.single_le_sum
              (f := fun m' : Fin r => if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
        · exact Nat.zero_le _
    _ = ∑ m' : Fin r, ∑ v ∈ μ.support, (if v.1 = Fr.fr (jz - 1) (r - 1 - m'.val) then μ v else 0) := Finset.sum_comm
    _ = ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val)) :=
        Finset.sum_congr rfl fun m' _ => sum_fiber_multideg μ _

end Formalism.MainNotions.PairMembershipBlocks
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem opSteps_of (h : NoOpStep) : OpSteps :=
  ⟨trDerPl, trDerNo, trMulPl, trMulNo, plDer, plEul, plMul, h, geoTop, geoTouch⟩

theorem restWord_of_steps (h : OpSteps) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestWord D CLa Ck Crk Cdeg :=
  restWord_of D CLa Ck Crk Cdeg restLeOfG (restOneOp_of h D CLa Ck Crk Cdeg) (restWordBound D CLa Ck Crk Cdeg)

theorem restMEM_of_last (hNO : NoOpStep) (hPl : RestPl)
    (hAr : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ, RestArithStep C CLa)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestMEM D CLa Ck Crk Cdeg :=
  memCondition_of_theoremII D CLa Ck Crk Cdeg
    (lemma5a_of_monomial D CLa Ck Crk Cdeg
      (rest5aMono_of_cut restT (restN D) restTh hPl restSP hAr D CLa Ck Crk Cdeg))
    (restWord_of_steps (opSteps_of hNO) D CLa Ck Crk Cdeg)

theorem stmtE_of_last (D : Formalism.BasicNotions.D7) (hNO : NoOpStep) (hPl : RestPl)
    (hAr : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ, RestArithStep C CLa) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  Formalism.MainNotions.Proposition5Numerics.stmtE_of_mem D (fun CLa Ck Crk Cdeg => restMEM_of_last hNO hPl hAr D CLa Ck Crk Cdeg)

theorem stmtE_of_pl (D : Formalism.BasicNotions.D7) (hPl : RestPl) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_last D Formalism.MainNotions.LetterSubstitution.noOpStep hPl ⟨1, one_pos, fun C hC CLa => arithCondition_of_one_le C CLa hC⟩

theorem level_link_of_degree_letters (hLL : LinkL) (hDg : LkDeg) (hVr : LkVars) : RestLink :=
  restLink_of Formalism.MainNotions.LetterSubstitution.valNN Formalism.MainNotions.LetterSubstitution.homDec hLL hDg hVr restTr (fun Fr jz μ => lkW Fr jz μ)

private theorem restPl_of_restChain_of_restLink (hC : RestChain) (hL : RestLink) : RestPl := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr L₁ N₁ hV hE J _ Dt hT hJ A hA l hl ga hg t ht dPl
  exact ⟨hC p n' r K m O hk Fr L₁ N₁ hV hE J Dt hT hJ A hA l hl ga hg t ht dPl,
    hL p n' r K m O hk Fr L₁ N₁ hV hE J Dt hT hJ A hA l hl ga hg t ht dPl⟩

theorem restLink : RestLink := level_link_of_degree_letters linkL lkDeg lkVars

theorem stmtE_of_chain (D : Formalism.BasicNotions.D7) (hC : RestChain) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_pl D (restPl_of_restChain_of_restLink hC restLink)

end Formalism.MainNotions.PairMembershipBlocks
end
end
end
