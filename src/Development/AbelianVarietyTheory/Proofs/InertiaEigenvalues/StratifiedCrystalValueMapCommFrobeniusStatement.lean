module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisorStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasisStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCoverStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedCrystalFrobeniusCoordinates

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem coord_of_frac_rel {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {d : ℕ}
    (b : Module.Basis (Fin d) A N) (b' : Fin d → N) (hb : ∀ i, b i = b' i) (T c : A) (v w : Fin d → A) (n : N) (r s j k : ℕ)
    (h1 : (T * T) ^ r • (T ^ j • ∑ i, v i • b' i - T ^ k • n) = 0)
    (h2 : T ^ s • (c • n - T ^ j • ∑ i, w i • b' i) = 0) :
    T ^ (r + r + s + j) • (c • v - T ^ k • w) = 0 := by
  obtain rfl : ⇑b = b' := funext hb
  apply b.equivFun.symm.injective
  rw [map_zero, map_smul, map_sub, map_smul, map_smul, Module.Basis.equivFun_symm_apply,
    Module.Basis.equivFun_symm_apply]
  generalize ∑ i, v i • b i = V at *
  generalize ∑ i, w i • b i = W at *
  linear_combination (norm := module) (T ^ s * c) • h1 + (T ^ (r + r + k)) • h2

theorem coord_frobenius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)), IsCoord e V → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ r : ℕ, a.f t ^ r • (BK.hf g bk.E ^ S.a • V.v a g m - a.f t ^ k • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) = 0 := by
  intro l _ K bk d S M e hF B V hV t x m k h Q a g
  refine (exists_isFrac (a.f t) (M.Φ Q ⟨a.f t, a.f_I _ t.2⟩ (M.tr a x))).elim fun n hn => hn.elim fun j hn => ?_
  refine (M.Φ_nat a t ⟨a.f t, a.f_I _ t.2⟩ x m k n j h hn).elim fun r hr => ?_
  refine (GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ Q g ⟨a.f t, a.f_I _ t.2⟩ (V.v a g x) n j
    ((congrArg (M.Φ Q ⟨a.f t, a.f_I _ t.2⟩) (hV a g x)).symm.trans hn)).elim fun s hs => ?_
  refine (GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ g.f _ _ (M.tr g) (M.tr_bc g) _ e).elim fun b hb => ?_
  exact ⟨r + r + s + j, coord_of_frac_rel b (fun i => M.tr g (e i)) hb (a.f t) (BK.hf g bk.E ^ S.a)
    (V.v a g m) ((S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) n r s j k
    ((congrArg (fun z => (a.f t * a.f t) ^ r • (a.f t ^ j • z - a.f t ^ k • n)) (hV a g m)).symm.trans hr) hs⟩

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedCrystalFrobeniusCoordinatesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.framedCrystal_frobenius_coordinates : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)), IsCoord e V → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ r : ℕ, a.f t ^ r • (BK.hf g bk.E ^ S.a • V.v a g m - a.f t ^ k • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) = 0 := by
  first | exact @GlobalTheory.BSP.coord_frobenius | exact GlobalTheory.BSP.coord_frobenius | (intros; apply GlobalTheory.BSP.coord_frobenius <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCrystalValueMapCommFrobenius

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem frob_coord_compat {C : Type} [CommRing C] {d d' : ℕ} (φ : C →+* C) (E T : C) (hE : E ∈ nonZeroDivisors C)
    (A : Matrix (Fin d) (Fin d) C) (A' : Matrix (Fin d') (Fin d') C) (Y : Matrix (Fin d') (Fin d) C)
    (a a' r r' k j : ℕ) (hY : E ^ a • (A' * Y.map φ) = E ^ a' • (Y * A)) (u m : Fin d → C) (n : Fin d' → C)
    (h1 : T ^ r • (E ^ a • m - T ^ k • A.mulVec fun i => φ (u i)) = 0)
    (h2 : T ^ r' • (E ^ a' • n - T ^ j • A'.mulVec fun i => φ (Y.mulVec u i)) = 0) :
    T ^ (r + r') • (T ^ k • n) = T ^ (r + r') • (T ^ j • Y.mulVec m) := by
  have e1 : (fun i => φ (Y.mulVec u i)) = (Y.map φ).mulVec fun i => φ (u i) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  rw [e1, Matrix.mulVec_mulVec] at h2
  have h3 := congrArg Y.mulVec h1
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mulVec_zero] at h3
  have h4 := congrArg (fun Z => Matrix.mulVec Z fun i => φ (u i)) hY
  simp only [Matrix.smul_mulVec] at h4
  funext i
  have h2i := congrFun h2 i
  have h3i := congrFun h3 i
  have h4i := congrFun h4 i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h2i h3i h4i ⊢
  rw [← sub_eq_zero]
  refine (mem_nonZeroDivisors_iff.1 (pow_mem hE (a + a'))).1 _ ?_
  linear_combination (T ^ r * T ^ k * E ^ a) * h2i - (T ^ r' * T ^ j * E ^ a') * h3i +
    T ^ (r + r' + k + j) * h4i

theorem eval_map_Φ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (M' : FCrys l ↥(OL K)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)), Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)) (V' : Eval S' B (M'.M B)), IsCoord e V → IsCoord e' V' → ∀ w : M.M B →ₗ[B.A] M'.M B, (∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x)) → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → IsFrac (t : B.A) (M'.Φ B t (w x)) (w m) k := by
  intro l _ K bk d d' S S' M e M' e' hF hF' Y hY B V V' hV hV' w hw t x m k hx
  refine (GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B).elim fun C hC => hC.elim fun h hC => hC.1.elim fun g => ?_
  have hc := hC.2
  have hinj := (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' B C (M'.M B) V' h g hc).1
  have hE := (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C g).2
  have hnj : ∃ n j, IsFrac (t : B.A) (M'.Φ B t (w x)) n j := by
    induction M'.Φ B t (w x) using LocalizedModule.induction_on with
    | h n s =>
      obtain ⟨_, j, rfl⟩ := s
      exact ⟨n, j, rfl⟩
  refine hnj.elim fun n hn => hn.elim fun j hn => ?_
  refine (GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d S M e hF B V hV t x m k hx C h g).elim fun r h1 => ?_
  refine (GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d' S' M' e' hF' B V' hV' t (w x) n j hn C h g).elim fun r' h2 => ?_
  rw [hw] at h2
  have hY' : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf g) * (Y.map (BK.hf g)).map C.D.φ) =
      BK.hf g bk.E ^ S'.a • (Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
    have e1 : (Y.map (BK.hf g)).map C.D.φ = (Y.map (frobS l bk.a)).map (BK.hf g) := by
      ext i j
      exact (g.f_φ (Y i j)).symm
    rw [e1, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    have h5 := congrArg (BK.hf g) (congrFun (congrFun hY.φ i) j)
    simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.map_apply] using h5
  have key := frob_coord_compat C.D.φ _ _ hE _ _ _ _ _ _ _ _ _ hY' _ _ _ h1 h2
  unfold IsFrac at hn ⊢
  rw [hn, LocalizedModule.mk_eq]
  refine ⟨⟨(t : B.A) ^ (r + r'), r + r', rfl⟩, hinj ?_⟩
  simp only [Submonoid.smul_def, LinearMap.map_smulₛₗ, map_pow, hw]
  exact key

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCrystalValueMapCommFrobeniusStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.stratifiedCrystalValueMap_comm_frobenius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (M' : FCrys l ↥(OL K)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)), Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)) (V' : Eval S' B (M'.M B)), IsCoord e V → IsCoord e' V' → ∀ w : M.M B →ₗ[B.A] M'.M B, (∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x)) → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → IsFrac (t : B.A) (M'.Φ B t (w x)) (w m) k := by
  first | exact @GlobalTheory.BSP.eval_map_Φ | exact GlobalTheory.BSP.eval_map_Φ | (intros; apply GlobalTheory.BSP.eval_map_Φ <;> assumption)
end
end
