module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Formalism.WeaklyAdmissibleFiltrations.StatementTor
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasisStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasisStatement
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrobeniusPeriodStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLatticePeriodsOnDisc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedFCrystalOfStratifiedPhiModuleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleCrystallineLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatumStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyDiscPeriodAinfBasisDataOfIsPer

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeOfBasisMapsToBasis

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semiBC_of_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (ι : Type) (e : Module.Basis ι A M) (b : Module.Basis ι B N), (∀ i, b i = u (e i)) → SemiBC u := by
  intro A B _ _ f M _ _ N _ _ u ι e b hb Q _ _ v
  refine ⟨b.constr B (fun i => v (e i)), ?_, ?_⟩
  · intro x
    have h : (b.constr B (fun i => v (e i))).comp u = v := by
      refine e.ext fun i => ?_
      simp [LinearMap.comp_apply, ← hb, Module.Basis.constr_basis]
    exact LinearMap.congr_fun h x
  · intro w hw
    refine b.ext fun i => ?_
    rw [Module.Basis.constr_basis, hb, hw]

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeOfBasisMapsToBasisStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isSemilinearBaseChange_of_basis_maps_to_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (ι : Type) (e : Module.Basis ι A M) (b : Module.Basis ι B N), (∀ i, b i = u (e i)) → SemiBC u := by
  first | exact @GlobalTheory.BSP.semiBC_of_basis | exact GlobalTheory.BSP.semiBC_of_basis | (intros; apply GlobalTheory.BSP.semiBC_of_basis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationOfFramedMatrices

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EtReal

open Matrix

variable {l : ℕ} [hl : Fact l.Prime]

theorem equivFun_frob {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ_[l] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (b.baseChange (WCb l)).equivFun (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) =
      fun i => frobW l ((b.baseChange (WCb l)).equivFun y i) := by
  funext i
  simp only [Module.Basis.equivFun_apply]
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
      map_smul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), Finsupp.add_apply, Finsupp.add_apply, map_add (f := _), hy, hz]

theorem equivFun_map {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ_[l] T) (s : WCb l ≃ₐ[ℤ_[l]] WCb l) (r : T →ₗ[ℤ_[l]] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (b.baseChange (WCb l)).equivFun (TensorProduct.map s.toLinearMap r y) =
      (LinearMap.toMatrix b b r).map (algebraMap ℤ_[l] (WCb l)) *ᵥ
        fun k => s ((b.baseChange (WCb l)).equivFun y k) := by
  funext i
  simp only [Module.Basis.equivFun_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul, AlgEquiv.toLinearMap_apply,
      ← LinearMap.toMatrix_mulVec_repr b b r t]

    simp only [Module.Basis.baseChange_repr_tmul, Matrix.mulVec, dotProduct, map_smul, Algebra.smul_def,
    Finset.sum_mul, map_mul, mul_assoc, map_sum, AlgEquiv.commutes]
  | add y z hy hz =>
    simp only [map_add (f := _), Finsupp.add_apply, hy, hz, mul_add, Finset.sum_add_distrib]

theorem algEquiv_mulVec {R A : Type} [CommSemiring R] [CommRing A] [Algebra R A] {n : Type} [Fintype n]
    (s : A ≃ₐ[R] A) (U : Matrix n n A) (v : n → A) (i : n) :
    s ((U *ᵥ v) i) = (U.map s *ᵥ fun k => s (v k)) i :=
  RingHom.map_mulVec s.toRingEquiv.toRingHom U v i

theorem realises_of_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U → ∃ j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j := by
  intro l _ K bk d S M e hF T _ _ ρ b U hU
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) _ e
  let σ : (ainfObj K).A →+* WCb l := (inclW l).comp (ainfId K).toRingHom
  let cv : (Fin d → (ainfObj K).A) →ₛₗ[σ] (Fin d → WCb l) :=
    { toFun := fun v k => σ (v k)
      map_add' := fun v w => funext fun k => map_add σ (v k) (w k)
      map_smul' := fun a v => funext fun k => map_mul σ a (v k) }
  let j : M.M (ainfObj K) →ₛₗ[σ] (WCb l ⊗[ℤ_[l]] T) :=
    ((b.baseChange (WCb l)).equivFun.symm.toLinearMap ∘ₗ Matrix.toLin' U) ∘ₛₗ (cv ∘ₛₗ b₀.equivFun.toLinearMap)
  have hj : ∀ x, (b.baseChange (WCb l)).equivFun (j x) = U *ᵥ fun k => σ (b₀.equivFun x k) := fun x =>
    (b.baseChange (WCb l)).equivFun.apply_symm_apply _
  have hjs : ∀ c : Fin d → (ainfObj K).A, (b.baseChange (WCb l)).equivFun (j (b₀.equivFun.symm c)) = U *ᵥ fun k => σ (c k) := fun c => by
    rw [hj, LinearEquiv.apply_symm_apply]

  have hbc : SemiBC j := by
    letI := hU.unit.invertible
    let c := (Pi.basisFun (WCb l) (Fin d)).map ((Matrix.toLinearEquiv' U this).trans (b.baseChange (WCb l)).equivFun.symm)
    refine GlobalTheory.T.isSemilinearBaseChange_of_basis_maps_to_basis _ _ _ _ _ j (Fin d) b₀ c fun i => ?_
    apply (b.baseChange (WCb l)).equivFun.injective
    rw [hj]
    simp only [c, Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
    refine congrArg _ (funext fun k => ?_)
    rw [Module.Basis.equivFun_self]
    by_cases h : i = k
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  have hu : IsUnit (inclW l (bk.ev bk.E)) := isUnit_inclW_of_span bk.span_ev
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : ↥(ainfObj K).I, ((d₀ : (ainfObj K).A) : Ainf l) = bk.ev bk.E :=
    ⟨⟨bk.ι.f bk.E, bk.ι.f_I _ (Ideal.mem_span_singleton_self _)⟩, rfl⟩
  have hne : (d₀ : (ainfObj K).A) ≠ 0 := fun h => hu.ne_zero (by rw [← hd₀, h]; exact map_zero (inclW l))
  refine ⟨j, Realises.of_generator (isAinf_ainfObj K) hbc d₀ (by rw [hd₀]; exact bk.span_ev) ?_ ?_⟩
  · intro x m k hfr
    have hx : x = ∑ i, b₀.equivFun x i • M.tr bk.ι (e i) := by
      simp_rw [← hb₀]; exact (b₀.sum_equivFun x).symm
    rw [hx] at hfr
    obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ (ainfObj K) bk.ι d₀ (b₀.equivFun x) m k hfr
    haveI : IsDomain (ainfObj K).A := (ainfId K).toMulEquiv.isDomain
    haveI := Module.Free.of_basis b₀
    have h1 := sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ hne))
    simp_rw [← hb₀] at h1
    rw [← b₀.equivFun_symm_apply] at h1
    have h2 : σ (BK.hf bk.ι bk.E) ^ S.a • j m = σ (d₀ : (ainfObj K).A) ^ k •
        j (b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ fun i => (ainfObj K).D.φ (b₀.equivFun x i))) :=
      calc σ (BK.hf bk.ι bk.E) ^ S.a • j m = σ (BK.hf bk.ι bk.E ^ S.a) • j m := by rw [map_pow]
        _ = j (BK.hf bk.ι bk.E ^ S.a • m) := (j.map_smulₛₗ _ _).symm
        _ = j ((d₀ : (ainfObj K).A) ^ k • b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ
              fun i => (ainfObj K).D.φ (b₀.equivFun x i))) := congrArg j h1
        _ = σ ((d₀ : (ainfObj K).A) ^ k) • j (b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ
              fun i => (ainfObj K).D.φ (b₀.equivFun x i))) := j.map_smulₛₗ _ _
        _ = _ := congrArg (· • _) (map_pow σ _ _)
    suffices hs : σ (BK.hf bk.ι bk.E) ^ S.a • (σ (d₀ : (ainfObj K).A) ^ k •
        TensorProduct.map (frobW l).toLinearMap LinearMap.id (j x)) = σ (BK.hf bk.ι bk.E) ^ S.a • j m from
      (hu.pow S.a).smul_left_cancel.1 hs
    rw [h2]
    refine (smul_comm (σ (BK.hf bk.ι bk.E) ^ S.a) (σ (d₀ : (ainfObj K).A) ^ k) _).trans
      (congrArg (σ (d₀ : (ainfObj K).A) ^ k • ·) ?_)
    apply (b.baseChange (WCb l)).equivFun.injective
    have hz : (fun i => frobW l ((b.baseChange (WCb l)).equivFun (j x) i)) =
        U.map (frobW l) *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k)) := by
      rw [hj]
      funext i
      refine (RingHom.map_mulVec (frobW l).toRingHom U _ i).trans ?_
      exact congrArg (fun v => (U.map (frobW l) *ᵥ v) i) (funext fun k => frobW_inclW (b₀.equivFun x k))
    have hc : (fun k => σ (((S.A.map (BK.hf bk.ι)) *ᵥ fun i => (ainfObj K).D.φ (b₀.equivFun x i)) k)) =
        S.A.map bk.evW *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k)) := by
      funext k
      have hA : (S.A.map (BK.hf bk.ι)).map σ = S.A.map bk.evW := Matrix.ext fun _ _ => rfl
      exact (RingHom.map_mulVec σ _ _ k).trans
        (congrArg (fun A => (A *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k))) k) hA)
    have hσE : σ (BK.hf bk.ι bk.E) = bk.evW bk.E := rfl
    refine ((b.baseChange (WCb l)).equivFun.map_smul _ _).trans ?_
    refine Eq.trans ?_ (hjs _).symm
    refine (congrArg (σ (BK.hf bk.ι bk.E) ^ S.a • ·) ((equivFun_frob b (j x)).trans hz)).trans ?_
    refine Eq.trans ?_ (congrArg (U *ᵥ ·) hc).symm
    exact (congrArg (fun t => t ^ S.a • (U.map (frobW l) *ᵥ _)) hσE).trans
      ((Matrix.smul_mulVec _ _ _).symm.trans
        ((congrArg (· *ᵥ _) hU.φ).trans (Matrix.mulVec_mulVec _ _ _).symm))
  · intro g x
    let h := (isAinf_ainfObj K).galHom g
    have hk : ∀ k, M.tr h (b₀ k) = ∑ i, S.ε bk.ι (h.comp bk.ι) i k • b₀ i := fun k =>
      (congrArg (M.tr h) (hb₀ k)).trans ((M.tr_comp h bk.ι (e k)).symm.trans
        ((hF.tr bk.ι (h.comp bk.ι) k).trans (Finset.sum_congr rfl fun i _ => congrArg _ (hb₀ i).symm)))
    have htr : M.tr h x = b₀.equivFun.symm ((S.ε bk.ι (h.comp bk.ι)) *ᵥ fun k => h.f (b₀.equivFun x k)) :=
      calc M.tr h x = M.tr h (∑ k, b₀.equivFun x k • b₀ k) := congrArg (M.tr h) (b₀.sum_equivFun x).symm
        _ = ∑ k, h.f (b₀.equivFun x k) • M.tr h (b₀ k) :=
          (map_sum (M.tr h) _ _).trans (Finset.sum_congr rfl fun k _ => (M.tr h).map_smulₛₗ _ _)
        _ = ∑ k, ∑ i, (h.f (b₀.equivFun x k) * S.ε bk.ι (h.comp bk.ι) i k) • b₀ i :=
          Finset.sum_congr rfl fun k _ => (congrArg _ (hk k)).trans
            (Finset.smul_sum.trans (Finset.sum_congr rfl fun i _ => smul_smul _ _ _))
        _ = ∑ i, (∑ k, S.ε bk.ι (h.comp bk.ι) i k * h.f (b₀.equivFun x k)) • b₀ i :=
          Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ =>
            (Finset.sum_congr rfl fun k _ => congrArg (· • b₀ i) (mul_comm _ _)).trans Finset.sum_smul.symm)
        _ = _ := (b₀.equivFun_symm_apply _).symm
    apply (b.baseChange (WCb l)).equivFun.injective
    have hσ : ∀ a : (ainfObj K).A, σ a = inclW l a := fun a => rfl
    have hh : ∀ a : (ainfObj K).A, h.f a = Per.σA (g : GQ l) a := fun a => rfl
    have hL : (fun k => σ (((S.ε bk.ι (h.comp bk.ι)) *ᵥ fun k => h.f (b₀.equivFun x k)) k)) =
        (S.ε bk.ι (h.comp bk.ι)).map σ *ᵥ fun k => σ (h.f (b₀.equivFun x k)) :=
      funext fun k => RingHom.map_mulVec σ _ _ k
    have hR : (fun k => galW l (g : GQ l) ((b.baseChange (WCb l)).equivFun (j x) k)) =
        U.map (galW l (g : GQ l)) *ᵥ fun k => σ (h.f (b₀.equivFun x k)) :=
      funext fun i => by
        have h1 := congrArg (fun v : Fin d → WCb l => galW l (g : GQ l) (v i)) (hj x)
        have h2 := algEquiv_mulVec (galW l (g : GQ l)) U (fun k => σ (b₀.equivFun x k)) i
        have h3 : (fun k => galW l (g : GQ l) (σ (b₀.equivFun x k))) = fun k => σ (h.f (b₀.equivFun x k)) :=
          funext fun k => (congrArg (galW l (g : GQ l)) (hσ _)).trans ((galW_inclW (g : GQ l) (b₀.equivFun x k)).trans
            ((hσ _).symm.trans (congrArg σ (hh _).symm)))
        beta_reduce at h1 ⊢
        exact h1.trans (h2.trans (congrArg (fun v => (U.map (galW l (g : GQ l)) *ᵥ v) i) h3))
    have hg := hU.gal g
    refine ((congrArg (fun z => (b.baseChange (WCb l)).equivFun (j z)) htr).trans (hjs _)).trans ?_
    refine Eq.trans ?_ (equivFun_map b _ _ _).symm
    refine (congrArg (U *ᵥ ·) hL).trans (Eq.trans ?_ (congrArg (_ *ᵥ ·) hR).symm)
    exact (Matrix.mulVec_mulVec _ _ _).trans ((congrArg (· *ᵥ _) hg.symm).trans (Matrix.mulVec_mulVec _ _ _).symm)

end GlobalTheory.BSP.EtReal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationOfFramedMatricesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.etaleRealisation_of_framedMatrices : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U → ∃ j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j := by
  first | exact @GlobalTheory.BSP.EtReal.realises_of_mreal | exact GlobalTheory.BSP.EtReal.realises_of_mreal | (intros; apply GlobalTheory.BSP.EtReal.realises_of_mreal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLatticePeriodsOnDiscStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_crystalline_lattice_periods_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), Nonempty (Seed bk d (fun g => LinearMap.toMatrix b b (actT L g)) τ) := by
  first | exact @GlobalTheory.SeedExists.exists_seed | exact GlobalTheory.SeedExists.exists_seed | (intros; apply GlobalTheory.SeedExists.exists_seed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyDiscPeriodAinfBasisDataOfIsPerStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.nonempty_discPeriodAinfBasisData_of_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ s : Seed bk d ρ τ, Nonempty (Height s) := by
  first | exact @GlobalTheory.BSP.HeightEx.nonempty_height | exact GlobalTheory.BSP.HeightEx.nonempty_height | (intros; apply GlobalTheory.BSP.HeightEx.nonempty_height <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticePrismaticFCrystalPerfectPrism

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem galoisLatticeAction_mul {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) (g h : ↥(GK K)) :
    actT L g ∘ₗ actT L h = actT L (g * h) := by
  ext x
  simp [actT, map_mul]
  rfl

theorem galoisLatticeAction_one {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) :
    actT L 1 = LinearMap.id := by
  ext x
  simp [actT, map_one]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem isUnit_toMatrix_actT {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] ↥L.T) (g : ↥(GK K)) :
    IsUnit (LinearMap.toMatrix b b (actT L g)) := by
  have h1 : LinearMap.toMatrix b b (actT L g) * LinearMap.toMatrix b b (actT L g⁻¹) = 1 := by
    rw [← LinearMap.toMatrix_comp, galoisLatticeAction_mul, mul_inv_cancel, galoisLatticeAction_one, LinearMap.toMatrix_id]
  have h2 : LinearMap.toMatrix b b (actT L g⁻¹) * LinearMap.toMatrix b b (actT L g) = 1 := by
    rw [← LinearMap.toMatrix_comp, galoisLatticeAction_mul, inv_mul_cancel, galoisLatticeAction_one, LinearMap.toMatrix_id]
  exact ⟨⟨_, _, h1, h2⟩, rfl⟩

theorem clause1_perfectPrism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∃ (M : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] ↥L.T)), Realises K M (ainfObj K) (ainfId K) ↥L.T (fun g => actT L g) j := by
  intro l _ K P AI hStd V _ _ _ _ _ _ _ ρ L hcont hcrys
  haveI : Module.Free ℤ_[l] ↥L.T := L.free
  haveI : Module.Finite ℤ_[l] ↥L.T := Module.Finite.iff_fg.mpr L.fg
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_breuilKisin_frobenius_period l K bk
  let b := Module.finBasis ℤ_[l] ↥L.T
  obtain ⟨s⟩ := GlobalTheory.T.exists_crystalline_lattice_periods_on_disc l K bk τ hτ P AI hStd V ρ L hcont hcrys _ b
  have hu : ∀ g, IsUnit (LinearMap.toMatrix b b (actT L g)) := fun g => isUnit_toMatrix_actT L b g
  obtain ⟨hs⟩ := GlobalTheory.T.nonempty_discPeriodAinfBasisData_of_isPer l K bk τ hτ _ _ hu s
  obtain ⟨S, T, hST⟩ := GlobalTheory.T.exists_stratified_phiModule_crystalline_lattice l K bk τ hτ _ _ hu s hs
  obtain ⟨M, e, hMe⟩ := GlobalTheory.T.exists_framed_fCrystal_of_stratifiedPhiModule l K bk _ S
  exact ⟨M, GlobalTheory.T.etaleRealisation_of_framedMatrices l K bk _ S M e hMe ↥L.T (fun g => actT L g) b T hST⟩

end GlobalTheory.BSP
end
end
