module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantLatticeMatrixOverBreuilKisinStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfStratifiedPhiModuleHomStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedStratifiedCrystalBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStratifiedPhiModuleHomOfGaloisEquivariantStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatumStatement
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedMatricesOfEtaleRealisation

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem repr_map_baseChange {l : ℕ} [Fact l.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] T) (s : WCb l →ₗ[ℤ_[l]] WCb l) (r : T →ₗ[ℤ_[l]] T)
    (y : WCb l ⊗[ℤ_[l]] T) (i : Fin d) :
    (b.baseChange (WCb l)).repr (TensorProduct.map s r y) i =
      ∑ n, algebraMap ℤ_[l] (WCb l) (LinearMap.toMatrix b b r i n) * s ((b.baseChange (WCb l)).repr y n) := by
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul,
      ← congrFun (LinearMap.toMatrix_mulVec_repr b b r t) i, Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Module.Basis.baseChange_repr_tmul, map_smul, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
  | add y z hy hz =>
    rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, hy, hz, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [map_add (f := _), Finsupp.add_apply, mul_add]

end GlobalTheory.BSP

namespace GlobalTheory.BSP



theorem exists_mReal_of_realises : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K M (ainfObj K) (ainfId K) T ρ j → ∃ (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U ∧ ∀ k, j (M.tr bk.ι (e k)) = ∑ i, U i k ⊗ₜ[ℤ_[l]] b i := by
  intro l _ K bk d S M e hF T _ _ ρ j H
  have hfin := H.finite
  have hfree := H.free
  obtain ⟨e', he'⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) (Fin d) e
  obtain ⟨c, hc⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ j H.bc (Fin d) e'
  have hrank : Module.finrank ℤ_[l] T = d := by
    rw [← Module.finrank_baseChange (R := WCb l), Module.finrank_eq_card_basis c, Fintype.card_fin]
  let b := Module.finBasisOfFinrankEq ℤ_[l] T hrank
  let U : Matrix (Fin d) (Fin d) (WCb l) := (b.baseChange (WCb l)).toMatrix c
  have hck : ∀ k, c k = ∑ i, U i k • (b.baseChange (WCb l)) i := fun k => ((b.baseChange (WCb l)).sum_repr (c k)).symm
  have hcj : ∀ k, c k = j (M.tr bk.ι (e k)) := fun k => by rw [hc, he']
  refine ⟨b, U, ⟨?_, ?_, ?_⟩, fun k => ?_⟩
  · letI := (b.baseChange (WCb l)).invertibleToMatrix c
    exact isUnit_of_invertible _
  · have hu : IsUnit (inclW l (bk.ev bk.E)) := isUnit_inclW_of_span bk.span_ev
    let t : ↥(ainfObj K).I := ⟨bk.ι.f bk.E, bk.ι.f_I _ (Ideal.mem_span_singleton_self _)⟩
    have hu' : IsUnit (((inclW l).comp (ainfId K).toRingHom) (t : (ainfObj K).A)) := hu
    have ht0 : (t : (ainfObj K).A) ≠ 0 := fun h => hu'.ne_zero (by rw [h, map_zero])
    have key : ∀ k, inclW l (bk.ev bk.E) ^ S.a • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c k) =
        ∑ i, bk.evW (S.A i k) • c i := by
      intro k
      have hsum : ∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j') = M.tr bk.ι (e k) := by
        simp [Pi.single_apply]
      obtain ⟨m, s, hm⟩ := exists_isFrac (t : (ainfObj K).A)
        (M.Φ (ainfObj K) t (∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j')))
      obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ (ainfObj K) bk.ι t _ m s hm
      replace hm : IsFrac (t : (ainfObj K).A) (M.Φ (ainfObj K) t (M.tr bk.ι (e k))) m s := by
        simpa only [hsum] using hm
      have hj : inclW l (bk.ev bk.E) ^ s • TensorProduct.map (frobW l).toLinearMap LinearMap.id
          (j (M.tr bk.ι (e k))) = j m := H.j_φ t ht0 _ m s hm
      have hφ1 : (fun j' => (ainfObj K).D.φ ((Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j')) =
          (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) :=
        funext fun j' => by
          by_cases h : j' = k
          · subst h; simp
          · simp [Pi.single_apply, h]
      rw [hφ1] at hr
      have hr3 := (j.map_smulₛₗ ((t : (ainfObj K).A) ^ r) _).symm.trans ((congrArg j hr).trans j.map_zero)
      have hur : IsUnit (((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ r)) := by
        rw [map_pow]; exact hu'.pow r
      have hr5 := sub_eq_zero.1 ((j.map_sub _ _).symm.trans (hur.smul_eq_zero.1 hr3))
      have hr7 := (j.map_smulₛₗ _ _).symm.trans (hr5.trans (j.map_smulₛₗ _ _))
      have e1 : ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) = inclW l (bk.ev bk.E) ^ S.a :=
        map_pow _ _ _
      have e2 : ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) = inclW l (bk.ev bk.E) ^ s :=
        map_pow _ _ _
      have hsum2 : j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) =
          ∑ i, bk.evW (S.A i k) • c i := by

        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.map_smulₛₗ, ← hcj, Matrix.mulVec_single_one]
        rfl
      apply (hu.pow s).smul_left_cancel.1
      calc inclW l (bk.ev bk.E) ^ s • (inclW l (bk.ev bk.E) ^ S.a •
              TensorProduct.map (frobW l).toLinearMap LinearMap.id (c k))
          = inclW l (bk.ev bk.E) ^ S.a • (inclW l (bk.ev bk.E) ^ s •
              TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (M.tr bk.ι (e k)))) := by
            rw [hcj, smul_smul, smul_smul, mul_comm]
        _ = inclW l (bk.ev bk.E) ^ S.a • j m := congrArg _ hj
        _ = ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) • j m := congrArg (· • j m) e1.symm
        _ = ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) •
              j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) := hr7
        _ = inclW l (bk.ev bk.E) ^ s • ∑ i, bk.evW (S.A i k) • c i := by rw [e2, hsum2]
    have hev : ∀ x, bk.evW x = inclW l (bk.ev x) := fun _ => rfl
    refine Matrix.ext fun i k => ?_
    have h := congrArg (fun y => (b.baseChange (WCb l)).repr y i) (key k)

    simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
    repr_map_baseChange, LinearMap.toMatrix_id, Matrix.one_apply, smul_eq_mul, apply_ite (algebraMap ℤ_[l] (WCb l)),
    map_one, map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    AlgHom.toLinearMap_apply] at h
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul, hev, U,
      Module.Basis.toMatrix_apply]
    rw [h]
    exact Finset.sum_congr rfl fun x _ => by rw [hev, mul_comm]
  · intro g
    have keyg : ∀ k, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (c k) =
        ∑ i, inclW l (S.ε bk.ι ((ainfHom K g).comp bk.ι) i k) • c i := by
      intro k

      rw [hcj, ← H.j_act_of g (ainfHom K g) (fun _ => rfl), ← M.tr_comp, hF.tr bk.ι ((ainfHom K g).comp bk.ι) k,
      map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, ← hcj]
      rfl
    refine Matrix.ext fun i k => ?_
    have h := congrArg (fun y => (b.baseChange (WCb l)).repr y i) (keyg k)

    simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
    repr_map_baseChange, smul_eq_mul, AlgEquiv.toLinearMap_apply] at h
    simp only [Matrix.mul_apply, Matrix.map_apply, U, Module.Basis.toMatrix_apply, zW]
    rw [h]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  · rw [← hcj, hck]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedMatricesOfEtaleRealisationStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_framedMatrices_of_etaleRealisation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K M (ainfObj K) (ainfId K) T ρ j → ∃ (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U ∧ ∀ k, j (M.tr bk.ι (e k)) = ∑ i, U i k ⊗ₜ[ℤ_[l]] b i := by
  apply _root_.GlobalTheory.BSP.exists_mReal_of_realises <;> assumption
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfEquivariantEtaleMapAinf

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semilinear_square_of_basis {A B N N' Q Q' ι : Type} [CommRing A] [CommRing B] [AddCommGroup N]
    [Module A N] [AddCommGroup N'] [Module A N'] [AddCommGroup Q] [Module B Q] [AddCommGroup Q'] [Module B Q']
    {c : A →+* B} (β : Module.Basis ι A N) (w : N →ₗ[A] N') (j : N →ₛₗ[c] Q) (j' : N' →ₛₗ[c] Q')
    (G : Q →ₗ[B] Q') (h : ∀ k, j' (w (β k)) = G (j (β k))) (x : N) : j' (w x) = G (j x) :=
  LinearMap.congr_fun (β.ext (f₁ := j'.comp w) (f₂ := G.comp j) h) x

theorem sum_smul_column_eq {R B T T' : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup T]
    [Module R T] [AddCommGroup T'] [Module R T'] {d d' : ℕ} (b : Module.Basis (Fin d) R T)
    (b' : Module.Basis (Fin d') R T') (f : T →ₗ[R] T') (U : Matrix (Fin d) (Fin d) B)
    (U' : Matrix (Fin d') (Fin d') B) (Y : Matrix (Fin d') (Fin d) B)
    (h : U' * Y = (LinearMap.toMatrix b b' f).map (algebraMap R B) * U) (k : Fin d) :
    ∑ i, Y i k • ∑ m, U' m i ⊗ₜ[R] b' m = f.baseChange B (∑ i, U i k ⊗ₜ[R] b i) := by
  have h1 : ∀ i, f (b i) = ∑ m, LinearMap.toMatrix b b' f m i • b' m := fun i => by
    conv_lhs => rw [← b'.sum_repr (f (b i))]
    simp only [LinearMap.toMatrix_apply]
  have h2 : ∀ m, ∑ i, Y i k * U' m i = ∑ i, LinearMap.toMatrix b b' f m i • U i k := fun m => by
    have := congrFun (congrFun h m) k
    simp only [Matrix.mul_apply, Matrix.map_apply] at this
    simp only [Algebra.smul_def, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

  simp only [map_sum, LinearMap.baseChange_tmul, h1, TensorProduct.tmul_sum, Finset.smul_sum,
  TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.tmul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← TensorProduct.sum_tmul, ← TensorProduct.sum_tmul, h2]

theorem square_column {S A B P P' N N' Q Q' κ : Type} [CommRing S] [CommRing A] [CommRing B] [AddCommGroup P]
    [Module S P] [AddCommGroup P'] [Module S P'] [AddCommGroup N]
    [Module A N] [AddCommGroup N'] [Module A N'] [AddCommGroup Q] [Module B Q] [AddCommGroup Q'] [Module B Q']
    [Fintype κ] {a : S →+* A} {c : A →+* B} (t : P →ₛₗ[a] N) (t' : P' →ₛₗ[a] N') (v : P →ₗ[S] P')
    (w : N →ₗ[A] N') (j : N →ₛₗ[c] Q) (j' : N' →ₛₗ[c] Q') (G : Q →ₗ[B] Q') (hw : ∀ x, w (t x) = t' (v x))
    {n : N} {p : P} {y : κ → S} {e : κ → P'} {q : Q} {q' : κ → Q'} (hn : n = t p) (hp : v p = ∑ i, y i • e i)
    (hq : j (t p) = q) (hq' : ∀ i, j' (t' (e i)) = q' i) (h : ∑ i, c (a (y i)) • q' i = G q) :
    j' (w n) = G (j n) := by

  rw [hn, hw, hp, hq, ← h, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [t'.map_smulₛₗ, j'.map_smulₛₗ, hq']

theorem exists_fHom_of_equivariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T'] (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)) (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')), Realises K M (ainfObj K) (ainfId K) T ρ j → Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ f : T →ₗ[ℤ_[l]] T', (∀ g x, f (ρ g x) = ρ' g (f x)) → ∃ u : FHom M M', ∀ x, j' (u.u (ainfObj K) x) = f.lTensor (WCb l) (j x) := by
  intro l _ K T _ _ ρ T' _ _ ρ' M M' j j' H H' f hf
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  obtain ⟨d, S, e, hS⟩ := GlobalTheory.T.exists_framedStratifiedCrystalBasis l K bk M
  obtain ⟨d', S', e', hS'⟩ := GlobalTheory.T.exists_framedStratifiedCrystalBasis l K bk M'
  obtain ⟨b, U, hU, hj⟩ := GlobalTheory.T.exists_framedMatrices_of_etaleRealisation l K bk d S M e hS T ρ j H
  obtain ⟨b', U', hU', hj'⟩ := GlobalTheory.T.exists_framedMatrices_of_etaleRealisation l K bk d' S' M' e' hS' T' ρ' j' H'
  have hF : ∀ g, LinearMap.toMatrix b b' f * LinearMap.toMatrix b b (ρ g) =
      LinearMap.toMatrix b' b' (ρ' g) * LinearMap.toMatrix b b' f := fun g => by
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    exact LinearMap.ext (hf g)
  obtain ⟨Y, hY⟩ := GlobalTheory.T.equivariant_latticeMatrix_over_breuilKisin l K bk d d' S S' _ _ U U' hU hU' _ hF
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_fCrystalHom_of_stratifiedPhiModuleHom l K bk d d' S S' M M' e e' hS hS' Y
    (GlobalTheory.T.isStratifiedPhiModuleHom_of_galois_equivariant l K bk d d' S S' _ _ U U' hU hU' _ hF Y hY)
  obtain ⟨β, hβ⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) _ e
  refine ⟨u, fun x => ?_⟩
  refine semilinear_square_of_basis β (u.u (ainfObj K)) j j' (f.baseChange (WCb l)) (fun k => ?_) x
  refine square_column (M.tr bk.ι) (M'.tr bk.ι) (u.u bk.prism) (u.u (ainfObj K)) j j' (f.baseChange (WCb l))
    (u.u_tr bk.ι) (hβ k) (hu k) (hj k) hj' ?_
  exact sum_smul_column_eq b b' f U U' _ hY k

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfEquivariantEtaleMapAinfStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_FCrystalHom_of_equivariantEtaleMap_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T'] (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)) (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')), Realises K M (ainfObj K) (ainfId K) T ρ j → Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ f : T →ₗ[ℤ_[l]] T', (∀ g x, f (ρ g x) = ρ' g (f x)) → ∃ u : FHom M M', ∀ x, j' (u.u (ainfObj K) x) = f.lTensor (WCb l) (j x) := by
  first | exact @GlobalTheory.BSP.exists_fHom_of_equivariant | exact GlobalTheory.BSP.exists_fHom_of_equivariant | (intros; apply GlobalTheory.BSP.exists_fHom_of_equivariant <;> assumption)
end
end
