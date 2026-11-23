module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisorStatement
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasisStatement
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixFCrystalBreuilKisin

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.FrobMat

theorem isFrac_add {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k : ℕ} (h : IsFrac d y m k) (c : ℕ) :
    IsFrac d y (d ^ c • m) (k + c) := by
  unfold IsFrac at *
  rw [h, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, smul_smul, pow_add, mul_comm]

theorem isFrac_le {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k a : ℕ} (h : IsFrac d y m k) (hka : k ≤ a) :
    IsFrac d y (d ^ (a - k) • m) a := by
  have := isFrac_add h (a - k)
  rwa [Nat.add_sub_cancel' hka] at this

theorem isFrac_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k : ℕ} (h : IsFrac d y m k) :
    d ^ k • y = LocalizedModule.mk m 1 := by
  unfold IsFrac at h
  rw [h, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, OneMemClass.coe_one]

theorem exists_common_den {R : Type} [CommRing R] (x : R) {ι : Type} [Finite ι]
    (f : ι → Localization.Away x) : ∃ (n : ℕ) (g : ι → R), ∀ i, algebraMap R _ (g i) = x ^ n • f i := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers x) f
  choose g hg using hn
  exact ⟨n, g, hg⟩

theorem span_eq_top_of_semiBC {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) {ι : Type} [Fintype ι]
    (e : Module.Basis ι A M) : Submodule.span B (Set.range fun i => u (e i)) = ⊤ := by
  let S := Submodule.span B (Set.range fun i => u (e i))
  have hu : ∀ x, u x ∈ S := by
    intro x

    rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [u.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨w, -, huniq⟩ := h (N ⧸ S) 0
  have h1 : S.mkQ = w := huniq _ fun x => by
    simp only [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]; exact hu x
  have h2 : (0 : N →ₗ[B] N ⧸ S) = w := huniq _ fun x => by simp
  rw [eq_top_iff]
  intro y _
  have := LinearMap.congr_fun (h1.trans h2.symm) y
  simpa using this

end GlobalTheory.BSP.FrobMat

namespace GlobalTheory.BSP.FrobMat

theorem frob_matrix_general {R Mo : Type} [CommRing R] [IsDomain R] [AddCommGroup Mo] [Module R Mo]
    (φ : R →+* R) (x : R) (hx : x ≠ 0)
    (u : Mo →ₛₗ[(algebraMap R (Localization.Away x)).comp φ] LocalizedModule (Submonoid.powers x) Mo)
    (hu : SemiBC u) {d : ℕ} (e : Module.Basis (Fin d) R Mo) :
    ∃ (a b : ℕ) (A A' : Matrix (Fin d) (Fin d) R), A * A' = x ^ b • (1 : Matrix (Fin d) (Fin d) R) ∧
      ∀ j, IsFrac x (u (e j)) (∑ i, A i j • e i) a := by
  haveI : Module.Free R Mo := Module.Free.of_basis e
  have h1 : ∀ j, ∃ m k, IsFrac x (u (e j)) m k := fun j => exists_isFrac _ _
  choose m k hmk using h1
  let a := ∑ j, k j
  have hk : ∀ j, k j ≤ a := fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let m' : Fin d → Mo := fun j => x ^ (a - k j) • m j
  have hm' : ∀ j, IsFrac x (u (e j)) (m' j) a := fun j => isFrac_le (hmk j) (hk j)
  let A : Matrix (Fin d) (Fin d) R := fun i j => e.repr (m' j) i
  have hA : ∀ j, ∑ i, A i j • e i = m' j := fun j => e.sum_repr (m' j)
  have hsp := span_eq_top_of_semiBC hu e
  have h2 : ∀ k' : Fin d, ∃ c : Fin d → Localization.Away x,
      ∑ j, c j • u (e j) = LocalizedModule.mk (e k') 1 := fun k' =>
    (Submodule.mem_span_range_iff_exists_fun _).1 (Submodule.eq_top_iff'.1 hsp _)
  choose c hc using h2
  obtain ⟨n, A', hA'⟩ := exists_common_den x (fun p : Fin d × Fin d => c p.2 p.1)
  let A'' : Matrix (Fin d) (Fin d) R := fun j k' => A' (j, k')
  refine ⟨a, a + n, A, A'', ?_, fun j => (hA j).symm ▸ hm' j⟩
  have key : ∀ k', LocalizedModule.mk (x ^ (a + n) • e k') (1 : Submonoid.powers x) =
      LocalizedModule.mk (∑ j, A' (j, k') • m' j) 1 := by
    intro k'
    have hr : LocalizedModule.mk (∑ j, A' (j, k') • m' j) (1 : Submonoid.powers x) =
        ∑ j, A' (j, k') • LocalizedModule.mk (m' j) (1 : Submonoid.powers x) := by

      rw [← LocalizedModule.mkLinearMap_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LocalizedModule.mkLinearMap_apply]
    rw [hr, ← LocalizedModule.smul'_mk, ← hc k', pow_add, mul_smul, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_assoc (x ^ n) (c k' j), ← hA' (j, k'), algebraMap_smul, smul_comm,
      isFrac_smul (hm' j)]
  have key2 : ∀ k', x ^ (a + n) • e k' = ∑ j, A' (j, k') • m' j := by
    intro k'
    obtain ⟨⟨_, r, rfl⟩, hr⟩ := LocalizedModule.mk_eq.1 (key k')
    simp only [Submonoid.smul_def, one_smul] at hr
    exact smul_right_injective _ (pow_ne_zero r hx) hr
  ext i k'
  have h3 := congrArg (fun y => e.repr y i) (key2 k')

  simp only [map_smul, e.repr_self, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum,
  Finset.sum_apply, Finsupp.single_apply, smul_eq_mul] at h3
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [eq_comm] at h3
  simp only [eq_comm (a := k') (b := i)] at h3
  rw [← h3]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.BSP.FrobMat

theorem GlobalTheory.BSP.frob_matrix_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), ∃ (a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) ∧ ∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a := by
  intro l _ K bk d M e
  haveI : IsDomain bk.prism.A := inferInstanceAs (IsDomain bk.S)
  exact GlobalTheory.BSP.FrobMat.frob_matrix_general (R := bk.prism.A) bk.prism.D.φ (bk.toP bk.E) bk.E_ne_zero
    (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩)
    (M.Φ_bc bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩) e
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixFCrystalBreuilKisinStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_frobenius_matrix_fCrystal_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), ∃ (a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) ∧ ∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a := by
  first | exact @GlobalTheory.BSP.frob_matrix_bk | exact GlobalTheory.BSP.frob_matrix_bk | (intros; apply GlobalTheory.BSP.frob_matrix_bk <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedStratifiedCrystalBasis

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem frame_coord_cancel {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ}
    (b : Module.Basis (Fin d) B N) {t p q : B} (ht : t ∈ nonZeroDivisors B) {m : N} {k r s : ℕ}
    {v w : Fin d → B} (h1 : t ^ r • (p • m - t ^ k • ∑ i, v i • b i) = 0)
    (h2 : t ^ s • (q • m - t ^ k • ∑ i, w i • b i) = 0) (i : Fin d) : p * w i = q * v i := by
  have e1 := congrArg (fun x => b.equivFun x i) h1
  have e2 := congrArg (fun x => b.equivFun x i) h2
  simp only [← b.equivFun_symm_apply, map_smul, map_sub, LinearEquiv.apply_symm_apply, map_zero,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at e1 e2
  have f1 := (mem_nonZeroDivisors_iff.1 (pow_mem ht r)).1 _ e1
  have f2 := (mem_nonZeroDivisors_iff.1 (pow_mem ht s)).1 _ e2
  rw [← sub_eq_zero]
  apply (mem_nonZeroDivisors_iff.1 (pow_mem ht k)).1
  linear_combination q * f1 - p * f2

theorem frame_sum_single {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ} (v : Fin d → N)
    (j : Fin d) : ∑ i, (Pi.single j 1 : Fin d → B) i • v i = v j := by
  simp [Pi.single_apply]

theorem frame_sum_mulVec {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ} (φ : B →+* B)
    (A ε : Matrix (Fin d) (Fin d) B) (v c : Fin d → N) (h : ∀ x, v x = ∑ i, ε i x • c i) (j : Fin d) :
    ∑ i, A.mulVec (fun x => φ ((Pi.single j 1 : Fin d → B) x)) i • v i = ∑ i, (ε * A) i j • c i := by
  have h2 : (fun x => φ ((Pi.single j 1 : Fin d → B) x)) = Pi.single j 1 := by
    ext x
    by_cases hx : x = j <;> simp [hx]
  simp only [h2, Matrix.mulVec_single_one, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h x, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul, mul_comm]
  rfl

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

theorem frame_matrix_φ (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ)
    (A : Matrix (Fin d) (Fin d) bk.S)
    (hΦ : ∀ j : Fin d, IsFrac (bk.toP bk.E)
      (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a)
    {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (c : Module.Basis (Fin d) B.A (M.M B))
    (hc : ∀ i, c i = M.tr f (e i)) (ε : Matrix (Fin d) (Fin d) B.A)
    (htr : ∀ j, M.tr g (e j) = ∑ i, ε i j • M.tr f (e i)) :
    BK.hf g bk.E ^ a • (A.map (BK.hf f) * ε.map B.D.φ) = BK.hf f bk.E ^ a • (ε * A.map (BK.hf g)) := by
  obtain ⟨hI, ht⟩ := GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk B f
  let t : ↥B.I := ⟨BK.hf f bk.E, hI.ge (Ideal.mem_span_singleton_self _)⟩
  ext i j
  obtain ⟨m, k, hm⟩ := exists_isFrac (t : B.A) (M.Φ B t (M.tr g (e j)))
  obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e a A hΦ B g t (Pi.single j 1) m k
    (Eq.subst (motive := fun z => IsFrac (t : B.A) (M.Φ B t z) m k)
      (frame_sum_single (fun i => M.tr g (e i)) j).symm hm)
  obtain ⟨s, hs⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e a A hΦ B f t (fun i => ε i j) m k
    (Eq.subst (motive := fun z => IsFrac (t : B.A) (M.Φ B t z) m k) (htr j) hm)
  have h1 := frame_sum_mulVec B.D.φ (A.map (BK.hf g)) ε (fun i => M.tr g (e i)) c
    (fun x => (htr x).trans (Finset.sum_congr rfl fun i _ => congrArg (fun z => ε i x • z) (hc i).symm)) j
  rw [h1] at hr
  simp only [← hc] at hs
  exact frame_coord_cancel c ht hr hs i

theorem exists_frame_matrices (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) :
    ∃ ε : ∀ {B : Obj l ↥(OL K)}, Hom bk.prism B → Hom bk.prism B → Matrix (Fin d) (Fin d) B.A,
      (∀ {B} (f g : Hom bk.prism B) (j : Fin d), M.tr g (e j) = ∑ i, ε f g i j • M.tr f (e i)) ∧
      (∀ {B} (f : Hom bk.prism B), ε f f = 1) ∧
      (∀ {B} (f g h : Hom bk.prism B), ε f g * ε g h = ε f h) ∧
      (∀ {B B'} (k : Hom B B') (f g : Hom bk.prism B), (ε f g).map k.f = ε (k.comp f) (k.comp g)) := by
  have hb : ∀ {B : Obj l ↥(OL K)} (f : Hom bk.prism B), ∃ c : Module.Basis (Fin d) B.A (M.M B),
      ∀ i, c i = M.tr f (e i) := fun f => GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ _ (M.tr_bc f) _ e
  choose c hc using @hb
  have htr : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (j : Fin d),
      M.tr g (e j) = ∑ i, (c f).toMatrix (c g) i j • M.tr f (e i) := fun f g j => by
    rw [← hc, ← (c f).sum_toMatrix_smul_self (c g) j]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]
  have huniq : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (j : Fin d) (v : Fin d → B.A),
      M.tr g (e j) = ∑ i, v i • M.tr f (e i) → ∀ i, (c f).toMatrix (c g) i j = v i := fun f g j v h i => by
    change (c f).repr (c g j) i = v i
    rw [hc, h]
    simp only [← hc]
    rw [← (c f).equivFun_symm_apply, ← (c f).equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨fun f g => (c f).toMatrix (c g), htr, fun f => (c f).toMatrix_self,
    fun f g h => (c f).toMatrix_mul_toMatrix (c g) (c h), fun k f g => ?_⟩
  ext i j
  refine (huniq (k.comp f) (k.comp g) j (fun i => k.f ((c f).toMatrix (c g) i j)) ?_ i).symm
  refine (M.tr_comp k g (e j)).trans ((congrArg (M.tr k) (htr f g j)).trans ?_)
  refine (map_sum (M.tr k) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  exact ((M.tr k).map_smulₛₗ _ _).trans
    (congrArg (fun z => k.f ((c f).toMatrix (c g) i j) • z) (M.tr_comp k f (e i)).symm)

theorem exists_framed (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M : FCrys l ↥(OL K)) :
    ∃ (d : ℕ) (S : Strat bk d) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  have : IsLocalRing bk.prism.A := inferInstanceAs (IsLocalRing (Wq l bk.a)⟦X⟧)
  have := M.fin bk.prism
  have := M.proj bk.prism
  have : Module.Free bk.prism.A (M.M bk.prism) := Module.free_of_flat_of_isLocalRing
  obtain ⟨d, ⟨e⟩⟩ : ∃ d, Nonempty (Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) :=
    ⟨_, ⟨Module.finBasis bk.prism.A (M.M bk.prism)⟩⟩
  obtain ⟨a, b, A, A', hA, hΦ⟩ := GlobalTheory.T.exists_frobenius_matrix_fCrystal_breuilKisin l K bk d M e
  obtain ⟨ε, htr, h1, h2, h3⟩ := exists_frame_matrices M e
  refine ⟨d, ⟨a, b, A, A', hA, ε, h1, h2, h3, fun f g => ?_⟩, e, htr, hΦ⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ _ (M.tr_bc f) _ e
  exact frame_matrix_φ M e a A hΦ f g c hc (ε f g) (htr f g)

end GlobalTheory.BSP
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedStratifiedCrystalBasisStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_framedStratifiedCrystalBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M : FCrys l ↥(OL K)), ∃ (d : ℕ) (S : Strat bk d) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  first | exact @GlobalTheory.BSP.exists_framed | exact GlobalTheory.BSP.exists_framed | (intros; apply GlobalTheory.BSP.exists_framed <;> assumption)
end
end
