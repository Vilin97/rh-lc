module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentConstPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocommOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAppEqBialgHomKernelIdealOfIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerIdealFinrankEqPowOfIdempotent
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeBaseChangeOfIdem

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup.IdemSplit

theorem finrank_range_baseChange_of_idem {R S M : Type} [CommRing R] [CommRing S] [Algebra R S]
    [StrongRankCondition R] [StrongRankCondition S] [AddCommGroup M] [Module R M]
    (e : M →ₗ[R] M) (he : e ∘ₗ e = e) [Module.Free R (LinearMap.range e)] :
    Module.finrank S (LinearMap.range (e.baseChange S)) =
      Module.finrank R (LinearMap.range e) := by
  let r : M →ₗ[R] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[R] M := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  have hir : e = i ∘ₗ r := LinearMap.ext fun _ => rfl
  have hS : r.baseChange S ∘ₗ i.baseChange S = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id]
  have hsurj : Function.Surjective (r.baseChange S) := fun x =>
    ⟨i.baseChange S x, LinearMap.congr_fun hS x⟩
  have hinj : Function.Injective (i.baseChange S) := fun x y hxy => by
    have := congrArg (r.baseChange S) hxy
    rwa [← LinearMap.comp_apply, hS, ← LinearMap.comp_apply, hS] at this
  have h2 : e.baseChange S = i.baseChange S ∘ₗ r.baseChange S := by
    rw [← LinearMap.baseChange_comp, ← hir]
  rw [h2, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hsurj),
    LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

def quotEquivRange {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (f : A →ₐ[R] A)
    (I : Ideal A) (h : RingHom.ker f = I) : (A ⧸ I) ≃ₗ[R] LinearMap.range f.toLinearMap :=
  (Submodule.Quotient.restrictScalarsEquiv R I).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by ext x; simp [← h]) ≪≫ₗ
    LinearMap.quotKerEquivRange f.toLinearMap

end GlobalTheory.PDivGroup.IdemSplit

namespace GlobalTheory.PDivGroup.IdemSplit

open GlobalTheory.PDivGroup.KerGrp

theorem exists_of_family {p : ℕ} {k : Type} [CommRing k] (G : PDivGroup p k)
    (v : G ⟶ G) (h₀ : ℕ) (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, HopfAlgebra k (B n)]
    [∀ n, Module.Projective k (B n)]
    (π : ∀ n, G.A n →ₐc[k] B n) (hπ : ∀ n, Function.Surjective (π n))
    (hk : ∀ n, RingHom.ker (π n) = kerIdeal (v.app n))
    (h : ∀ (n : ℕ) (q : PrimeSpectrum k), Module.rankAtStalk (B n) q = p ^ (n * h₀)) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = kerIdeal (v.app n) := by
  haveI : ∀ n, IsCocomm k (B n) := fun n => isCocomm_of_surjective (π n) (hπ n)
  have hle : ∀ n, RingHom.ker (π (n + 1)) ≤ RingHom.ker ((π n).comp (G.res n)) := fun n a ha => by
    have : G.res n a ∈ RingHom.ker (π n) := by
      rw [hk, ← map_res_kerIdeal]
      rw [hk] at ha
      exact Ideal.mem_map_of_mem (G.res n : G.A (n + 1) →ₐ[k] G.A n) ha
    exact this
  let r := fun n => liftSurj (π (n + 1)) (hπ (n + 1)) ((π n).comp (G.res n)) (hle n)
  have hr : ∀ n a, r n (π (n + 1) a) = π n (G.res n a) := fun n a => liftSurj_apply ..
  let K : PDivGroup p k :=
    { height := h₀
      A := B
      finite := fun n => Module.Finite.of_surjective (π n : G.A n →ₗ[k] B n) (hπ n)
      rank_eq := h
      res := r
      res_surjective := fun n b => by
        obtain ⟨c, rfl⟩ := hπ n b
        obtain ⟨a, rfl⟩ := G.res_surjective n c
        exact ⟨_, hr n a⟩
      ker_res := fun n => by
        rw [← map_torsionIdeal (hπ (n + 1)), ← G.ker_res]
        refine le_antisymm (fun b hb => ?_) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
        · obtain ⟨a, rfl⟩ := hπ _ b
          have h1 : G.res n a ∈ RingHom.ker (π n) := (hr n a).symm.trans hb
          rw [hk, ← map_res_kerIdeal] at h1
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (G.res n : G.A (n + 1) →ₐ[k] G.A n) (G.res_surjective n)).1 h1
          rw [← hk] at hc
          have hc' : π (n + 1) c = 0 := hc
          have e' : G.res n c = G.res n a := e
          have h2 : a - c ∈ RingHom.ker (G.res n) := by
            rw [RingHom.mem_ker, map_sub, e', sub_self]
          have h3 : π (n + 1) a = π (n + 1) (a - c) := by rw [map_sub, hc', sub_zero]
          rw [h3]
          exact Ideal.mem_map_of_mem (π (n + 1) : G.A (n + 1) →ₐ[k] B (n + 1)) h2
        · have ha' : G.res n a = 0 := ha
          change r n (π (n + 1) a) = 0
          rw [hr, ha', map_zero] }
  exact ⟨K, ⟨π, fun n => BialgHom.ext fun a => hr n a⟩, fun n => ⟨hπ n, hk n⟩⟩

end GlobalTheory.PDivGroup.IdemSplit

namespace GlobalTheory.PDivGroup.IdemSplit

theorem baseChangeMap_zero {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (O' : Type) [CommRing O']
    [Algebra O O'] (G H : PDivGroup p O) : baseChangeMap O' (0 : G ⟶ H) = 0 := by
  have h := baseChangeMap_add O' (0 : G ⟶ H) 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

theorem bcMap_toLinearMap {O : Type} [CommRing O] (O' : Type) [CommRing O'] [Algebra O O']
    {A : Type} [CommRing A] [Bialgebra O A] (f : A →ₐc[O] A) :
    ((bcMap O' f : O' ⊗[O] A →ₐ[O'] O' ⊗[O] A)).toLinearMap =
      ((f : A →ₐ[O] A).toLinearMap).baseChange O' := by
  refine LinearMap.ext fun x => ?_
  induction x with
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul r a => exact bcMap_tmul f r a

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]

theorem idempotent_split_of_isLocalRing (G : PDivGroup p O) (u : G ⟶ G) (hu : u ≫ u = u) :
    ∃ (H : PDivGroup p O) (i : H ⟶ G) (q : G ⟶ H), i ≫ q = 𝟙 H ∧ q ≫ i = u := by
  set v : G ⟶ G := 𝟙 G - u with hv
  have huv : u + v = 𝟙 G := add_sub_cancel u (𝟙 G)
  have h1 : u ≫ v = 0 := by rw [hv, Preadditive.comp_sub, hu, Category.comp_id, sub_self]
  have h2 : v ≫ u = 0 := by rw [hv, Preadditive.sub_comp, hu, Category.id_comp, sub_self]
  have hker : ∀ n, RingHom.ker (u.app n) = kerIdeal (v.app n) :=
    ker_app_eq_kerIdeal_of_idempotents p O G u v huv h1 h2

  let k := IsLocalRing.ResidueField O
  let uk := baseChangeMap k u
  let vk := baseChangeMap k v
  have hF : ∀ {X Y Z : PDivGroup p O} (f : X ⟶ Y) (g : Y ⟶ Z),
      baseChangeMap k (f ≫ g) = baseChangeMap k f ≫ baseChangeMap k g := fun f g =>
    (baseChangeFunctor p O k).map_comp f g
  have hI : baseChangeMap k (𝟙 G) = 𝟙 (G.baseChange k) := (baseChangeFunctor p O k).map_id G
  have hvuk : vk + uk = 𝟙 _ := by rw [← baseChangeMap_add, add_comm, huv, hI]
  have huvk : uk + vk = 𝟙 _ := by rw [add_comm]; exact hvuk
  have h1k : uk ≫ vk = 0 := by rw [← hF, h1, baseChangeMap_zero]
  have h2k : vk ≫ uk = 0 := by rw [← hF, h2, baseChangeMap_zero]
  obtain ⟨h₀, hrk⟩ := kerIdeal_finrank_eq_pow_of_idempotent p k (G.baseChange k) vk uk
    hvuk h2k h1k
  have hkerk : ∀ n, RingHom.ker (uk.app n) = kerIdeal (vk.app n) :=
    ker_app_eq_kerIdeal_of_idempotents p k (G.baseChange k) uk vk huvk h1k h2k

  let e : ∀ n, G.A n →ₗ[O] G.A n := fun n => ((u.app n : G.A n →ₐ[O] G.A n)).toLinearMap
  have he : ∀ n, e n ∘ₗ e n = e n := fun n => LinearMap.ext fun a =>
    DFunLike.congr_fun (congrArg (fun w : G ⟶ G => w.app n) hu) a
  have hproj : ∀ n, Module.Projective O (LinearMap.range (e n)) := fun n =>
    Module.Projective.of_split (LinearMap.range (e n)).subtype (e n).rangeRestrict
      (LinearMap.ext fun x => Subtype.ext (by
        obtain ⟨y, hy⟩ := x.2
        change e n x.1 = x.1
        rw [← hy]
        exact LinearMap.congr_fun (he n) y))
  have hfin : ∀ n, Module.Finite O (LinearMap.range (e n)) := fun n =>
    Module.Finite.of_surjective (e n).rangeRestrict (LinearMap.surjective_rangeRestrict _)
  have hfree : ∀ n, Module.Free O (LinearMap.range (e n)) := fun n =>
    Module.free_of_flat_of_isLocalRing
  let B := fun n => G.A n ⧸ kerIdeal (v.app n)
  have hHopf : ∀ n, (kerIdeal (v.app n)).IsHopfIdeal O := fun n =>
    GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom O _ _ (v.app n)
  let eqv : ∀ n, B n ≃ₗ[O] LinearMap.range (e n) := fun n =>
    quotEquivRange (u.app n : G.A n →ₐ[O] G.A n) _ (hker n)
  have hBproj : ∀ n, Module.Projective O (B n) := fun n =>
    Module.Projective.of_equiv (eqv n).symm
  have hrank : ∀ n, Module.finrank O (B n) = p ^ (n * h₀) := fun n => by
    rw [(eqv n).finrank_eq, ← finrank_range_baseChange_of_idem (S := k) (e n) (he n),
      ← bcMap_toLinearMap, ← (quotEquivRange _ _ (hkerk n)).finrank_eq]
    exact hrk n
  have hBrank : ∀ (n : ℕ) (q : PrimeSpectrum O), Module.rankAtStalk (B n) q = p ^ (n * h₀) :=
    fun n q => by
      haveI := Module.Free.of_equiv (eqv n).symm
      rw [Module.rankAtStalk_eq_finrank_of_free, hrank]
      rfl
  obtain ⟨K, i, hi⟩ := exists_of_family G v h₀ B
    (fun _ => Bialgebra.Quotient.mkBialgHom _) (fun _ => Ideal.Quotient.mk_surjective)
    (fun _ => Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem) hBrank
  obtain ⟨hfac, hcan⟩ := factor_closedImmersion p O K G i (fun n => (hi n).1)
  obtain ⟨q, hq⟩ := hfac G u (fun n => by rw [(hi n).2, hker n])
  have hiv : i ≫ v = 0 := by
    refine Hom.ext (funext fun n => BialgHom.ext fun b => ?_)
    have h := (kerIdeal_le_ker_iff (v.app n) (i.app n : G.A n →ₐ[O] K.A n)).1 (hi n).2.ge b
    change i.app n (v.app n b) = (1 : WithConv (G.A n →ₐc[O] K.A n)).ofConv b
    refine Eq.trans h ?_
    simp
  have hiu : i ≫ u = i := by
    have e := Preadditive.comp_add _ _ _ i u v
    rw [huv, hiv, add_zero, Category.comp_id] at e
    exact e.symm
  refine ⟨K, i, q, ?_, hq⟩
  apply hcan K
  rw [Category.assoc, hq, hiu, Category.id_comp]

end GlobalTheory.PDivGroup.IdemSplit

theorem GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
      [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
      ∀ (G : PDivGroup p O) (u : G ⟶ G), u ≫ u = u →
        ∃ (H : PDivGroup p O) (i : H ⟶ G) (q : G ⟶ H), i ≫ q = 𝟙 H ∧ q ≫ i = u :=
  fun p _ _ _ _ _ _ O _ _ _ _ _ _ _ G u hu =>
    GlobalTheory.PDivGroup.IdemSplit.idempotent_split_of_isLocalRing p O G u hu
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfSubsingletonPoints

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ConnConstSplit

open IsLocalRing

theorem isLocalRing_of_subsingleton_points (O : Type) [CommRing O] [IsLocalRing O]
    [IsAlgClosed (ResidueField O)] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A]
    [Subsingleton (A →ₐ[O] ResidueField O)] (c₀ : A →ₐ[O] ResidueField O) : IsLocalRing A := by
  have key : ∀ M : Ideal A, M.IsMaximal → M = RingHom.ker c₀ := by
    intro M hM
    have hu : (M.under O).IsMaximal := Ideal.IsMaximal.under O M
    have hum : M.under O = maximalIdeal O := IsLocalRing.eq_maximalIdeal hu
    letI : Field (A ⧸ M) := Ideal.Quotient.field M
    let g : O →+* A ⧸ M := (Ideal.Quotient.mk M).comp (algebraMap O A)
    haveI : IsLocalHom g := ⟨fun x hx => by
      by_contra h
      have hxm : x ∈ M.under O := by rw [hum]; exact h
      have h0 : g x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hxm
      exact hx.ne_zero h0⟩
    let f : ResidueField O →+* A ⧸ M := ResidueField.lift g
    letI : Algebra (ResidueField O) (A ⧸ M) := f.toAlgebra
    have hf : ∀ x : O, f (residue O x) = g x := fun x => rfl
    haveI : Algebra.IsIntegral (ResidueField O) (A ⧸ M) := ⟨fun y => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨P, hPm, hPa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
      refine ⟨P.map (residue O), hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have h1 : (algebraMap (ResidueField O) (A ⧸ M)).comp (residue O) = g := RingHom.ext hf
      rw [h1]
      have h2 := Polynomial.hom_eval₂ P (algebraMap O A) (Ideal.Quotient.mk M) a
      rw [hPa, map_zero] at h2
      exact h2.symm⟩
    have hsurj := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField O) (K := A ⧸ M)).2
    let e : ResidueField O ≃+* A ⧸ M := RingEquiv.ofBijective f ⟨f.injective, hsurj⟩
    let c : A →ₐ[O] ResidueField O :=
      { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk M)
        commutes' := fun x => by
          change e.symm (Ideal.Quotient.mk M (algebraMap O A x)) = algebraMap O (ResidueField O) x
          rw [RingEquiv.symm_apply_eq]
          exact (hf x).symm }
    have hc : c = c₀ := Subsingleton.elim _ _
    ext a
    rw [← hc, RingHom.mem_ker]
    change a ∈ M ↔ e.symm (Ideal.Quotient.mk M a) = 0
    rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  haveI : Nontrivial A := c₀.toRingHom.domain_nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  exact IsLocalRing.of_unique_max_ideal ⟨M, hM, fun M' hM' => (key M' hM').trans (key M hM).symm⟩

theorem comp_add_app {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {B : Type} [CommRing B]
    [Algebra O B] {G H : PDivGroup p O} (f g : G ⟶ H) (n : ℕ) (x : G.A n →ₐ[O] B) :
    x.comp ((f + g).app n : H.A n →ₐ[O] G.A n) = WithConv.ofConv
      (WithConv.toConv (x.comp (f.app n : H.A n →ₐ[O] G.A n)) *
        WithConv.toConv (x.comp (g.app n : H.A n →ₐ[O] G.A n))) :=
  congrArg WithConv.ofConv
    (map_mul ((GlobalTheory.PDiv.ptsPush (H.A n) x).comp GlobalTheory.PDiv.toPts) (f.conv n) (g.conv n))

theorem eq_one_of_mul_self_of_pow {M : Type*} [Monoid M] {y : M} (hy : y * y = y) {m : ℕ}
    (hm : 1 ≤ m) (h : y ^ m = 1) : y = 1 := by
  have hk : ∀ k : ℕ, y ^ (k + 1) = y := by
    intro k
    induction k with
    | zero => exact pow_one y
    | succ k ih => rw [pow_succ, ih, hy]
  rw [← h, ← Nat.sub_add_cancel hm, hk]

end GlobalTheory.ConnConstSplit

namespace GlobalTheory.ConnConstSplit

open IsLocalRing

theorem exists_isSum_conn_const : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, ∃ G₁ G₂ : PDivGroup p O, IsSum G G₁ G₂ ∧ PDivLat.IsConn G₁ ∧ IsConst G₂ := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G
  haveI := ValuationRing.of_integers v hv
  haveI := hv.isFractionRing
  haveI : IsAlgClosed (ResidueField O) :=
    GlobalTheory.isAlgClosed_residueField_of_valuationRing_of_isAlgClosed O C
  obtain ⟨u, huu, hfix, hrange⟩ := GlobalTheory.ConstPart.exists_idempotent_constPart p C v O hv G
  obtain ⟨G₂, i₂, q₂, h₂1, h₂2⟩ := GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers p C v O hv G u huu
  have h1u : (𝟙 G - u) ≫ (𝟙 G - u) = 𝟙 G - u := by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id, huu]
    abel
  obtain ⟨G₁, i₁, q₁, h₁1, h₁2⟩ := GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers p C v O hv G (𝟙 G - u) h1u
  have hl₁ : ∀ n (b : G₁.A n), i₁.app n (q₁.app n b) = b := fun n b => by
    have h := congrArg (fun f : G₁ ⟶ G₁ => f.app n b) h₁1
    simpa using h
  have hl₂ : ∀ n (b : G₂.A n), i₂.app n (q₂.app n b) = b := fun n b => by
    have h := congrArg (fun f : G₂ ⟶ G₂ => f.app n b) h₂1
    simpa using h
  have hu₂ : ∀ n (a : G.A n), u.app n a = q₂.app n (i₂.app n a) := fun n a => by
    rw [← h₂2]; rfl
  refine ⟨G₁, G₂, ⟨i₁, i₂, q₁, q₂, h₁1, h₂1, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have e1 : i₁ ≫ q₂ = i₁ ≫ ((q₁ ≫ i₁) ≫ (q₂ ≫ i₂)) ≫ q₂ := by
      simp only [Category.assoc]
      rw [h₂1, Category.comp_id, reassoc_of% h₁1]
    rw [e1, h₁2, h₂2, Preadditive.sub_comp, Category.id_comp, huu, sub_self,
      Limits.zero_comp, Limits.comp_zero]
  · have e1 : i₂ ≫ q₁ = i₂ ≫ ((q₂ ≫ i₂) ≫ (q₁ ≫ i₁)) ≫ q₁ := by
      simp only [Category.assoc]
      rw [h₁1, Category.comp_id, reassoc_of% h₂1]
    rw [e1, h₁2, h₂2, Preadditive.comp_sub, Category.comp_id, huu, sub_self,
      Limits.zero_comp, Limits.comp_zero]
  · rw [h₁2, h₂2, sub_add_cancel]
  · intro n
    let c₀ : G₁.A n →ₐ[O] ResidueField O :=
      (Algebra.ofId O (ResidueField O)).comp (Bialgebra.counitAlgHom O (G₁.A n))
    have hall : ∀ c : G₁.A n →ₐ[O] ResidueField O, c = c₀ := by
      intro c
      set x : G.A n →ₐ[O] ResidueField O := c.comp (i₁.app n : G.A n →ₐ[O] G₁.A n) with hxdef
      have hx1 : x.comp (u.app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext (hfix n x)
      have hx2 : x.comp ((q₁ ≫ i₁).app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext fun a => by
        change c (i₁.app n (q₁.app n (i₁.app n a))) = c (i₁.app n a)
        rw [hl₁]
      have hsum : q₁ ≫ i₁ + u = 𝟙 G := by rw [h₁2, sub_add_cancel]
      have hid : x.comp ((𝟙 G : G ⟶ G).app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext fun a => rfl
      have hmul := comp_add_app (q₁ ≫ i₁) u n x
      rw [hsum, hid, hx2, hx1] at hmul
      have hyy : WithConv.toConv x * WithConv.toConv x = WithConv.toConv x := by
        exact (congrArg WithConv.toConv hmul).symm
      have hx : WithConv.toConv x = 1 :=
        eq_one_of_mul_self_of_pow hyy (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
          (G.pts_pow_self n (WithConv.toConv x))
      ext b
      have hb : c b = x (q₁.app n b) := by
        change c b = c (i₁.app n (q₁.app n b)); rw [hl₁]
      rw [hb]
      have hx' : x = WithConv.ofConv (1 : WithConv (G.A n →ₐ[O] ResidueField O)) := by
        rw [← hx]
      rw [hx', AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply]
      rfl
    haveI : Subsingleton (G₁.A n →ₐ[O] ResidueField O) :=
      ⟨fun a b => (hall a).trans (hall b).symm⟩
    exact isLocalRing_of_subsingleton_points O (G₁.A n) c₀
  · intro n
    obtain ⟨N, ⟨e⟩⟩ := hrange n
    have hinj : Function.Injective (q₂.app n : G₂.A n →ₐ[O] G.A n) := fun a b h => by
      rw [← hl₂ n a, ← hl₂ n b]
      exact congrArg (i₂.app n) h
    have hrng : (u.app n : G.A n →ₐ[O] G.A n).range = (q₂.app n : G₂.A n →ₐ[O] G.A n).range := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨i₂.app n a, (hu₂ n a).symm⟩
      · rintro ⟨b, rfl⟩
        refine ⟨q₂.app n b, ?_⟩
        change u.app n (q₂.app n b) = q₂.app n b
        rw [hu₂, hl₂]
    let e' : G₂.A n ≃ₐ[O] (Fin N → O) :=
      (AlgEquiv.ofInjective _ hinj).trans ((Subalgebra.equivOfEq _ _ hrng.symm).trans e)
    have hN : N = p ^ (n * G₂.height) := by
      have h1 := G₂.rank_eq n ⟨maximalIdeal O, inferInstance⟩
      rw [Module.rankAtStalk_eq_of_equiv e'.toLinearEquiv, Module.rankAtStalk_eq_finrank_of_free,
        Module.finrank_fin_fun] at h1
      simpa using h1
    exact ⟨hN ▸ e'⟩

end GlobalTheory.ConnConstSplit
end
end
